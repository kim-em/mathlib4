from pathlib import Path
import importlib.util, json, os, platform, re, subprocess, sys, time, hashlib
cwd=Path('.').resolve();tag=sys.argv[1];config=sys.argv[2] if len(sys.argv)>2 else 'lakefile-abel-normal.lean'
out=cwd/'.abel-evidence'/tag;out.mkdir(exist_ok=False)
spec=importlib.util.spec_from_file_location('cpu_lease','/home/kim/worktrees/hex-dev/hex-dev-sym-arith/scripts/bench/cpu_lease.py')
lease_mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(lease_mod)
cpu,lease=lease_mod.cpu_lease();os.sched_setaffinity(0,{cpu})
meta=dict(cpu=cpu,host=platform.node(),schedule=['AB','BA','AB','BA'],warmups=3,mode='Standard loading; no explicit native plugins',toolchain=(cwd/'lean-toolchain').read_text().strip(),lean_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd='/home/kim/worktrees/lean4/lean4-sym-module',text=True).strip(),mathlib_base='a3bcf0a3c2',timing='saved.restore and evalTactic; includes auxiliary theorem kernel checking inside both Abel implementations; excludes final declaration check',load_before=os.getloadavg(),source_sha256={})
for name in ['JacobiOldAbel.lean','AbelBenchCurrent.lean','AbelBench.lean',config]:
 p=Path(name);(out/p.name).write_bytes(p.read_bytes());meta['source_sha256'][name]=hashlib.sha256(p.read_bytes()).hexdigest()
(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
Path('.lake/build/lib/lean/AbelBench.trace').unlink(missing_ok=True)
start=time.monotonic();r=subprocess.run(['lake','-f',config,'--no-cache','build','AbelBench'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(out/'build.log').write_text(r.stdout)
rows=[dict(label=label,iterations=int(it),duration_ns=int(ns),heartbeats=int(hb),ns_per_call=int(ns)/int(it)) for label,it,ns,hb in re.findall(r'ABEL_BENCH (\S+) (\d+) (\d+) (\d+)',r.stdout)]
(out/'samples.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
meta.update(exit_code=r.returncode,sample_count=len(rows),load_after=os.getloadavg(),elapsed_s=time.monotonic()-start)
(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta,indent=2));print(r.stdout[-3000:])
if r.returncode: raise RuntimeError('build failed; all completed samples retained')
if len(rows)!=96: raise RuntimeError('missing samples; all outputs retained')
