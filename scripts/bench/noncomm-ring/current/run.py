from pathlib import Path
import hashlib,importlib.util,json,os,platform,re,subprocess,sys,time
cwd=Path('.').resolve();tag=sys.argv[1];mod=sys.argv[2];config=sys.argv[3] if len(sys.argv)>3 else 'lakefile-jacobi.lean'
out=cwd/'.jacobi-evidence'/tag;out.mkdir(exist_ok=False)
spec=importlib.util.spec_from_file_location('cpu_lease','/home/kim/worktrees/hex-dev/hex-dev-sym-arith/scripts/bench/cpu_lease.py')
lease_mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(lease_mod)
cpu,lease=lease_mod.cpu_lease();os.sched_setaffinity(0,{cpu})
meta=dict(cpu=cpu,host=platform.node(),schedule=['AB','BA','AB','BA'],warmups=3,reps=50,toolchain=(cwd/'lean-toolchain').read_text().strip(),lean_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd='/home/kim/worktrees/lean4/lean4-sym-module',text=True).strip(),baseline_commit='a3bcf0a3c2',mode=('Standard Mathlib loading; no explicit native plugins' if 'normal' in config else 'Explicit native .so loading for original Abel and old/current NoncommRing copies, harness, and shared import closure'),timing='evalTactic plus saved.restore; excludes final declaration kernel check, includes any kernel work performed inside tactic',host_context='Shared host. Root holds other Lake builds using these caches; other host activity unrestricted.',load_before=os.getloadavg(),source_sha256={},binary_sha256={})
for p in [Path('JacobiOldAbel.lean'),Path('JacobiOldNoncommRing.lean'),Path('JacobiCurrentNoncommRing.lean'),Path('JacobiHarness.lean'),Path(mod+'.lean'),Path(config)]:
 meta['source_sha256'][str(p)]=hashlib.sha256(p.read_bytes()).hexdigest();(out/p.name).write_bytes(p.read_bytes())
for p in list(Path('.lake/build/lib/lean').glob('mathlib_Jacobi*.so'))+[Path('.lake/build/lib/libJacobiMathlibDeps.so'),Path('/home/kim/worktrees/lean4/lean4-sym-module/build/release/stage1/lib/lean/libleanshared.so')]:
 if p.exists():meta['binary_sha256'][str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
Path('.lake/build/lib/lean/'+mod+'.trace').unlink(missing_ok=True)
start=time.monotonic();r=subprocess.run(['lake','-f',config,'--no-cache','build',mod],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(out/'build.log').write_text(r.stdout)
rows=[dict(pair=int(pair),arm=arm,iterations=int(it),duration_ns=int(ns),ns_per_call=int(ns)/int(it)) for pair,arm,it,ns in re.findall(r'JACOBI_BENCH (\d+) (\S+) (\d+) (\d+)',r.stdout)]
(out/'samples.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
meta.update(exit_code=r.returncode,sample_count=len(rows),load_after=os.getloadavg(),elapsed_s=time.monotonic()-start)
(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n');print(r.stdout[-6000:]);print(json.dumps(meta,indent=2))
if r.returncode or len(rows)!=8:raise RuntimeError('failed; logs and all completed samples retained')
