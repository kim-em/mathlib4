import Lake

open Lake DSL

/-!
## Mathlib dependencies on upstream projects
-/

require "leanprover-community" / "batteries" @ git "nightly-testing"
require "leanprover-community" / "Qq" @ git "master"

require "leanprover-community" / "aesop" @ git "nightly-testing"
require "leanprover-community" / "proofwidgets" @ git "nightly-testing"
  with NameMap.empty.insert `errorOnBuild
    "ProofWidgets failed to reuse pre-built JS code. \
    Please report this issue on the Lean Zulip."
require "leanprover-community" / "importGraph" @ git "main"
require "leanprover-community" / "LeanSearchClient" @ git "main"
require "leanprover-community" / "plausible" @ git "nightly-testing"


/-!
## Options for building mathlib
-/

/-- These options are used as `leanOptions`, prefixed by `` `weak``, so that
`lake build` uses them, as well as `Archive` and `Counterexamples`. -/
abbrev mathlibOnlyLinters : Array LeanOption := #[
  ⟨`linter.mathlibStandardSet, true⟩,
  -- Explicitly enable the header linter, since the standard set is defined in `Mathlib.Init`
  -- but we want to run this linter in files imported by `Mathlib.Init`.
  ⟨`linter.style.header, true⟩,
  ⟨`linter.checkInitImports, true⟩,
  ⟨`linter.allScriptsDocumented, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
  -- ⟨`linter.nightlyRegressionSet, true⟩,
  -- `latest_import.yml` uses this comment: if you edit it, make sure that the workflow still works
]

/-- These options are passed as `leanOptions` to building mathlib, as well as the
`Archive` and `Counterexamples`. -/
abbrev mathlibLeanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.unreachableTactic, false⟩, -- superseded by the unused tactic linter
  ] ++ -- options that are used in `lake build`
    mathlibOnlyLinters.map fun s ↦ { s with name := `weak ++ s.name }

/-- These options are passed as `leanOptions` when building `MathlibTest`. We don't use the typical
mathlib options in order to simulate the default downstream environment. -/
abbrev mathlibTestOptions : Array LeanOption := #[
    ⟨`pp.mvars.anonymous, false⟩ -- test stability: pretty-print `?m.37` as `?_`
  ]

package mathlib where
  testDriver := "MathlibTest"
  lintDriver := "batteries/runLinter"
  lintDriverArgs := #["Mathlib"]
  -- Run the builtin linting steps in addition to the `lintDriver` set above.
  builtinLint := true
  -- A version of Mathlib only supports the toolchain it is built with.
  fixedToolchain := true
  -- Mathlib oleans are built on Linux CI and used across platforms.
  platformIndependent := true
  -- Mathlib currently expects artifacts to be in the build directory.
  restoreAllArtifacts := true
  requiresModuleSystem := true
  -- These are additional settings which do not affect the lake hash,
  -- so they can be enabled in CI and disabled locally or vice versa.
  -- Warning: Do not put any options here that actually change the olean files,
  -- or inconsistent behavior may result
  -- weakLeanArgs := #[]

/-!
## Mathlib libraries
-/

@[default_target]
lean_lib Mathlib where
  libName := "JacobiMathlibDeps"
  roots := #[`Mathlib.Tactic.Linter.DirectoryDependency, `Mathlib.Tactic.Linter.Header, `Mathlib.Lean.Linter, `Mathlib.Tactic.AdaptationNote, `Mathlib.Tactic.Lemma, `Mathlib.Tactic.Linter.AuxLemma, `Mathlib.Tactic.Linter.DeprecatedSyntaxLinter, `Mathlib.Tactic.Linter.DocPrime, `Mathlib.Tactic.Linter.DocString, `Mathlib.Tactic.Linter.EmptyLine, `Mathlib.Tactic.Linter.GlobalAttributeIn, `Mathlib.Tactic.Linter.HashCommandLinter, `Mathlib.Tactic.Linter.HaveILetI, `Mathlib.Tactic.Linter.InternalConstructor, `Mathlib.Tactic.Linter.FlexibleLinter, `Mathlib.Tactic.Linter.Multigoal, `Mathlib.Tactic.Linter.OldObtain, `Mathlib.Lean.Expr.Basic, `Mathlib.Lean.Environment, `Mathlib.Lean.Elab.InfoTree, `Mathlib.Tactic.Linter.UnusedInstancesInType, `Mathlib.Tactic.Linter.OverlappingInstances, `Mathlib.Tactic.Linter.PrivateModule, `Mathlib.Tactic.Linter.TacticDocumentation, `Mathlib.Tactic.Linter.UnusedTacticExtension, `Mathlib.Tactic.Linter.UnusedTactic, `Mathlib.Tactic.DeclarationNames, `Mathlib.Tactic.Linter.Style, `Mathlib.Tactic.Linter.Whitespace, `Mathlib.Lean.Elab.Tactic.Meta, `Mathlib.Lean.ContextInfo, `Mathlib.Tactic.TacticAnalysis, `Mathlib.Tactic.MinImports, `Mathlib.Tactic.ExtractGoal, `Mathlib.Util.ParseCommand, `Mathlib.Tactic.TacticAnalysis.Declarations, `Mathlib.Tactic.TypeStar, `Mathlib.Tactic.Linter.Lint, `Mathlib.Util.CodeActions.BinderPlicity, `Mathlib.Util.CodeActions, `Mathlib.Init, `Mathlib.Lean.Meta.Simp, `Mathlib.Lean.Name, `Mathlib.Tactic.Eqns, `Mathlib.Tactic.Translate.Attributes, `Mathlib.Tactic.Translate.Reorder, `Mathlib.Tactic.Translate.UnfoldBoundary, `Mathlib.Data.String.Defs, `Mathlib.Tactic.Translate.GuessName, `Mathlib.Tactic.Translate.Expr, `Mathlib.Tactic.Translate.Core, `Mathlib.Tactic.Translate.ToAdditive, `Mathlib.Tactic.ToAdditive, `Mathlib.Algebra.Regular.Defs, `Mathlib.Lean.Meta, `Mathlib.Tactic.MkIffOfInductiveProp, `Mathlib.Util.AddRelatedDecl, `Mathlib.Tactic.Simps.NotationClass, `Mathlib.Tactic.Simps.Basic, `Mathlib.Tactic.Simps, `Mathlib.Algebra.Group.Semigroup, `Mathlib.Data.Nat.BinaryRec, `Mathlib.Data.Nat.Notation, `Mathlib.Tactic.Push.Attr, `Mathlib.Algebra.Group.Monoid, `Mathlib.Data.Int.Notation, `Mathlib.Tactic.CrossRefAttribute, `Mathlib.Tactic.OfNat, `Mathlib.Algebra.Group.DivInvMonoid, `Mathlib.Algebra.Group.Defs, `Mathlib.Lean.PrettyPrinter.Delaborator, `Mathlib.Tactic.SetNotationForOrder, `Mathlib.Tactic.Translate.TagUnfoldBoundary, `Mathlib.Tactic.Translate.ToDual, `Mathlib.Tactic.ToDual, `Mathlib.Data.Set.Defs, `Mathlib.Tactic.ExtendDoc, `Mathlib.Order.Defs.Unbundled, `Mathlib.Algebra.Group.Semiconj.Defs, `Mathlib.Algebra.Group.Commute.Defs, `Mathlib.Algebra.Notation.Defs, `Mathlib.Basic.IsEmpty.Defs, `Mathlib.Basic.ExistsUnique, `Mathlib.Tactic.Attr.Register, `Mathlib.Basic.Logic.Basic, `Mathlib.Basic.Nonempty, `Mathlib.Basic.Nontrivial.Defs, `Mathlib.Logic.Function.Defs, `Mathlib.Logic.Function.Basic, `Mathlib.Tactic.Inhabit, `Mathlib.Basic.Unique, `Mathlib.Tactic.Core, `Mathlib.Tactic.SplitIfs, `Mathlib.Basic.FunLike.Basic, `Mathlib.Basic.FunLike.Embedding, `Mathlib.Basic.FunLike.Equiv, `Mathlib.Logic.Relator, `Mathlib.Tactic.Use, `Mathlib.Tactic.SimpRw, `Mathlib.Order.Defs.Prop, `Mathlib.Logic.Relation, `Mathlib.Lean.Elab.Term, `Mathlib.Util.WithWeakNamespace, `Mathlib.Tactic.ScopedNS, `Mathlib.Util.Notation3, `Mathlib.Data.Quot, `Mathlib.Data.Subtype, `Mathlib.Logic.Equiv.Defs, `Mathlib.Algebra.Opposites, `Mathlib.Logic.Function.Conjugate, `Mathlib.Logic.Function.Iterate, `Mathlib.Tactic.Spread, `Mathlib.Algebra.Group.Action.Defs, `Mathlib.Algebra.Group.InjSurj, `Mathlib.Tactic.DepRewrite, `Mathlib.Data.Int.Init, `Mathlib.Algebra.Group.Basic, `Mathlib.Algebra.Group.Semiconj.Basic, `Mathlib.Algebra.Group.Commute.Basic, `Mathlib.Algebra.Group.SelfInv, `Mathlib.Algebra.Group.Torsion, `Mathlib.Tactic.Conv, `Mathlib.Algebra.Group.Opposite, `Mathlib.Tactic.ApplyCongr, `Mathlib.Lean.Meta.Basic, `Mathlib.Tactic.ApplyAt, `Mathlib.Tactic.ApplyWith, `Mathlib.Tactic.PPWithUniv, `Mathlib.Tactic.Basic, `Mathlib.Util.AtLocation, `Mathlib.Tactic.Push, `Mathlib.Tactic.ByCases, `Mathlib.Tactic.ByContra, `Mathlib.Tactic.CasesM, `Mathlib.Tactic.Check, `Mathlib.Tactic.Choose, `Mathlib.Tactic.ClearExclamation, `Mathlib.Tactic.ClearExcept, `Mathlib.Tactic.Clear_, `Mathlib.Tactic.GCongr.ForwardAttr, `Mathlib.Tactic.GCongr.Core, `Mathlib.Tactic.Hint, `Mathlib.Tactic.GCongr, `Mathlib.Tactic.GRewrite.Core, `Mathlib.Tactic.GRewrite.Elab, `Mathlib.Tactic.GRewrite, `Mathlib.Tactic.NthRewrite, `Mathlib.Tactic.ClickSuggestions.Util, `Mathlib.Tactic.ClickSuggestions.SectionState, `Mathlib.Control.Combinators, `Mathlib.Tactic.Attr.Core, `Mathlib.Control.Basic, `Mathlib.Tactic.ClickSuggestions.Rewrite, `Mathlib.Tactic.ClickSuggestions.GRewrite, `Mathlib.Tactic.ClickSuggestions.Apply, `Mathlib.Tactic.ClickSuggestions.ApplyAt, `Mathlib.Lean.FoldEnvironment, `Mathlib.Lean.Meta.RefinedDiscrTree.Basic, `Mathlib.Lean.Meta.RefinedDiscrTree.Encode, `Mathlib.Lean.Meta.RefinedDiscrTree.Lookup, `Mathlib.Lean.Meta.RefinedDiscrTree.Initialize, `Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Tactic.ClickSuggestions.FindPremises, `Mathlib.Tactic.ClickSuggestions.TryPremises, `Mathlib.Tactic.ClickSuggestions.Unfold, `Mathlib.Lean.Meta.KAbstractPositions, `Mathlib.Lean.GoalsLocation, `Mathlib.Tactic.ClickSuggestions, `Mathlib.Tactic.Coe, `Mathlib.Lean.Meta.CongrTheorems, `Mathlib.Tactic.Relation.Rfl, `Mathlib.Tactic.CongrExclamation, `Mathlib.Tactic.TermCongr, `Mathlib.Tactic.CongrM, `Mathlib.Tactic.Constructor, `Mathlib.Tactic.Contrapose, `Mathlib.Tactic.Convert, `Mathlib.Lean.MessageData.Trace, `Mathlib.Tactic.DefEqAbuse, `Mathlib.Tactic.DefEqTransformations, `Mathlib.Tactic.DeprecateTo, `Mathlib.Tactic.DSimpPercent, `Mathlib.Tactic.ErwQuestion, `Mathlib.Tactic.ExistsI, `Mathlib.Tactic.FailIfNoProgress, `Mathlib.Tactic.Find, `Mathlib.Tactic.FunProp.Decl, `Mathlib.Tactic.FunProp.Mor, `Mathlib.Tactic.FunProp.ToBatteries, `Mathlib.Tactic.FunProp.FunctionData, `Mathlib.Tactic.FunProp.Types, `Mathlib.Tactic.FunProp.Theorems, `Mathlib.Tactic.FunProp.Attr, `Mathlib.Tactic.FunProp.Core, `Mathlib.Tactic.InferParam, `Mathlib.Tactic.FunProp.Elab, `Mathlib.Tactic.FunProp, `Mathlib.Tactic.GrindAttrs, `Mathlib.Tactic.GuardGoalNums, `Mathlib.Tactic.GuardHypNums, `Mathlib.Tactic.HigherOrder, `Mathlib.Util.TermReduce, `Mathlib.Tactic.IrreducibleDef, `Mathlib.Tactic.Lift, `Mathlib.Tactic.Linter.HaveLetLinter, `Mathlib.Tactic.Linter.MinImports, `Mathlib.Tactic.Linter.PPRoundtrip, `Mathlib.Tactic.Linter.UpstreamableDecl, `Mathlib.Tactic.Linter, `Mathlib.Tactic.Observe, `Mathlib.Tactic.RSuffices, `Mathlib.Tactic.Recover, `Mathlib.Tactic.Rename, `Mathlib.Util.Tactic, `Mathlib.Tactic.RenameBVar, `Mathlib.Tactic.Says, `Mathlib.Tactic.Set, `Mathlib.Lean.Elab.Tactic.Basic, `Mathlib.Tactic.Setm, `Mathlib.Tactic.SimpIntro, `Mathlib.Tactic.Simproc.ExistsAndEq, `Mathlib.Tactic.Subsingleton, `Mathlib.Tactic.Substs, `Mathlib.Tactic.SuccessIfFailWithMsg, `Mathlib.Tactic.SudoSetOption, `Mathlib.Tactic.SwapVar, `Mathlib.Tactic.Tauto, `Mathlib.Tactic.ToFun, `Mathlib.Tactic.ToExpr, `Mathlib.Tactic.ToLevel, `Mathlib.Tactic.Trace, `Mathlib.Tactic.UnsetOption, `Mathlib.Tactic.Variable, `Mathlib.Tactic.Widget.SelectInsertParamsClass, `Mathlib.Tactic.Widget.SelectPanelUtils, `Mathlib.Tactic.Widget.Calc, `Mathlib.Tactic.Widget.CongrM, `Mathlib.Tactic.Widget.Conv, `Mathlib.Tactic.Widget.LibraryRewrite, `Mathlib.Tactic.WLOG, `Mathlib.Util.CountHeartbeats, `Mathlib.Util.PrintSorries, `Mathlib.Util.TransImports, `Mathlib.Util.WhatsNew, `Mathlib.Tactic.Common, `Mathlib.Algebra.Divisibility.Basic, `Mathlib.Algebra.Notation.Pi.Defs, `Mathlib.Algebra.Group.Hom.Defs, `Mathlib.Algebra.Divisibility.Hom, `Mathlib.Algebra.Group.Equiv.Defs, `Mathlib.Algebra.Group.Hom.Basic, `Mathlib.Control.EquivFunctor, `Mathlib.Data.Option.Defs, `Mathlib.Data.Option.Basic, `Mathlib.Logic.Equiv.Option, `Mathlib.Data.Sigma.Basic, `Mathlib.Util.CompileInductive, `Mathlib.Logic.Equiv.Prod, `Mathlib.Logic.Equiv.Sum, `Mathlib.Logic.Equiv.Basic, `Mathlib.Algebra.Group.Equiv.Basic, `Mathlib.Algebra.Group.Equiv.Opposite, `Mathlib.Algebra.Notation.Pi.Basic, `Mathlib.Algebra.Group.TypeTags.Basic, `Mathlib.Tactic.FBinop, `Mathlib.Basic.SProd, `Mathlib.Data.Set.CoeSort, `Mathlib.Order.Notation, `Mathlib.Data.Set.Operations, `Mathlib.Algebra.Group.Even, `Mathlib.Algebra.Group.Nat.Defs, `Mathlib.Algebra.Group.TypeTags.Hom, `Mathlib.Algebra.Group.Nat.Hom, `Mathlib.Algebra.GroupWithZero.Defs, `Mathlib.Order.Defs.PartialOrder, `Mathlib.Tactic.Basify.Attr, `Mathlib.Algebra.NeZero, `Mathlib.Algebra.GroupWithZero.NeZero, `Mathlib.Algebra.GroupWithZero.Basic, `Mathlib.Algebra.GroupWithZero.Hom, `Mathlib.Data.Sum.Basic, `Mathlib.Algebra.Group.Pi.Basic, `Mathlib.Tactic.FastInstance, `Mathlib.Algebra.Group.Hom.Instances, `Mathlib.Algebra.Group.IsCommutative, `Mathlib.Data.Nat.Init, `Mathlib.Data.Nat.Cast.Defs, `Mathlib.Data.Int.Cast.Defs, `Mathlib.Algebra.Ring.Defs, `Mathlib.Util.AtomM, `Mathlib.Data.List.TFAE, `Mathlib.Logic.Pairwise, `Mathlib.Data.List.Pairwise, `Mathlib.Tactic.TFAE, `Mathlib.Algebra.Ring.Basic, `Mathlib.Algebra.Ring.Hom.Defs, `Mathlib.Algebra.CharZero.Defs, `Mathlib.Algebra.GroupWithZero.Nat, `Mathlib.Data.Ordering.Basic, `Mathlib.Order.Defs.LinearOrder, `Mathlib.Data.Nat.Basic, `Mathlib.Algebra.Ring.Nat, `Mathlib.Data.Nat.Cast.Basic, `Mathlib.Util.AtomM.Recurse, `Mathlib.Algebra.Group.Int.Defs, `Mathlib.Data.Int.Basic, `Mathlib.Data.Int.Cast.Basic, `Mathlib.Algebra.Ring.Int.Defs, `Mathlib.Algebra.Group.Units.Defs, `Mathlib.Algebra.Group.Units.Basic, `Mathlib.Data.Prod.Basic, `Mathlib.Basic.Nontrivial.Basic, `Mathlib.Tactic.Nontriviality.Core, `Mathlib.Tactic.Nontriviality, `Mathlib.Algebra.GroupWithZero.Units.Basic, `Mathlib.Algebra.Group.Semiconj.Units, `Mathlib.Algebra.GroupWithZero.Semiconj, `Mathlib.Algebra.Group.Commute.Units, `Mathlib.Algebra.GroupWithZero.Commute, `Mathlib.Algebra.Notation.Bracket, `Mathlib.Algebra.Ring.Semiconj, `Mathlib.Algebra.GroupWithZero.InjSurj, `Mathlib.Algebra.Ring.InjSurj, `Mathlib.Algebra.Group.Units.Hom, `Mathlib.Algebra.Ring.Units, `Mathlib.Algebra.Ring.Commute, `Mathlib.Data.Nat.Cast.Commute, `Mathlib.Tactic.HaveI, `Mathlib.Lean.Expr.Rat, `Mathlib.Data.Rat.Init, `Mathlib.Algebra.Field.Defs, `Mathlib.Algebra.Group.Invertible.Defs, `Mathlib.Algebra.Group.Invertible.Basic, `Mathlib.Algebra.GroupWithZero.Invertible, `Mathlib.Tactic.NormNum.Result, `Mathlib.Util.Qq, `Mathlib.Tactic.NormNum.Core, `Mathlib.Tactic.NormNum.Basic, `Mathlib.Tactic.TryThis]
  -- Enforce Mathlib's default linters and style options.
  leanOptions := mathlibLeanOptions

-- NB. When adding further libraries, check if they should be excluded from `getLeanLibs` in
-- `scripts/mk_all.lean`.
lean_lib Cache where
  globs := #[`Cache.+]
  -- The `Cache` modules do not use the module system, but they import each other and thus
  -- the `requiresModuleSystem` package option set above.
  allowNonModules := true

lean_lib MathlibTest where
  globs := #[`MathlibTest.+]
  leanOptions := mathlibTestOptions
  allowNonModules := true

lean_lib Archive where
  leanOptions := mathlibLeanOptions

lean_lib Counterexamples where
  leanOptions := mathlibLeanOptions

/-- Wanted statements: `Wanted/X/Y/Z.lean` contains the `proof_wanted` statements
corresponding to `Mathlib/X/Y/Z.lean`. Each file carries a copyright header naming the
author of the original statements, but beyond that contains only imports, context setup
(`open`/`namespace`/`variable`) and `proof_wanted` statements; in particular there are no
module docstrings, so the header style linter is disabled.
`proof_wanted` elaborates to a `private` placeholder declaration, so every module here
consists solely of private declarations; the `privateModule` linter is disabled accordingly
(neither `@[expose] public section` nor a `public` modifier suppresses it, since the
placeholder is unconditionally `private`). -/
lean_lib Wanted where
  leanOptions := mathlibLeanOptions.push ⟨`weak.linter.style.header, false⟩
    |>.push ⟨`weak.linter.privateModule, false⟩

/-- Additional documentation in the form of modules that only contain module docstrings. -/
lean_lib docs where
  roots := #[`docs]

/-!
## Executables provided by Mathlib
-/

/--
`lake exe autolabel 150100` adds a topic label to PR `150100` if there is a unique choice.
This requires GitHub CLI `gh` to be installed!

Calling `lake exe autolabel` without a PR number will print the result without applying
any labels online.
-/
lean_exe autolabel where
  srcDir := "scripts"

/-- `lake exe cache get` retrieves precompiled `.olean` files from a central server. -/
lean_exe cache where
  root := `Cache.Main
  -- As for `lean_lib Cache`: the root does not use the module system either, and the
  -- executable's configuration does not inherit the library's.
  allowNonModules := true

/-- `lake exe cache-test` runs the cache tool's unit tests (container URL
construction, per-repo trust-ordered allowlist, `--cache-from` parsing).
Runnable standalone — does not require building Mathlib or `MathlibTest`. -/
lean_exe «cache-test» where
  root := `Cache.Test

/-- `lake exe check-yaml` verifies that all declarations referred to in `docs/*.yaml` files exist. -/
lean_exe «check-yaml» where
  srcDir := "scripts"
  supportInterpreter := true

/-- `lake exe mk_all` constructs the files containing all imports for a project. -/
lean_exe mk_all where
  srcDir := "scripts"
  supportInterpreter := true
  -- Executables which import `Lake` must set `-lLake`.
  weakLinkArgs := #["-lLake"]

/-- `lake exe lint-style` runs text-based style linters. -/
lean_exe «lint-style» where
  srcDir := "scripts"
  supportInterpreter := true
  -- Executables which import `Lake` must set `-lLake`.
  weakLinkArgs := #["-lLake"]

/-- `lake exe check-title-labels` checks if a PR title obeys some basic formatting requirements.
Currently, these checks are quite lenient, but could be made stricter in the future. -/
lean_exe «check_title_labels» where
  srcDir := "scripts"

/-- `lake exe nightly-testing-checklist` reports nightly-testing branch status. -/
lean_exe «nightly-testing-checklist» where
  srcDir := "scripts"

lean_exe mathlib_test_executable where
  root := `MathlibTest.MathlibTestExecutable

/-!
## Other configuration
-/

/--
When a package depending on Mathlib updates its dependencies,
update its toolchain to match Mathlib's and fetch the new cache.
-/
post_update pkg do
  let rootPkg ← getRootPackage
  if rootPkg.baseName = pkg.baseName then
    return -- do not run in Mathlib itself
  if (← IO.getEnv "MATHLIB_NO_CACHE_ON_UPDATE") != some "1" then
    -- Check if Lake version matches toolchain version
    let toolchainFile := rootPkg.dir / "lean-toolchain"
    let toolchainContent ← IO.FS.readFile toolchainFile
    let toolchainVersion := match toolchainContent.trimAscii.copy.splitOn ":" with
      | [_, version] => version
      | _ => toolchainContent.trimAscii.copy  -- fallback to full content if format is unexpected
    -- Lean.versionString does not start with a `v`, while the `lean-toolchain` file is flexible.
    let toolchainVersion := (toolchainVersion.dropPrefix "v").copy
    if Lean.versionString ≠ toolchainVersion then
      IO.println s!"Not running `lake exe cache get` yet, as \
        the `lake` version ({Lean.versionString}) does not match \
        the toolchain version ({toolchainVersion}) in the project.\n\
        You should run `lake exe cache get` manually."
      return
    let exeFile ← runBuild cache.fetch
    -- Run the command in the root package directory,
    -- which is the one that holds the .lake folder and lean-toolchain file.
    let cwd ← IO.Process.getCurrentDir
    let exitCode ← try
      IO.Process.setCurrentDir rootPkg.dir
      env exeFile.toString #["get"]
    finally
      IO.Process.setCurrentDir cwd
    if exitCode ≠ 0 then
      error s!"{pkg.baseName}: failed to fetch cache"

lean_lib JacobiOldAbel where
  roots := #[`JacobiOldAbel]

lean_lib JacobiOldNoncommRing where
  roots := #[`JacobiOldNoncommRing]

lean_lib JacobiCurrentNoncommRing where
  roots := #[`JacobiCurrentNoncommRing]

lean_lib JacobiHarness where
  roots := #[`JacobiHarness]

lean_lib JacobiBenchCurrent where
  roots := #[`JacobiBenchCurrent]

lean_lib JacobiKernelHarness where
  roots := #[`JacobiKernelHarness]

lean_lib JacobiBenchKernel where
  roots := #[`JacobiBenchKernel]
