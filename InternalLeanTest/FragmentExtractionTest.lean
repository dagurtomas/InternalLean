/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Examples.UniverseHierarchy
public import InternalLean.Command
public import InternalLeanTest.InternalTacticTest
public import InternalLeanTest.TinyNat

@[expose] public section

open Lean Elab Command
open InternalLean

/-- A minimal theory whose one theorem uses every model-renderable declaration. -/
declare_type_theory F1FragmentEverything where
  syntax_sort A
  judgment Good (a : A)
  lf_opaque a : A
  rule good_a : Good a

namespace F1FragmentEverything
internal def good_a_thm : Good a := good_a
end F1FragmentEverything

/-- A minimal theory whose fragment report carries an admitted dependency. -/
declare_type_theory F1Admission where
  syntax_sort A

/-- warning: internal declaration 'F1Admission.a' was admitted by `sorry`; the annotation was
checked in theory 'F1Admission', but the body was not checked. Use
`#lint_type_theory_sorries F1Admission` to list current admissions. -/
#guard_msgs (whitespace := lax) in
internal def F1Admission.a : A := sorry

namespace F1Admission
internal def b : A := a
end F1Admission

namespace InternalLeanTest.FragmentExtraction

def assertFragment (ok : Bool) (msg : String) : CommandElabM Unit := do
  unless ok do
    throwError msg

/-- info: theory fragment report for UniverseHierarchy.zero_le_succ_zero
mode: report-only; no fragment theory was registered
model fields: full=21, fragment=5
level parameters (1):
  - u: universe annotation of syntax_sort Level
syntax sorts (1):
  - Level: global LF head used by theorem zero_le_succ_zero
syntax abbreviations: none
syntax definitions: none
judgment abbreviations: none
context zones: none
binder classes: none
judgments (1):
  - Le: dependency of theorem zero_le_succ_zero
LF opaque constants (2):
  - zero: dependency of theorem zero_le_succ_zero
  - succ: dependency of theorem zero_le_succ_zero
side-condition solvers: none
conversion plugins: none
level-normalizer profiles: none
rules (1):
  - le_succ: dependency of theorem zero_le_succ_zero
LF object definitions: none
LF judgment theorems (1):
  - zero_le_succ_zero: seed theorem zero_le_succ_zero
side-condition certificates: none
carried admissions: none
carried metadata: none
dropped metadata: none -/
#guard_msgs (whitespace := lax) in
#print_theory_fragment UniverseHierarchy zero_le_succ_zero

run_cmd do
  let report ← TheoryFragment.buildReport `UniverseHierarchy `zero_le_succ_zero
  let c := report.closure
  assertFragment (c.syntaxSorts.contains `Level) "zero fragment omitted Level"
  assertFragment (!c.syntaxSorts.contains `Ty) "zero fragment should not include Ty"
  assertFragment (c.judgments.contains `Le) "zero fragment omitted Le"
  assertFragment (!c.judgments.contains `IsTy) "zero fragment should not include IsTy"
  assertFragment (c.lfOpaqueConsts.contains `zero) "zero fragment omitted zero"
  assertFragment (c.lfOpaqueConsts.contains `succ) "zero fragment omitted succ"
  assertFragment (!c.lfOpaqueConsts.contains `lift) "zero fragment should not include lift"
  assertFragment (c.rules.contains `le_succ) "zero fragment omitted le_succ"
  assertFragment (!c.rules.contains `lift_wf) "zero fragment should not include lift_wf"
  assertFragment (report.fragmentModelFieldCount < report.fullModelFieldCount)
    "fragment model field count should be smaller for zero_le_succ_zero"

run_cmd do
  let report ← TheoryFragment.buildReport `TinyNat `one_wf
  let c := report.closure
  assertFragment (c.lfJudgmentTheorems.contains `one_wf) "one_wf fragment omitted root"
  assertFragment (c.lfJudgmentTheorems.contains `zero_wf) "one_wf fragment omitted zero_wf"
  assertFragment (c.rules.contains `succ_intro) "one_wf fragment omitted succ_intro"
  assertFragment (c.rules.contains `zero_intro) "one_wf fragment omitted zero_intro"

run_cmd do
  let report ← TheoryFragment.buildReport `TinyNat `doubleTwo
  let c := report.closure
  assertFragment (c.lfObjectDefs.contains `doubleTwo) "doubleTwo fragment omitted root"
  assertFragment (c.lfObjectDefs.contains `double) "doubleTwo fragment omitted double"
  assertFragment (c.lfObjectDefs.contains `two) "doubleTwo fragment omitted two"
  assertFragment (c.lfObjectDefs.contains `add) "doubleTwo fragment omitted add"
  assertFragment (c.lfOpaqueConsts.contains `natRec) "doubleTwo fragment omitted natRec"

run_cmd do
  let report ← TheoryFragment.buildReport `UniverseHierarchy `liftedZeroUnivLmax_wf
  let c := report.closure
  assertFragment (c.sideConditionSolvers.contains `level_norm_solver)
    "level-normalizer fragment omitted solver"
  assertFragment (c.conversionPlugins.contains `level_norm)
    "level-normalizer fragment omitted conversion plugin"
  assertFragment (c.levelNormalizerProfiles.contains `level_norm_solver)
    "level-normalizer fragment omitted profile"
  assertFragment (c.sideConditionCertificates.contains `lift_lmax_left_wf.side_condition.le_left)
    "level-normalizer fragment omitted checked side-condition certificate"
  assertFragment (c.rules.contains `lift_lmax_left_wf)
    "level-normalizer fragment omitted certified rule"

run_cmd do
  let report ← TheoryFragment.buildReport `F1FragmentEverything `good_a_thm
  assertFragment (report.fragmentModelFieldCount == report.fullModelFieldCount)
    "fragment using all declarations should have the same model field count as the full theory"

run_cmd do
  let report ← TheoryFragment.buildReport `InternalTacticSimpPluginSmoke `beta_plugin_simp
  assertFragment (report.closure.conversionPlugins.contains `beta_step)
    "fragment report should carry theorem statement conversion plugin beta_step"

run_cmd do
  let report ← TheoryFragment.buildReport `F1Admission `b
  let carriesA := report.carriedAdmissions.foldl (fun ok a => ok || a.declName == `a) false
  assertFragment carriesA "fragment report should carry admitted dependency a"
  assertFragment (report.closure.lfOpaqueConsts.contains `a)
    "admitted object dependency should remain in the LF opaque closure"

run_cmd do
  let before ← liftCoreM getTheories
  let first ← TheoryFragment.reportStringFor `UniverseHierarchy `zero_le_succ_zero
  let second ← TheoryFragment.reportStringFor `UniverseHierarchy `zero_le_succ_zero
  let after ← liftCoreM getTheories
  assertFragment (first == second) "fragment reports should be deterministic"
  assertFragment (before.toList.length == after.toList.length)
    "fragment report should not register a new theory"
  assertFragment (after.find? `UniverseHierarchy).isSome
    "fragment report should preserve the original theory registry"

end InternalLeanTest.FragmentExtraction
