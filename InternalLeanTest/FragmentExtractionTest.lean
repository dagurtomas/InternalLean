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

/-- Parent-fragment smoke theory for F2 standalone flattened extraction. -/
declare_type_theory F2ParentBase where
  syntax_sort A
  judgment Good (a : A)
  lf_opaque a : A
  rule good_a : Good a

declare_type_theory F2ParentChild extends F2ParentBase where

namespace F2ParentChild
internal theorem good_a_thm : Good a := good_a
end F2ParentChild

extract_theory_fragment F2UniverseFragment from UniverseHierarchy for zero_le_succ_zero
#check F2UniverseFragment.zero_le_succ_zero

/-- info: type theory F2UniverseFragment: direct-LF signature
Lean-visible anchor: F2UniverseFragment.theory
internal declarations: 1 checked/replayed, 0 admitted by `sorry`
LF metadata: 1 syntax sort(s), 0 syntax abbreviation(s), 0 judgment abbreviation(s),
  1 judgment(s), 1 rule(s), 1 checked judgment theorem(s)
generated admitted transports recorded: 0
user workflow: `#print_model_obligations`, `generate_model_interface`,
  `#print_model_template`, `#print_model_transport_status`, `generate_model_transport`,
  `generate_model_transports` -/
#guard_msgs (whitespace := lax) in
#check_theory F2UniverseFragment

extract_theory_fragment F2AdmissionFragment from F1Admission for b
#check F2AdmissionFragment.a

/-- warning: type theory 'F2AdmissionFragment' has 1 admitted internal declaration(s):
admitted internal def F2AdmissionFragment.a : A [missing doc]
downstream declarations mentioning admissions:
internal def b depends on admitted a -/
#guard_msgs (whitespace := lax) in
#lint_type_theory_sorries F2AdmissionFragment

extract_theory_fragment F2LevelNormalizerFragment from UniverseHierarchy for liftedZeroUnivLmax_wf
extract_theory_fragment F2ParentFragment from F2ParentChild for good_a_thm
extract_theory_fragment F4UniverseMultiFragment from UniverseHierarchy for zero_le_succ_zero
  liftedZeroUniv_wf
#check F4UniverseMultiFragment.zero_le_succ_zero
#check F4UniverseMultiFragment.liftedZeroUniv
#check F4UniverseMultiFragment.liftedZeroUniv_wf

generate_model_interface F2UniverseFragment as Model
generate_syntactic_model_instance F2UniverseFragment as syntacticModel for Model
generate_model_restriction UniverseHierarchy to F2UniverseFragment as restrictUniverseToZeroFragment
generate_model_transport UniverseHierarchy zero_le_succ_zero for Model
generate_model_transport F2UniverseFragment zero_le_succ_zero for Model

#check F2UniverseFragment.syntacticModel
#check restrictUniverseToZeroFragment
#check (restrictUniverseToZeroFragment UniverseHierarchy.natModel : F2UniverseFragment.Model)
#check F2UniverseFragment.Model.zero_le_succ_zero
#check UniverseHierarchy.Model.zero_le_succ_zero

example :
    F2UniverseFragment.Model.zero_le_succ_zero
        (restrictUniverseToZeroFragment UniverseHierarchy.natModel) =
      UniverseHierarchy.Model.zero_le_succ_zero UniverseHierarchy.natModel := rfl

def directZeroFragmentModel : F2UniverseFragment.Model where
  Level := Nat
  Le := fun i j => PLift (i ≤ j)
  zero := 0
  succ := Nat.succ
  le_succ := fun i => ⟨Nat.le_succ i⟩

#check (F2UniverseFragment.Model.zero_le_succ_zero directZeroFragmentModel)

generate_model_interface F1FragmentEverything as Model

/--
error: cannot generate model restriction from 'UniverseHierarchy' to 'F1FragmentEverything':
  fragment model field 'A' has no matching source model field in 'UniverseHierarchy.Model'
-/
#guard_msgs (whitespace := lax) in
generate_model_restriction UniverseHierarchy to F1FragmentEverything as badRestriction

/-- error: unknown type theory 'NoSuchTheory' -/
#guard_msgs in
extract_theory_fragment F2NegativeUnknownTheory from NoSuchTheory for foo

/-- error: unknown checked internal declaration 'nope' in type theory 'UniverseHierarchy' -/
#guard_msgs in
extract_theory_fragment F2NegativeUnknownRoot from UniverseHierarchy for nope

/-- error: extract_theory_fragment requires at least one root declaration after `for` -/
#guard_msgs in
extract_theory_fragment F4NegativeNoRoots from UniverseHierarchy for

/-- error: unknown checked internal declaration 'nope' in type theory 'UniverseHierarchy' -/
#guard_msgs in
extract_theory_fragment F4NegativeUnknownRoot from UniverseHierarchy for zero_le_succ_zero nope

declare_type_theory F2NegativeClash where
  syntax_sort A

/-- error: type theory 'F2NegativeClash' has already been declared -/
#guard_msgs in
extract_theory_fragment F2NegativeClash from UniverseHierarchy for zero_le_succ_zero

declare_type_theory F2NegativeBadRoot where
  syntax_sort A

/-- error: Unknown identifier `missing` -/
#guard_msgs in
internal def F2NegativeBadRoot.bad : A := missing

/-- error: unknown checked internal declaration 'bad' in type theory 'F2NegativeBadRoot' -/
#guard_msgs in
extract_theory_fragment F2NegativeBadRootFragment from F2NegativeBadRoot for bad

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

run_cmd do
  let report ← TheoryFragment.buildReport `UniverseHierarchy `zero_le_succ_zero
  let expectedRaw := TheoryFragment.buildFragmentSignature `F2UniverseFragment report
  let expected ← liftCoreM do
    let head ← flattenSignature expectedRaw
    elaborateImplicitAppsInSignatureWithEnv head expectedRaw
  let some actual ← liftCoreM <| getTheory? `F2UniverseFragment
    | throwError "missing extracted F2UniverseFragment"
  assertFragment (actual == expected)
    "extracted fragment source records should match the filtered source signature"

run_cmd do
  let some sourceChecked ← liftCoreM <| getCheckedTheory? `UniverseHierarchy
    | throwError "missing source UniverseHierarchy checked signature"
  let some fragmentChecked ← liftCoreM <| getCheckedTheory? `F2UniverseFragment
    | throwError "missing extracted F2UniverseFragment checked signature"
  let some sourceTheorem := sourceChecked.lfJudgmentTheorems.find? (fun t =>
      t.name == `zero_le_succ_zero)
    | throwError "missing source theorem zero_le_succ_zero"
  let some fragmentTheorem := fragmentChecked.lfJudgmentTheorems.find? (fun t =>
      t.name == `zero_le_succ_zero)
    | throwError "missing fragment theorem zero_le_succ_zero"
  assertFragment (objectExprEq (eraseObjExprScopes sourceTheorem.judgmentExpr)
      (eraseObjExprScopes fragmentTheorem.judgmentExpr))
    "fragment theorem statement should equal the source theorem statement"
  let evidence? ← liftCoreM <| findInternalDeclarationEvidence? `F2UniverseFragment
    `zero_le_succ_zero
  let some evRec := evidence?
    | throwError "missing fragment theorem evidence"
  assertFragment (evRec.kind == .checkedJudgmentTheorem)
    "fragment root theorem should be checked, not admitted"

run_cmd do
  let some sourceChecked ← liftCoreM <| getCheckedTheory? `UniverseHierarchy
    | throwError "missing source UniverseHierarchy checked signature"
  let some fragmentChecked ← liftCoreM <| getCheckedTheory? `F2UniverseFragment
    | throwError "missing extracted F2UniverseFragment checked signature"
  let sourceCert ← kernelLFReplayCertificateForTheorem sourceChecked `zero_le_succ_zero
  let fragmentKernelSig ← match checkedSignatureToKSignature fragmentChecked.name
      fragmentChecked.lfSyntaxDefs fragmentChecked.lfOpaqueConsts fragmentChecked.lfContextZones
      fragmentChecked.lfBinderClasses fragmentChecked.lfConversionPlugins
      fragmentChecked.lfRuleSchemas fragmentChecked.lfObjectDefs fragmentChecked.lfJudgmentTheorems
    with
    | .ok sig => pure sig
    | .error err => throwError err
  let fragmentCert : Kernel.KernelLFReplayCertificate := {
    sourceCert with signature := fragmentKernelSig }
  match fragmentCert.check with
  | .ok _ => pure ()
  | .error err => throwError "source certificate failed against fragment signature: {err}"

run_cmd do
  let env ← getEnv
  for n in [`Level, `Le, `zero, `succ, `le_succ, `zero_le_succ_zero] do
    assertFragment (env.contains (lfQuoteDeclName `F2UniverseFragment n))
      s!"fragment omitted quote stub for {n}"
  assertFragment (env.contains (lfMirrorDeclName `F2UniverseFragment `Le))
    "fragment omitted mirror declaration for Le"
  assertFragment (env.contains (theoryAnchorName `F2UniverseFragment))
    "fragment omitted theory anchor"
  let some _ ← liftCoreM <| internalSourceDeclAnchorName? `F2UniverseFragment `Le
    | throwError "fragment omitted source anchor for Le"

run_cmd do
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents `F2AdmissionFragment
  assertFragment (admissions.any (fun a => a.declName == `a))
    "extracted fragment should carry admitted dependency a"
  let report ← TheoryFragment.buildReport `F1Admission `b
  let summary := TheoryFragment.extractionSummaryString `F2AdmissionFragment report
    (TheoryFragment.buildFragmentSignature `F2AdmissionFragment report)
  assertFragment (summary.contains "carried admissions: 1: a")
    "extraction summary should count carried admissions"

run_cmd do
  let some checked ← liftCoreM <| getCheckedTheory? `F2LevelNormalizerFragment
    | throwError "missing F2 level-normalizer fragment"
  assertFragment (checked.lfLevelNormalizerProfiles.any (fun p =>
      p.solverName == `level_norm_solver))
    "level-normalizer fragment should revalidate the profile"
  assertFragment (checked.lfConversionPlugins.any (fun p =>
      p.name == `level_norm && p.levelNormalizer?.isSome))
    "level-normalizer fragment should keep executable plugin provenance"
  let _ ← kernelLFReplayCertificateForTheorem checked `liftedZeroUnivLmax_wf

run_cmd do
  let some sig ← liftCoreM <| getTheory? `F2ParentFragment
    | throwError "missing parent-fragment theory"
  assertFragment sig.parents.isEmpty "extracted parent fragment should be standalone"
  let some checked ← liftCoreM <| getCheckedTheory? `F2ParentFragment
    | throwError "missing parent-fragment checked signature"
  assertFragment (checked.lfSyntaxSorts.any (fun d => d.name == `A))
    "parent fragment should contain inherited flattened declarations"

run_cmd do
  let zeroReport ← TheoryFragment.buildReport `UniverseHierarchy `zero_le_succ_zero
  let multiReport ← TheoryFragment.buildReportForRoots `UniverseHierarchy
    #[`zero_le_succ_zero, `liftedZeroUniv_wf]
  assertFragment (multiReport.closure.lfJudgmentTheorems.contains `zero_le_succ_zero)
    "multi-root fragment omitted first theorem root"
  assertFragment (multiReport.closure.lfJudgmentTheorems.contains `liftedZeroUniv_wf)
    "multi-root fragment omitted second theorem root"
  assertFragment (multiReport.closure.lfObjectDefs.contains `liftedZeroUniv)
    "multi-root fragment omitted object-definition dependency"
  assertFragment (multiReport.fragmentModelFieldCount > zeroReport.fragmentModelFieldCount)
    "multi-root fragment should add fields beyond the zero-only fragment"
  let some checked ← liftCoreM <| getCheckedTheory? `F4UniverseMultiFragment
    | throwError "missing multi-root fragment checked signature"
  assertFragment (checked.lfJudgmentTheorems.any (fun d => d.name == `zero_le_succ_zero))
    "checked multi-root fragment omitted zero theorem"
  assertFragment (checked.lfJudgmentTheorems.any (fun d => d.name == `liftedZeroUniv_wf))
    "checked multi-root fragment omitted lifted theorem"
  assertFragment (checked.lfObjectDefs.any (fun d => d.name == `liftedZeroUniv))
    "checked multi-root fragment omitted lifted object definition"
  assertFragment (!checked.lfOpaqueConsts.any (fun d => d.name == `Pi))
    "multi-root fragment should not include unrelated later extension constants"

run_cmd do
  let report ← TheoryFragment.buildReportForRoots `UniverseHierarchy
    #[`zero_le_succ_zero, `liftedZeroUniv_wf]
  let expectedRaw := TheoryFragment.buildFragmentSignature `F4UniverseMultiFragment report
  let expected ← liftCoreM do
    let head ← flattenSignature expectedRaw
    elaborateImplicitAppsInSignatureWithEnv head expectedRaw
  let some actual ← liftCoreM <| getTheory? `F4UniverseMultiFragment
    | throwError "missing extracted F4UniverseMultiFragment"
  assertFragment (actual == expected)
    "multi-root fragment source records should match the filtered source signature"

run_cmd do
  let some sourceChecked ← liftCoreM <| getCheckedTheory? `UniverseHierarchy
    | throwError "missing source UniverseHierarchy checked signature"
  let some fragmentChecked ← liftCoreM <| getCheckedTheory? `F4UniverseMultiFragment
    | throwError "missing multi-root fragment checked signature"
  let fragmentKernelSig ← match checkedSignatureToKSignature fragmentChecked.name
      fragmentChecked.lfSyntaxDefs fragmentChecked.lfOpaqueConsts fragmentChecked.lfContextZones
      fragmentChecked.lfBinderClasses fragmentChecked.lfConversionPlugins
      fragmentChecked.lfRuleSchemas fragmentChecked.lfObjectDefs fragmentChecked.lfJudgmentTheorems
    with
    | .ok sig => pure sig
    | .error err => throwError err
  for root in #[`zero_le_succ_zero, `liftedZeroUniv_wf] do
    let sourceCert ← kernelLFReplayCertificateForTheorem sourceChecked root
    let fragmentCert : Kernel.KernelLFReplayCertificate := {
      sourceCert with signature := fragmentKernelSig }
    match fragmentCert.check with
    | .ok _ => pure ()
    | .error err => throwError "source certificate for {root} failed in multi fragment: {err}"

run_cmd do
  let report ← TheoryFragment.buildReport `UniverseHierarchy `zero_le_succ_zero
  assertFragment (report.fragmentModelFieldCount < report.fullModelFieldCount)
    "F3 fragment model should have fewer fields than the full UniverseHierarchy model"
  let env ← getEnv
  assertFragment (env.contains `F2UniverseFragment.Model) "missing generated fragment model"
  assertFragment (env.contains `restrictUniverseToZeroFragment) "missing model restriction"

run_cmd do
  let some checked ← liftCoreM <| getCheckedTheory? `F2UniverseFragment
    | throwError "missing extracted F2UniverseFragment checked signature"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents `F2UniverseFragment
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let provenance ← LeanTypeModelGeneration.lfModelObligationProvenanceString checked admittedNames
  assertFragment (provenance.contains "model obligation provenance for F2UniverseFragment")
    "fragment model provenance should render like an ordinary theory"
  assertFragment (provenance.contains "syntax_sort Level")
    "fragment model provenance should mention the retained Level field"

end InternalLeanTest.FragmentExtraction
