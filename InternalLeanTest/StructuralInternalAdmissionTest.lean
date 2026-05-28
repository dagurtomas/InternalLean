/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Structural internal admission tests

These tests cover `internal def ... := sorry` declarations whose checked annotations expand to
structural function or Sigma/package types.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

/-- Assert that a checked declaration is not requested as a user-provided model field. -/
elab "#guard_structural_no_model_field_for " theory:ident decl:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let obs ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  let declName := decl.getId.eraseMacroScopes
  if obs.any (fun o =>
      o.name.eraseMacroScopes == declName && o.generatedRole == .field && o.renderable) then
    throwError "expected '{decl.getId}' not to be a user model field for '{theory.getId}'"

/-- Assert the number of renderable user-provided model fields. -/
elab "#guard_structural_model_field_count " theory:ident expected:num : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let obs ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  let fields := obs.foldl (init := 0) fun n o =>
    if o.generatedRole == .field && o.renderable then n + 1 else n
  unless fields == expected.getNat do
    throwError "expected {expected.getNat} user model field(s) for '{theory.getId}', found \
      {fields}"

declare_type_theory SigmaAdmission where
  syntax_sort Obj : Type
  syntax_sort Fam (x : Obj) : Type
  lf_opaque base : Obj
  lf_opaque mkFam (x : Obj) : Fam x

namespace SigmaAdmission

/-- warning: internal declaration 'SigmaAdmission.pack' was admitted by `sorry`; the annotation
was checked in theory 'SigmaAdmission', but the body was not checked. Use
`#lint_type_theory_sorries SigmaAdmission` to list current admissions. -/
#guard_msgs (whitespace := lax) in
internal def pack : Σ x : Obj, Fam x := sorry

/-- warning: internal declaration 'SigmaAdmission.choose' was admitted by `sorry`; the annotation
was checked in theory 'SigmaAdmission', but the body was not checked. Use
`#lint_type_theory_sorries SigmaAdmission` to list current admissions. -/
#guard_msgs (whitespace := lax) in
internal def choose : Obj → Σ y : Obj, Fam y := sorry

/-- warning: internal declaration 'SigmaAdmission.chooseDep' was admitted by `sorry`; the
annotation was checked in theory 'SigmaAdmission', but the body was not checked. Use
`#lint_type_theory_sorries SigmaAdmission` to list current admissions. -/
#guard_msgs (whitespace := lax) in
internal def chooseDep : (x : Obj) → Σ y : Obj, Fam y := sorry

end SigmaAdmission

extend_type_theory SigmaAdmission where
  lf_def packObj : Obj := fst pack
  syntax_abbrev Pack := Σ x : Obj, Fam x

namespace SigmaAdmission

/-- warning: internal declaration 'SigmaAdmission.viaAbbrev' was admitted by `sorry`; the
annotation was checked in theory 'SigmaAdmission', but the body was not checked. Use
`#lint_type_theory_sorries SigmaAdmission` to list current admissions. -/
#guard_msgs (whitespace := lax) in
internal def viaAbbrev : Pack := sorry

end SigmaAdmission

#check_model_obligations SigmaAdmission
#guard_structural_model_field_count SigmaAdmission 8
#guard_structural_no_model_field_for SigmaAdmission packObj

generate_lf_model_structure SigmaAdmission as SigmaAdmissionModel

#check SigmaAdmission.SigmaAdmissionModel.pack
#check SigmaAdmission.SigmaAdmissionModel.choose
#check SigmaAdmission.SigmaAdmissionModel.chooseDep
#check SigmaAdmission.SigmaAdmissionModel.viaAbbrev

def sigmaAdmissionModel : SigmaAdmission.SigmaAdmissionModel where
  Obj := Unit
  Fam := fun _ => Unit
  base := ()
  mkFam := fun _ => ()
  pack := ⟨(), ()⟩
  choose := fun _ => ⟨(), ()⟩
  chooseDep := fun _ => ⟨(), ()⟩
  viaAbbrev := ⟨(), ()⟩

/-- warning: type theory 'SigmaAdmission' has 4 admitted internal declaration(s):
admitted internal def SigmaAdmission.pack : Σ x : Obj, Fam x [missing doc]
admitted internal def SigmaAdmission.choose : Obj → Σ y : Obj, Fam y [missing doc]
admitted internal def SigmaAdmission.chooseDep (x : Obj) : Σ y : Obj, Fam y [missing doc]
admitted internal def SigmaAdmission.viaAbbrev : Pack [missing doc]
downstream declarations mentioning admissions:
internal def packObj depends on admitted pack -/
#guard_msgs (whitespace := lax) in
#lint_type_theory_sorries SigmaAdmission

declare_type_theory NatIsoAdmission where
  syntax_sort Obj : Type
  syntax_sort NatTrans (C : Obj) (D : Obj) (F : Obj) (G : Obj) : Type
  syntax_sort ObjectwiseNatIso (C : Obj) (D : Obj) (F : Obj) (G : Obj)
    (α : NatTrans C D F G) : Type
  syntax_abbrev NatIso (C : Obj) (D : Obj) (F : Obj) (G : Obj) :=
    Σ α : NatTrans C D F G, ObjectwiseNatIso C D F G α
  lf_opaque C : Obj
  lf_opaque D : Obj
  lf_opaque F : Obj
  lf_opaque G : Obj

namespace NatIsoAdmission

/-- warning: internal declaration 'NatIsoAdmission.beta' was admitted by `sorry`; the annotation
was checked in theory 'NatIsoAdmission', but the body was not checked. Use
`#lint_type_theory_sorries NatIsoAdmission` to list current admissions. -/
#guard_msgs (whitespace := lax) in
internal def beta : NatIso C D F G := sorry

end NatIsoAdmission

#guard_structural_model_field_count NatIsoAdmission 8

generate_lf_model_structure NatIsoAdmission as NatIsoAdmissionModel
#check NatIsoAdmission.NatIsoAdmissionModel.beta

declare_type_theory JudgmentAdmissionClassification where
  syntax_sort Obj : Type
  lf_opaque a : Obj
  judgment J (x : Obj)
  rule ja : J a

namespace JudgmentAdmissionClassification

/-- warning: internal declaration 'JudgmentAdmissionClassification.h' was admitted by `sorry`; the
annotation was checked in theory 'JudgmentAdmissionClassification', but the body was not checked.
Use `#lint_type_theory_sorries JudgmentAdmissionClassification` to list current admissions. -/
#guard_msgs (whitespace := lax) in
internal def h : J a := sorry

end JudgmentAdmissionClassification

#guard_structural_model_field_count JudgmentAdmissionClassification 4
#guard_structural_no_model_field_for JudgmentAdmissionClassification h

/-- warning: type theory 'JudgmentAdmissionClassification' has 1 admitted internal declaration(s):
admitted internal theorem JudgmentAdmissionClassification.h : J a [missing doc] -/
#guard_msgs (whitespace := lax) in
#lint_type_theory_sorries JudgmentAdmissionClassification

declare_type_theory BadStructuralJudgmentAdmission where
  syntax_sort Obj : Type
  lf_opaque a : Obj
  judgment J (x : Obj)

/-- error: failed to classify admitted internal LF declaration
'BadStructuralJudgmentAdmission.bad' in type theory 'BadStructuralJudgmentAdmission': admitted
internal declaration 'bad' in type theory 'BadStructuralJudgmentAdmission' has annotation headed by
judgment 'J', expected an LF type expression

Accepted forms are object-shaped admissions such as `internal def c : Obj := sorry` and
theorem-shaped admissions such as `internal theorem h : J a := sorry`. -/
#guard_msgs (whitespace := lax) in
internal def BadStructuralJudgmentAdmission.bad : Σ x : Obj, J x := sorry

declare_type_theory BadUnknownStructuralAdmission where
  syntax_sort Obj : Type

/-- error: failed to classify admitted internal LF declaration
'BadUnknownStructuralAdmission.bad' in type theory 'BadUnknownStructuralAdmission': unknown
identifier 'Missing' in annotation of admitted internal declaration 'bad' in type theory
'BadUnknownStructuralAdmission'

Accepted forms are object-shaped admissions such as `internal def c : Obj := sorry` and
theorem-shaped admissions such as `internal theorem h : J a := sorry`. -/
#guard_msgs (whitespace := lax) in
internal def BadUnknownStructuralAdmission.bad : Σ x : Obj, Missing x := sorry

declare_type_theory BadSigmaDependencyAdmission where
  syntax_sort Obj : Type
  syntax_sort Fam (x : Obj) : Type

/-- error: failed to classify admitted internal LF declaration 'BadSigmaDependencyAdmission.bad' in
type theory 'BadSigmaDependencyAdmission': unknown identifier 'y' in annotation of admitted
internal declaration 'bad' in type theory 'BadSigmaDependencyAdmission'

Accepted forms are object-shaped admissions such as `internal def c : Obj := sorry` and
theorem-shaped admissions such as `internal theorem h : J a := sorry`. -/
#guard_msgs (whitespace := lax) in
internal def BadSigmaDependencyAdmission.bad : Σ x : Obj, Fam y := sorry

declare_type_theory BadStructuralShadowAdmission where
  syntax_sort Obj : Type

/-- error: failed to classify admitted internal LF declaration 'BadStructuralShadowAdmission.bad'
in type theory 'BadStructuralShadowAdmission': duplicate LF binder 'x' in annotation of admitted
internal declaration 'bad' in type theory 'BadStructuralShadowAdmission'

Accepted forms are object-shaped admissions such as `internal def c : Obj := sorry` and
theorem-shaped admissions such as `internal theorem h : J a := sorry`. -/
#guard_msgs (whitespace := lax) in
internal def BadStructuralShadowAdmission.bad : Σ x : Obj, Σ x : Obj, Obj := sorry

declare_type_theory BadStructuralUniverseAdmission where
  syntax_sort Obj : Type

/-- error: failed to classify admitted internal LF declaration 'BadStructuralUniverseAdmission.bad'
in type theory 'BadStructuralUniverseAdmission': admitted internal declaration 'bad' in type theory
'BadStructuralUniverseAdmission' uses undeclared universe level parameter 'u' in annotation;
declare it in the theory-level parameter list containing 'u' or use a numeric level. Currently
declared level parameter(s): none

Accepted forms are object-shaped admissions such as `internal def c : Obj := sorry` and
theorem-shaped admissions such as `internal theorem h : J a := sorry`. -/
#guard_msgs (whitespace := lax) in
internal def BadStructuralUniverseAdmission.bad : Σ x : Type u, Obj := sorry
