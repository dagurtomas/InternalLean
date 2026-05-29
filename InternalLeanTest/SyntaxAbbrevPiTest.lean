/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Pi- and Sigma-shaped syntax abbreviation tests

These regressions cover dependent-function-shaped and record/Sigma-shaped `syntax_abbrev` values
and checked projection patterns that should not become user model fields.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

/-- Assert that a checked declaration is not requested as a user-provided model field. -/
elab "#guard_no_model_field_for " theory:ident decl:ident : command => do
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
elab "#guard_model_field_count " theory:ident expected:num : command => do
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

declare_type_theory PiAbbrevTest where
  syntax_sort Obj : Type
  syntax_sort Fam (x : Obj) : Type
  syntax_abbrev Witness := (x : Obj) → Fam x
  lf_opaque base : Obj
  lf_opaque mkFam (x : Obj) : Fam x
  lf_def witness : Witness := fun x => mkFam x
  lf_def project : Witness ⇒ Fam base := fun w => w base

#check_model_obligations PiAbbrevTest
#guard_model_field_count PiAbbrevTest 4
#guard_no_model_field_for PiAbbrevTest witness
#guard_no_model_field_for PiAbbrevTest project

declare_type_theory WitnessProjectionTest where
  syntax_sort Cat : Type
  syntax_sort Obj (C : Cat) : Type
  syntax_sort Equiv (C : Cat) (D : Cat) : Type
  lf_opaque Hom (C : Cat) (x : Obj C) (y : Obj C) : Cat
  lf_opaque Terminal : Cat
  syntax_abbrev InitialWitness (C : Cat) (x : Obj C) :=
    (y : Obj C) → Equiv (Hom C x y) Terminal
  lf_def initialHomContractible :
      (C : Cat) ⇒ (x : Obj C) ⇒ InitialWitness C x ⇒
      (y : Obj C) ⇒ Equiv (Hom C x y) Terminal :=
    fun C x h y => h y

#check_model_obligations WitnessProjectionTest
#guard_model_field_count WitnessProjectionTest 5
#guard_no_model_field_for WitnessProjectionTest initialHomContractible

declare_type_theory SigmaAbbrevTest where
  syntax_sort Obj : Type
  syntax_sort Fam (x : Obj) : Type
  syntax_abbrev Witness := Σ x : Obj, Fam x
  syntax_abbrev ObjPair := Obj × Obj
  lf_opaque base : Obj
  lf_opaque mkFam (x : Obj) : Fam x
  lf_opaque takeWitness (w : Witness) : Obj
  lf_def witness : Witness := ⟨base, mkFam base⟩
  lf_def projectObj : Witness ⇒ Obj := fun w => fst w
  lf_def projectFam : (w : Witness) ⇒ Fam (fst w) := fun w => snd w
  lf_def basePair : ObjPair := ⟨base, base⟩
  lf_def firstBasePair : ObjPair ⇒ Obj := fun p => fst p

#check_model_obligations SigmaAbbrevTest
#guard_model_field_count SigmaAbbrevTest 5
#guard_no_model_field_for SigmaAbbrevTest witness
#guard_no_model_field_for SigmaAbbrevTest projectObj
#guard_no_model_field_for SigmaAbbrevTest projectFam
#guard_no_model_field_for SigmaAbbrevTest basePair
#guard_no_model_field_for SigmaAbbrevTest firstBasePair

generate_lf_model_structure SigmaAbbrevTest as SigmaAbbrevModel

generate_model_transports SigmaAbbrevTest for SigmaAbbrevModel
#check SigmaAbbrevTest.SigmaAbbrevModel.witness
#check SigmaAbbrevTest.SigmaAbbrevModel.projectObj
#check SigmaAbbrevTest.SigmaAbbrevModel.projectFam
#check SigmaAbbrevTest.SigmaAbbrevModel.basePair
#check SigmaAbbrevTest.SigmaAbbrevModel.firstBasePair

def sigmaAbbrevModel : SigmaAbbrevTest.SigmaAbbrevModel where
  Obj := Unit
  Fam := fun _ => Unit
  base := ()
  mkFam := fun _ => ()
  takeWitness := fun _ => ()

declare_type_theory DependentSigmaDefinitionApplicationTest where
  syntax_sort A : Type
  syntax_sort D : Type
  syntax_sort Hom (X : A) (Y : A) : Type
  lf_opaque obj (C : D) : A
  lf_opaque core (X : A) : A
  lf_opaque incl (X : A) : Hom (core X) X
  syntax_abbrev Sub (X : A) := Σ Y : A, Hom Y X
  syntax_abbrev Coll (C : D) := Sub (obj C)
  lf_def total : (X : A) ⇒ Sub X := fun X => ⟨core X, incl X⟩
  lf_def all : (C : D) ⇒ Coll C := fun C => total (obj C)

generate_model_interface DependentSigmaDefinitionApplicationTest as
  DependentSigmaDefinitionApplicationModel
generate_model_transports DependentSigmaDefinitionApplicationTest for
  DependentSigmaDefinitionApplicationModel
#check DependentSigmaDefinitionApplicationTest.DependentSigmaDefinitionApplicationModel.total
#check DependentSigmaDefinitionApplicationTest.DependentSigmaDefinitionApplicationModel.all

def dependentSigmaDefinitionApplicationModel :
    DependentSigmaDefinitionApplicationTest.DependentSigmaDefinitionApplicationModel where
  A := Unit
  D := Unit
  Hom := fun _ _ => Unit
  obj := fun _ => ()
  core := fun _ => ()
  incl := fun _ => ()

declare_type_theory OpaqueStructuralResultTest where
  syntax_sort Obj : Type
  syntax_sort Fam (x : Obj) : Type
  syntax_abbrev PiWitness := (x : Obj) → Fam x
  syntax_abbrev SigmaWitness := Σ x : Obj, Fam x
  lf_opaque base : Obj
  lf_opaque mkFam (x : Obj) : Fam x
  lf_opaque opaquePi : PiWitness
  lf_opaque opaqueSigma : SigmaWitness
  lf_def sigmaBase : Obj := fst opaqueSigma
  lf_def sigmaFiber : Fam (fst opaqueSigma) := snd opaqueSigma

#check_model_obligations OpaqueStructuralResultTest
#guard_model_field_count OpaqueStructuralResultTest 6
#guard_no_model_field_for OpaqueStructuralResultTest sigmaBase
#guard_no_model_field_for OpaqueStructuralResultTest sigmaFiber

generate_lf_model_structure OpaqueStructuralResultTest as OpaqueStructuralResultModel
generate_model_transports OpaqueStructuralResultTest for OpaqueStructuralResultModel
#check OpaqueStructuralResultTest.OpaqueStructuralResultModel.opaquePi
#check OpaqueStructuralResultTest.OpaqueStructuralResultModel.opaqueSigma
#check OpaqueStructuralResultTest.OpaqueStructuralResultModel.sigmaBase
#check OpaqueStructuralResultTest.OpaqueStructuralResultModel.sigmaFiber

def opaqueStructuralResultModel : OpaqueStructuralResultTest.OpaqueStructuralResultModel where
  Obj := Unit
  Fam := fun _ => Unit
  base := ()
  mkFam := fun _ => ()
  opaquePi := fun _ => ()
  opaqueSigma := ⟨(), ()⟩

declare_type_theory SigmaTheoremReplayTest where
  syntax_sort Obj : Type
  syntax_sort Fam (x : Obj) : Type
  syntax_abbrev Witness := Σ x : Obj, Fam x
  lf_opaque base : Obj
  lf_opaque mkFam (x : Obj) : Fam x
  lf_def witness : Witness := ⟨base, mkFam base⟩
  judgment HasWitness (w : Witness)
  rule witness_ok : HasWitness witness
  judgment_theorem witness_ok_checked : HasWitness witness := witness_ok

#guard_model_field_count SigmaTheoremReplayTest 6
#guard_no_model_field_for SigmaTheoremReplayTest witness
#guard_no_model_field_for SigmaTheoremReplayTest witness_ok_checked

generate_lf_model_structure SigmaTheoremReplayTest as SigmaTheoremReplayModel
generate_model_transports SigmaTheoremReplayTest for SigmaTheoremReplayModel
#check SigmaTheoremReplayTest.SigmaTheoremReplayModel.witness_ok_checked

/--
error: syntax_abbrev 'Bad' in type theory 'BadSigmaAbbrevValueTest' has value whose type cannot
be inferred: 'raw', expected an LF type expression
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSigmaAbbrevValueTest where
  syntax_sort Obj : Type
  lf_opaque raw / 0
  syntax_abbrev Bad := Σ x : Obj, raw

/--
error: lf_def 'bad' in type theory 'BadLFDefRecordTypeTest' has type as term-shaped record
expression '⟨base, base⟩', expected an LF type expression
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFDefRecordTypeTest where
  syntax_sort Obj : Type
  lf_opaque base : Obj
  lf_def bad : ⟨base, base⟩ := base

/--
error: syntax_abbrev 'Bad' in type theory 'BadSyntaxAbbrevValueTest' has value whose type
cannot be inferred: 'raw', expected an LF type expression
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxAbbrevValueTest where
  lf_opaque raw / 0
  syntax_abbrev Bad := raw
