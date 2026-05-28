/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Pi-shaped syntax abbreviation tests

These regressions cover dependent-function-shaped `syntax_abbrev` values and checked projection
patterns that should not become user model fields.
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

/--
error: syntax_abbrev 'Bad' in type theory 'BadSyntaxAbbrevValueTest' has value whose type
cannot be inferred: 'raw', expected an LF type expression
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxAbbrevValueTest where
  lf_opaque raw / 0
  syntax_abbrev Bad := raw
