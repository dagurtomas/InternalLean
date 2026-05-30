/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Judgment abbreviation tests

These regressions cover public judgment-shaped abbreviations. They should expand before LF
checking, theorem replay, and model-obligation generation, without becoming independent model
fields.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

/-- Assert that a checked declaration is not requested as a user-provided model field. -/
elab "#guard_judgment_abbrev_no_model_field_for " theory:ident decl:ident : command => do
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
elab "#guard_judgment_abbrev_model_field_count " theory:ident expected:num : command => do
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

declare_type_theory JudgmentAbbrevTest where
  syntax_sort Obj : Type
  lf_opaque a : Obj
  judgment J (x : Obj)
  judgment K (x : Obj)
  judgment_abbrev Alias (x : Obj) := J x
  judgment_abbrev Alias2 (x : Obj) := Alias x
  rule j_intro : Alias a
  rule k_from_alias (x : Obj) where
    premise h : Alias2 x
    conclusion : K x
  judgment_theorem a_ok : Alias2 a := j_intro

#check_type_theory JudgmentAbbrevTest
#check_model_obligations JudgmentAbbrevTest
#guard_judgment_abbrev_model_field_count JudgmentAbbrevTest 6
#guard_judgment_abbrev_no_model_field_for JudgmentAbbrevTest Alias
#guard_judgment_abbrev_no_model_field_for JudgmentAbbrevTest Alias2

generate_model_interface JudgmentAbbrevTest as JudgmentAbbrevModel
#check JudgmentAbbrevTest.JudgmentAbbrevModel.j_intro
#check JudgmentAbbrevTest.JudgmentAbbrevModel.k_from_alias

def judgmentAbbrevModel : JudgmentAbbrevTest.JudgmentAbbrevModel where
  Obj := Unit
  a := ()
  J := fun _ => Unit
  K := fun _ => Unit
  j_intro := ()
  k_from_alias := fun _ _ => ()

declare_type_theory JudgmentAbbrevIncrementalTest where
  syntax_sort Obj : Type
  lf_opaque a : Obj
  judgment J (x : Obj)

extend_type_theory JudgmentAbbrevIncrementalTest where
  judgment_abbrev Alias (x : Obj) := J x
  rule intro : Alias a
  judgment_theorem ok : Alias a := intro

#check_type_theory JudgmentAbbrevIncrementalTest
#check_model_obligations JudgmentAbbrevIncrementalTest
#guard_judgment_abbrev_no_model_field_for JudgmentAbbrevIncrementalTest Alias

declare_type_theory JudgmentAbbrevImplicitTest where
  syntax_sort Obj : Type
  syntax_sort El (A : Obj) : Type
  lf_opaque A : Obj
  lf_opaque a : El A
  judgment Has {A : Obj} (x : El A)
  judgment_abbrev HasAlias {A : Obj} (x : El A) := Has x
  rule intro : HasAlias a

#check_type_theory JudgmentAbbrevImplicitTest
#check_model_obligations JudgmentAbbrevImplicitTest
#guard_judgment_abbrev_no_model_field_for JudgmentAbbrevImplicitTest HasAlias

/--
error: judgment_abbrev 'Bad' in type theory 'BadJudgmentAbbrevValueTest' has value headed by
syntax_sort 'Obj', expected a judgment-headed expression
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadJudgmentAbbrevValueTest where
  syntax_sort Obj : Type
  judgment J (x : Obj)
  judgment_abbrev Bad := Obj

/--
error: syntax_abbrev 'Bad' in type theory 'BadSyntaxJudgmentAbbrevTest' has value headed by
judgment 'J', expected an LF type expression
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxJudgmentAbbrevTest where
  syntax_sort Obj : Type
  lf_opaque a : Obj
  judgment J (x : Obj)
  syntax_abbrev Bad := J a

/--
error: rule 'bad' omits explicit argument 'x' in application 'Alias' in conclusion
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadJudgmentAbbrevArityTest where
  syntax_sort Obj : Type
  judgment J (x : Obj)
  judgment_abbrev Alias (x : Obj) := J x
  rule bad : Alias

/--
error: cyclic or too-deep LF abbreviation expansion in value of judgment_abbrev 'Loop' in type
 theory 'BadJudgmentAbbrevCycleTest'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadJudgmentAbbrevCycleTest where
  judgment J
  judgment_abbrev Loop := Loop
  rule bad : Loop
