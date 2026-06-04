/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Syntax definition tests

These regressions cover checked and admitted `syntax_def` declarations. A `syntax_def` is a
named derived syntax family, not primitive model data; admitted bodies remain lint-visible debt
without becoming user-provided model fields.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

/-- Assert the number of renderable user-provided model fields. -/
elab "#guard_syntax_def_model_field_count " theory:ident expected:num : command => do
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

/-- Assert that a source declaration is not requested as a user-provided model field. -/
elab "#guard_syntax_def_no_model_field_for " theory:ident decl:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let obs ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  let declName := decl.getId.eraseMacroScopes
  if obs.any (fun o =>
      o.name.eraseMacroScopes == declName && o.generatedRole == .field && o.renderable) then
    throwError "expected '{decl.getId}' not to be a user model field for '{theory.getId}'"

/-- Assert the number of admitted syntax-definition records for a theory. -/
elab "#guard_syntax_def_admission_count " theory:ident expected:num : command => do
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let count := admissions.foldl (init := 0) fun n a => if a.kind == .syntaxDef then n + 1 else n
  unless count == expected.getNat do
    throwError "expected {expected.getNat} admitted syntax_def(s) for '{theory.getId}', found \
      {count}"

declare_type_theory SyntaxDefModelSmoke{u} where
  syntax_sort Obj : Type u
  syntax_def P (x : Obj) : Type u := sorry
  lf_opaque useP (x : Obj) (p : P x) : Obj

#check_type_theory SyntaxDefModelSmoke
#guard_syntax_def_admission_count SyntaxDefModelSmoke 1
#check_model_obligations SyntaxDefModelSmoke
#guard_syntax_def_model_field_count SyntaxDefModelSmoke 2
#guard_syntax_def_no_model_field_for SyntaxDefModelSmoke P

generate_model_interface SyntaxDefModelSmoke as SyntaxDefModelSmokeModel

/-- Checked syntax definitions unfold during model rendering and add no admission debt. -/
declare_type_theory SyntaxDefCheckedSmoke{u} where
  syntax_sort Obj : Type u
  syntax_def Pack (x : Obj) : Type u := Σ y : Obj, Obj
  lf_opaque usePack (x : Obj) (p : Pack x) : Obj

#guard_syntax_def_admission_count SyntaxDefCheckedSmoke 0
#check_model_obligations SyntaxDefCheckedSmoke
#guard_syntax_def_model_field_count SyntaxDefCheckedSmoke 2
#guard_syntax_def_no_model_field_for SyntaxDefCheckedSmoke Pack

generate_model_interface SyntaxDefCheckedSmoke as SyntaxDefCheckedSmokeModel

/-- `syntax_sort_role` may tag a derived syntax family, but zones still require primitive sorts. -/
declare_type_theory SyntaxDefRoleSmoke{u} where
  syntax_sort Obj : Type u
  syntax_def P (x : Obj) : Type u := sorry
  syntax_sort_role P : side_structure

#check_type_theory SyntaxDefRoleSmoke

/-- Later checked syntax definitions may refer to earlier admitted syntax definitions. -/
declare_type_theory SyntaxDefEarlierAdmission{u} where
  syntax_sort Obj : Type u
  syntax_def P (x : Obj) : Type u := sorry
  syntax_def Q (x : Obj) : Type u := P x

#check_type_theory SyntaxDefEarlierAdmission
#guard_syntax_def_admission_count SyntaxDefEarlierAdmission 1

/-- Extension blocks can add and later use admitted syntax definitions. -/
declare_type_theory SyntaxDefExtensionSmoke{u} where
  syntax_sort Obj : Type u

extend_type_theory SyntaxDefExtensionSmoke where
  syntax_def P (x : Obj) : Type u := sorry

extend_type_theory SyntaxDefExtensionSmoke where
  lf_opaque useP (x : Obj) (p : P x) : Obj

#check_model_obligations SyntaxDefExtensionSmoke
#guard_syntax_def_no_model_field_for SyntaxDefExtensionSmoke P

/-- Parents expose checked and admitted syntax definitions to children. -/
declare_type_theory SyntaxDefParentSmoke{u} where
  syntax_sort Obj : Type u
  syntax_def P (x : Obj) : Type u := sorry

declare_type_theory SyntaxDefChildSmoke extends SyntaxDefParentSmoke where
  lf_opaque useP (x : Obj) (p : P x) : Obj

#check_model_obligations SyntaxDefChildSmoke
#guard_syntax_def_admission_count SyntaxDefChildSmoke 1
#guard_syntax_def_no_model_field_for SyntaxDefChildSmoke P

/-- Cached internal-definition registration preserves implicit syntax-definition telescopes. -/
declare_type_theory SyntaxDefCachedImplicitSmoke where
  syntax_sort Obj
  syntax_sort El (A : Obj)
  lf_opaque A : Obj
  lf_opaque a : El A
  syntax_def P {A : Obj} (x : El A) : Type := Obj

namespace SyntaxDefCachedImplicitSmoke

internal def d : P a := A

#check d

end SyntaxDefCachedImplicitSmoke

/-- Lint dependency smoke. -/
declare_type_theory SyntaxDefLintDependencySmoke{u} where
  /-- Object sort. -/
  syntax_sort Obj : Type u
  /-- A point. -/
  lf_opaque a : Obj
  /-- Derived predicate. -/
  syntax_def P (x : Obj) : Type u := sorry
  /-- Constructor. -/
  lf_opaque p (x : Obj) : P x
  /-- Definition mentioning P. -/
  lf_def d : P a := p a

/--
warning: type theory 'SyntaxDefLintDependencySmoke' has 1 admitted internal declaration(s):
admitted syntax_def SyntaxDefLintDependencySmoke.P (x : Obj) : Type u [documented]
downstream declarations mentioning admissions:
internal def d depends on admitted P
-/
#guard_msgs (whitespace := lax) in
#lint_type_theory_sorries SyntaxDefLintDependencySmoke

/--
error: syntax_def 'Bad' in type theory 'BadSyntaxDefJudgmentRhs' has value headed by judgment
'J', expected an LF type expression
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxDefJudgmentRhs where
  syntax_sort Obj : Type
  lf_opaque a : Obj
  judgment J (x : Obj)
  syntax_def Bad : Type := J a

/--
error: syntax_def 'Bad' result annotation must be an object universe (`Type`, `Type u`,
`Type (u+1)`, ...)
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxDefResultAnnotation where
  syntax_sort Obj : Type
  syntax_def Bad : Obj := Obj

/--
error: syntax_def 'Bad' in type theory 'BadSyntaxDefUniverseMismatch' has value in universe
'Type 1', expected 'Type'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxDefUniverseMismatch where
  syntax_def Bad : Type := Type

/--
error: syntax_def 'P' in type theory 'BadSyntaxDefSelfRecursion' references syntax_def 'P'
before it is available in value
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxDefSelfRecursion where
  syntax_sort Obj : Type
  syntax_def P (x : Obj) : Type := P x

/--
error: syntax_def 'P' in type theory 'BadSyntaxDefMutualRecursion' references syntax_def 'Q'
before it is available in value
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxDefMutualRecursion where
  syntax_sort Obj : Type
  syntax_def P (x : Obj) : Type := Q x
  syntax_def Q (x : Obj) : Type := P x

/--
error: syntax_def 'P' in type theory 'BadSyntaxDefParamForwardRef' references syntax_def 'Q'
before it is available in parameter 'x' type
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxDefParamForwardRef where
  syntax_def P (x : Q) : Type := sorry
  syntax_def Q : Type := sorry

/--
error: context_zone 'z' in type theory 'BadSyntaxDefContextZone' uses unknown syntax sort 'P'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxDefContextZone where
  syntax_sort Obj : Type
  syntax_def P (x : Obj) : Type := sorry
  context_zone z : P
