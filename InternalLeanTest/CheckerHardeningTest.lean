/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Checker hardening regression tests

These tests cover LF metadata that previously passed direct checking and failed only during model
generation or low-level replay.
-/

@[expose] public section

open InternalLean

/--
error: rule 'bad' in type theory 'NonInferableArgRuleReject' has conclusion for judgment 'J'
argument 'Ctx ⇒ Ctx' whose type cannot be inferred: 'Ctx ⇒ Ctx', expected 'Ctx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory NonInferableArgRuleReject where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  judgment J (Γ : Ctx) (A : Ty Γ)
  lf_opaque mkTy (Γ : Ctx) : Ty Γ
  rule bad : J (Ctx ⇒ Ctx) (mkTy (Ctx ⇒ Ctx))

/--
error: lf_def 'bad' in type theory 'NonInferableArgDefReject' has type for syntax_sort 'Ty'
argument 'Type' whose type cannot be inferred: 'Type', expected 'Ctx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory NonInferableArgDefReject where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  lf_opaque mkTy (Γ : Ctx) : Ty Γ
  lf_def bad : Ty Type := mkTy Type

/--
error: syntax_sort 'Bad' in type theory 'BadBinderHeadReject' has parameter 'x' type whose type
cannot be inferred: 'bogus', expected an LF type expression
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadBinderHeadReject where
  syntax_sort A
  lf_opaque bogus
  syntax_sort Bad (x : bogus)

/--
error: rule 'bad' in type theory 'BadRuleParamHeadReject' has parameter 'x' type whose type cannot
be inferred: 'bogus', expected an LF type expression
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleParamHeadReject where
  syntax_sort A
  judgment J
  lf_opaque bogus
  rule bad (x : bogus) : J

/-- Valid universe-indexed metadata remains accepted. -/
declare_type_theory UniverseBinderHardeningSmoke {u} where
  syntax_sort Obj (A : Type u)
  judgment Has (A : Type u) (x : Obj A)
  lf_opaque id {A : Type u} (x : Obj A) : Obj A
  rule has_id {A : Type u} (x : Obj A) : Has A (id x)

#check_type_theory UniverseBinderHardeningSmoke

/-- Alpha-equivalent direct LF-definition alias types should compare equal. -/
declare_type_theory AliasAlphaSmoke where
  syntax_sort Obj
  syntax_sort Fam (f : Obj → Obj)
  lf_opaque idFam : Fam (fun x => x)
  lf_def d : Fam (fun x => x) := idFam
  lf_def alias : Fam (fun y => y) := d

#check_type_theory AliasAlphaSmoke
