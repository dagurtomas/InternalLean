/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Soundness regression tests

These tests cover checker and replay invariants at the LF trust boundary.
-/

@[expose] public section

declare_type_theory DependentLambdaSmoke where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  lf_opaque empty : Ctx
  lf_opaque other : Ctx
  lf_opaque mkTy (Γ : Ctx) : Ty Γ

namespace DependentLambdaSmoke

internal def good (Γ : Ctx) : Ty Γ := mkTy Γ

/-- error: failed to check binder-style internal LF declaration 'DependentLambdaSmoke.bad' in type
 theory 'DependentLambdaSmoke'

LF judgment theorem path:
rule 'bad' in type theory 'DependentLambdaSmoke' has statement headed by unknown judgment 'Ty'

LF object definition path:
lf_def 'bad' in type theory 'DependentLambdaSmoke' has value with type 'Ty other', expected
'Ty Γ' -/
#guard_msgs (whitespace := lax) in
internal def bad (Γ : Ctx) : Ty Γ := mkTy other

end DependentLambdaSmoke

declare_type_theory DependentFunctionTransportSmoke where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  lf_opaque mkTy (Γ : Ctx) : Ty Γ
  lf_def GoodTy : ((Γ : Ctx) ⇒ Ty Γ) := fun Γ => mkTy Γ

generate_model_interface DependentFunctionTransportSmoke as DependentFunctionTransportModel
generate_lf_model_transports DependentFunctionTransportSmoke only GoodTy for
  DependentFunctionTransportModel
#check DependentFunctionTransportSmoke.DependentFunctionTransportModel.GoodTy

/--
error: lf_def 'bad' in type theory 'LambdaArityMismatchReject' has value as lambda expression
'fun extra => mkTy Γ', expected non-function type 'Ty Γ'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory LambdaArityMismatchReject where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  lf_opaque mkTy (Γ : Ctx) : Ty Γ
  lf_def bad : ((Γ : Ctx) ⇒ Ty Γ) := fun Γ extra => mkTy Γ

/--
error: lf_def 'bad' in type theory 'NonInferableReject' has value whose type cannot be inferred:
'Type', expected 'Obj'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory NonInferableReject where
  syntax_sort Obj
  lf_def bad : Obj := Type

/--
error: lf_def 'bad' in type theory 'LFDefinitionAliasReject' has value with type 'Ty other',
expected 'Ty empty'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory LFDefinitionAliasReject where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  lf_opaque empty : Ctx
  lf_opaque other : Ctx
  lf_opaque mkTy (Γ : Ctx) : Ty Γ
  lf_def Alias : Ctx := empty
  lf_def bad : Ty Alias := mkTy other

/--
error: rule 'bad' in type theory 'LFRuleAliasReject' has conclusion for judgment 'HasTy' argument
'mkTy other' with type 'Ty other', expected 'Ty empty'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory LFRuleAliasReject where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  judgment HasTy (Γ : Ctx) (A : Ty Γ)
  lf_opaque empty : Ctx
  lf_opaque other : Ctx
  lf_opaque mkTy (Γ : Ctx) : Ty Γ
  lf_def Alias : Ctx := empty
  rule bad where
    conclusion : HasTy Alias (mkTy other)

/--
error: judgment_theorem 'bad' in type theory 'CaptureBetaReject' applies rule 'refl_rhs' but its
statement is 'EqFun (fun x => fun y => x y) (fun y => y)', expected rule conclusion
'EqFun (fun y => y) (fun y => y)'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory CaptureBetaReject where
  syntax_sort Obj
  judgment EqFun (f : Obj → Obj) (g : Obj → Obj)
  lf_opaque y : Obj
  rule refl_rhs where
    conclusion : EqFun (fun y => y) (fun y => y)
  judgment_theorem bad : EqFun ((fun x => fun y => x) y) (fun y => y) := refl_rhs

/--
error: duplicate lambda binder 'x' in conclusion of rule 'bad' in type theory
'BinderShadowReject'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BinderShadowReject where
  syntax_sort Obj
  judgment EqFun (f : Obj → Obj) (g : Obj → Obj)
  rule bad where
    conclusion : EqFun (fun x x => x) (fun x => x)

/--
error: judgment_theorem 'bad' in type theory 'LFDefinitionCaptureUnfoldReject' applies rule
'refl_rhs' but the statement does not match the rule conclusion after LF-definition normalization:
LF-definition normalization could not match expressions.
actual: EqFun (fun y => Alias) (fun y => y)
expected: EqFun (fun y => y) (fun y => y)
normalized actual: EqFun (fun y._hyg0 => y) (fun y._hyg0 => y._hyg0)
normalized expected: EqFun (fun y._hyg0 => y._hyg0) (fun y._hyg0 => y._hyg0)
LF definitions mentioned before unfolding: Alias
LF definitions unfolded: Alias
Normalization policy: LF matching unfolds earlier checked `lf_def` values, beta-reduces
explicit LF lambdas, and alpha-renames binders to avoid local-binder capture.
-/
#guard_msgs (whitespace := lax) in
declare_type_theory LFDefinitionCaptureUnfoldReject where
  syntax_sort Obj
  judgment EqFun (f : Obj → Obj) (g : Obj → Obj)
  lf_opaque y : Obj
  lf_def Alias : Obj := y
  rule refl_rhs where
    conclusion : EqFun (fun y => y) (fun y => y)
  judgment_theorem bad : EqFun (fun y => Alias) (fun y => y) := refl_rhs

declare_type_theory AlphaEquivalenceTransportSmoke where
  syntax_sort Obj
  judgment EqFun (f : Obj → Obj) (g : Obj → Obj)
  lf_opaque idObj (x : Obj) : Obj
  rule intro where
    conclusion : EqFun (fun x => idObj x) (fun x => idObj x)
  judgment_theorem ok : EqFun (fun y => idObj y) (fun z => idObj z) := intro

generate_model_interface AlphaEquivalenceTransportSmoke as AlphaEquivalenceTransportModel
generate_lf_model_transports AlphaEquivalenceTransportSmoke only ok for
  AlphaEquivalenceTransportModel
#check AlphaEquivalenceTransportSmoke.AlphaEquivalenceTransportModel.ok

declare_type_theory LFDefinitionCaptureUnfoldAlphaSmoke where
  syntax_sort Obj
  judgment EqFun (f : Obj → Obj) (g : Obj → Obj)
  lf_opaque y : Obj
  lf_def Alias : Obj := y
  rule intro where
    conclusion : EqFun (fun y => Alias) (fun z => Alias)
  judgment_theorem ok : EqFun (fun a => y) (fun b => y) := intro

/--
error: judgment_theorem 'bad' in type theory 'LFParameterSubstitutionCaptureReject' applies rule
'bad_rule' but its statement is 'EqFun (fun y => y) (fun y => y)', expected rule conclusion
'EqFun (fun y._hyg0 => y) (fun y => y)'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory LFParameterSubstitutionCaptureReject where
  syntax_sort Obj
  judgment EqFun (f : Obj → Obj) (g : Obj → Obj)
  lf_opaque y : Obj
  rule bad_rule (x : Obj) where
    conclusion : EqFun (fun y => x) (fun y => y)
  judgment_theorem bad : EqFun (fun y => y) (fun y => y) := bad_rule y

declare_type_theory ReplaySummarySmoke where
  syntax_sort Obj
  judgment J
  rule intro where
    conclusion : J
  judgment_theorem ok : J := intro

/-- info: LF replay trust summary for ReplaySummarySmoke: 1/1 theorem replay artifact(s) checked
missing replay artifacts: none
validation failures: none
local assumptions: none
theorem references: none
certificate obligations: none
external certificates: none
rule applications: intro
opaque LF heads: none
all global LF heads: none -/
#guard_msgs (whitespace := lax) in
#print_lf_replay_trust_summary ReplaySummarySmoke

/-- info: type theory 'ReplaySummarySmoke' has no admitted internal declarations -/
#guard_msgs (whitespace := lax) in
#lint_type_theory_sorries ReplaySummarySmoke

/-- error: judgment_theorem 'bad' in type theory 'OpaqueProofReject' has unchecked proof 'bogus';
expected a local theorem assumption, checked judgment theorem, or LF rule application -/
#guard_msgs (whitespace := lax) in
declare_type_theory OpaqueProofReject where
  syntax_sort Obj
  judgment J
  lf_opaque bogus
  judgment_theorem bad : J := bogus

/-- error: judgment_theorem 'bad' in type theory 'TypedObjectProofReject' has unchecked proof 'x';
expected a local theorem assumption, checked judgment theorem, or LF rule application -/
#guard_msgs (whitespace := lax) in
declare_type_theory TypedObjectProofReject where
  syntax_sort Obj
  judgment J
  lf_opaque x : Obj
  judgment_theorem bad : J := x

