/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Conversion-profile diagnostics

Smoke tests for lightweight diagnostics added around LF/object conversion fallback paths.
-/

@[expose] public section

open InternalLean

#guard
  let sig : HLSignature := { name := `ArrowFunConversionProfileSmoke }
  let arrow := ObjExpr.arrow none (.ident `Obj) (.ident `Obj)
  let funArrow := ObjExpr.funArrow none (.ident `Obj) (.ident `Obj)
  match checkObjectGoalConversion sig #[] #[] arrow funArrow with
  | .ok _ => true
  | .error _ => false

/-- A compact large expression used to guard bounded diagnostic rendering. -/
def diagnosticAppTower : Nat → ObjExpr
  | 0 => .ident `x
  | n + 1 => .app (.ident `f) (diagnosticAppTower n)

#guard objExprNodeCount (diagnosticAppTower 80) > diagnosticObjExprFullRenderNodeLimit

#guard
  (diagnosticObjExprString (diagnosticAppTower 80)).toList.length <
    (toString (diagnosticAppTower 80)).toList.length

declare_type_theory LFConversionProfileSmoke where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque simplexPayload : Shape emptyCtx
  lf_def Alias : Shape emptyCtx := simplexPayload
  lf_def idShape : Shape emptyCtx ⇒ Shape emptyCtx := fun S => S
  lf_def Big : Shape emptyCtx := idShape (idShape (idShape Alias))
  rule simplex_refl_rule (S : Shape emptyCtx) where
    conclusion : shapeIncl emptyCtx S S
  judgment_theorem alias_payload : shapeIncl emptyCtx simplexPayload simplexPayload :=
    simplex_refl_rule Alias
  judgment_theorem big_refl : shapeIncl emptyCtx Big Big := simplex_refl_rule Big

internal theorem LFConversionProfileSmoke.big_exact : shapeIncl emptyCtx Big Big := by
  exact big_refl

internal theorem LFConversionProfileSmoke.big_apply : shapeIncl emptyCtx Big Big := by
  apply simplex_refl_rule

internal theorem LFConversionProfileSmoke.big_change : shapeIncl emptyCtx Big Big := by
  change shapeIncl emptyCtx Big Big
  exact big_refl

/--
info: LF conversion profile site=object_goal_conversion, theory=LFConversionProfileSmoke,
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=-,
compact=true, fallback=false, accepted=true, unfolded=none
-/
#guard_msgs (whitespace := lax) in
#print_internal_object_conversion_profile LFConversionProfileSmoke
  (shapeIncl emptyCtx Big Big) (shapeIncl emptyCtx Big Big)

/--
info: LF conversion profile site=object_goal_conversion, theory=LFConversionProfileSmoke,
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=-,
compact=false, fallback=true, accepted=true, unfolded=Alias:2
-/
#guard_msgs (whitespace := lax) in
#print_internal_object_conversion_profile LFConversionProfileSmoke
  (shapeIncl emptyCtx Alias Alias) (shapeIncl emptyCtx simplexPayload simplexPayload)

/--
info: LF conversion profile site=candidate_match, theory=LFConversionProfileSmoke,
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=-,
compact=true, fallback=false, accepted=true, unfolded=none
-/
#guard_msgs (whitespace := lax) in
#print_internal_candidate_match_profile LFConversionProfileSmoke
  (shapeIncl emptyCtx Big Big) (shapeIncl emptyCtx Big Big)

/--
info: LF conversion profile site=candidate_match, theory=LFConversionProfileSmoke,
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=-,
compact=false, fallback=true, accepted=true, unfolded=Alias:2
-/
#guard_msgs (whitespace := lax) in
#print_internal_candidate_match_profile LFConversionProfileSmoke
  (shapeIncl emptyCtx Alias Alias) (shapeIncl emptyCtx simplexPayload simplexPayload)
