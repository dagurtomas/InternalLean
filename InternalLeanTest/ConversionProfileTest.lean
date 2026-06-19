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

/-- Tiny definition map used to guard AR5 fallback-start rendering. -/
def ar5FallbackSummaryDefs : LFDefinitionValueMap :=
  ({} : LFDefinitionValueMap).insert `Alias (.ident `payload)

#guard renderLFConversionDefinitionSummary ar5FallbackSummaryDefs == "defs=Alias, def_count=1"

run_cmd do
  let defs : LFDefinitionValueMap := ({} : LFDefinitionValueMap).insert `d (.ident `body)
  let A : ObjExpr := .ident `A
  let B : ObjExpr := .ident `B
  let actual : ObjExpr := .app (.ident `d) (.arrow (some `x) A B)
  let expected : ObjExpr := .app (.ident `d) (.funArrow (some `x) A B)
  let accepted := lfDefinitionComparisonAccepted defs {} actual expected
  let entry ← Lean.Elab.Command.liftCoreM <|
    lfDefinitionComparisonProfileEntryWithOptionsLogged "logged_same_head"
      { theoryName := some `LR1LoggedComparisonSmoke } defs {} actual expected {}
  unless accepted do
    throwError "non-logged acceptedness did not exercise LR1 same-head fast path"
  unless entry.accepted do
    throwError "logged profile path rejected a same-head fast-path comparison"
  unless entry.compactSucceeded do
    throwError "logged profile path accepted but did not mark compact"

#guard
  (renderLFConversionProfileEntry {
    site := "definition_full_fallback_start"
    owner := { theoryName := some `LFConversionProfileSmoke }
    actualHead? := some `Alias
    expectedHead? := some `payload
    actualSize := 1
    expectedSize := 1
    compactSucceeded := false
    fullUnfoldFallback := true
    accepted := false
    fallbackDefinitionSummary? := some "env=restricted, defs=Alias, def_count=1" }).contains
      "fallback_defs=env=restricted, defs=Alias, def_count=1"

#guard
  (renderLFConversionProgressEntry {
    site := "object_goal_full_fallback_start"
    owner := {
      theoryName := some `LFConversionProfileSmoke
      ownerKind := some "internal"
      ownerName := some `diag }
    targetHead? := some `shapeIncl
    targetSize := 7
    message := "site=native_change_conversion, actual_head=shapeIncl, actual_size=7, \
      expected_head=shapeIncl, expected_size=7, fallback_defs=defs=Alias, def_count=1" }).contains
        "owner=internal:diag"

#guard
  let forced := ({} : Lean.NameMap Nat).insert `Compact 3
  let result : LFDeltaConversionResult := {
    stats := { deltaSteps := 3, pairVisits := 5, forcedByName := forced }
    fuelExhausted? := some "delta" }
  let summary := objectGoalDeltaFailureSummary result
  summary.contains "forced=Compact:3" && summary.contains "fuel_exhausted=delta"

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
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=0ms,
compact=true, fallback=false, accepted=true, unfolded=none
-/
#guard_msgs (whitespace := lax) in
#print_internal_object_conversion_profile LFConversionProfileSmoke
  (shapeIncl emptyCtx Big Big) (shapeIncl emptyCtx Big Big)

/--
info: LF conversion profile site=object_goal_conversion, theory=LFConversionProfileSmoke,
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=0ms,
compact=false, fallback=true, accepted=true, unfolded=Alias:2
-/
#guard_msgs (whitespace := lax) in
#print_internal_object_conversion_profile LFConversionProfileSmoke
  (shapeIncl emptyCtx Alias Alias) (shapeIncl emptyCtx simplexPayload simplexPayload)

/--
info: LF conversion profile site=candidate_match, theory=LFConversionProfileSmoke,
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=0ms,
compact=true, fallback=false, accepted=true, unfolded=none
-/
#guard_msgs (whitespace := lax) in
#print_internal_candidate_match_profile LFConversionProfileSmoke
  (shapeIncl emptyCtx Big Big) (shapeIncl emptyCtx Big Big)

/--
info: LF conversion profile site=candidate_match, theory=LFConversionProfileSmoke,
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=0ms,
compact=false, fallback=true, accepted=true, unfolded=Alias:2
-/
#guard_msgs (whitespace := lax) in
#print_internal_candidate_match_profile LFConversionProfileSmoke
  (shapeIncl emptyCtx Alias Alias) (shapeIncl emptyCtx simplexPayload simplexPayload)
