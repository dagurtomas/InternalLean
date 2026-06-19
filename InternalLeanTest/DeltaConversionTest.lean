/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Head-directed delta conversion smoke tests

Focused tests for the option-gated delta-conversion engine and its object-tactic integration.
These tests keep the LF checker as the final acceptance gate.
-/

@[expose] public section

open Lean
open InternalLean

/-- Definition environment for direct delta-conversion smoke tests. -/
def deltaSmokeDefs : LFDefinitionValueMap :=
  ((({} : LFDefinitionValueMap).insert `Alias (.ident `payload)).insert `Id
      (.lam #[`x] (.ident `x))).insert `K (.lam #[`x] (.lam #[`y] (.ident `x)))

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let env : LFDeltaConversionEnv := { defs := deltaSmokeDefs, options }
  let r := LFDeltaConversion.convertObjExpr env (.ident `Alias) (.ident `Alias)
  r.accepted && r.stats.deltaSteps == 0

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let env : LFDeltaConversionEnv := { defs := deltaSmokeDefs, options }
  let r := LFDeltaConversion.convertObjExpr env (.ident `Alias) (.ident `payload)
  r.accepted && r.stats.deltaSteps == 1 &&
    r.stats.forcedByName.find? `Alias == some 1 && r.stats.forcedLhs == 1

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let env : LFDeltaConversionEnv := { defs := deltaSmokeDefs, options }
  let r := LFDeltaConversion.convertObjExpr env (.ident `Alias) (.ident `other)
  !r.accepted && r.stats.deltaSteps == 1 && r.stats.forcedByName.find? `Alias == some 1

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let env : LFDeltaConversionEnv := { defs := deltaSmokeDefs, options }
  let lhs := ObjExpr.pair (.ident `Alias) (.ident `Alias)
  let rhs := ObjExpr.pair (.ident `payload) (.ident `payload)
  let r := LFDeltaConversion.convertObjExpr env lhs rhs
  r.accepted && r.stats.pairCacheHits > 0

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let env : LFDeltaConversionEnv := {
    defs := deltaSmokeDefs
    locals := ({`Alias} : NameSet)
    options }
  let r := LFDeltaConversion.convertObjExpr env (.ident `Alias) (.ident `payload)
  !r.accepted && r.stats.deltaSteps == 0 &&
    r.stats.blockedByLocal.find? `Alias == some 1

/-- Definition environment for AR3 dependency-restriction smoke tests. -/
def ar3DependencyDefs : LFDefinitionValueMap :=
  ((({} : LFDefinitionValueMap).insert `A (.ident `B)).insert `B (.ident `C)).insert `C
    (.ident `payload)

#guard
  let (defs, stats) := restrictLFDefinitionValuesForExprs ar3DependencyDefs {} #[.ident `A]
  defs.size == 3 && stats.rootCount == 1 && stats.reachableDefinitions == 3 &&
    normalizeLFExprForConversionWithLocals defs {} (.ident `A) == .ident `payload

#guard
  let (defs, _stats) := restrictLFDefinitionValuesForExprs ar3DependencyDefs {}
    #[.lam #[`A] (.ident `A)]
  defs.isEmpty

#guard
  lfExprEqModuloDefinitionsWithLocals ar3DependencyDefs {} (.ident `A) (.ident `payload)

/-- Definitions whose free identifiers stress comparison-binder freshness. -/
def deltaCaptureDefs : LFDefinitionValueMap :=
  ({} : LFDefinitionValueMap).insert `D (.ident `x)

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let env : LFDeltaConversionEnv := { defs := deltaCaptureDefs, options }
  let lhs := ObjExpr.lam #[`x] (.ident `D)
  let rhs := ObjExpr.lam #[`y] (.ident `y)
  let r := LFDeltaConversion.convertObjExpr env lhs rhs
  !r.accepted && r.stats.deltaSteps == 1

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let env : LFDeltaConversionEnv := { defs := deltaCaptureDefs, options }
  let lhs := ObjExpr.arrow (some `x) .sort (.ident `D)
  let rhs := ObjExpr.arrow (some `y) .sort (.ident `y)
  let r := LFDeltaConversion.convertObjExpr env lhs rhs
  !r.accepted && r.stats.deltaSteps == 1

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let sig : HLSignature := {
    name := `DeltaObjectGoalConversionDirectSmoke
    lfObjectDefs := #[{
      name := `Alias
      typeExpr := .ident `Shape
      value := .ident `payload }] }
  match checkObjectGoalConversion sig #[] #[] (.ident `Alias) (.ident `payload) options with
  | .ok conversion =>
      match conversion.steps[0]? with
      | some step => step.kind == .deltaConversion && step.unfoldedDefinitions.contains `Alias
      | none => false
  | .error _ => false

#guard
  let options : LFDeltaConversionOptions := {
    enabled := true
    compareWithFullFallback := true
    maxDeltaSteps := 0 }
  let sig : HLSignature := {
    name := `DeltaObjectGoalConversionFallbackSmoke
    lfObjectDefs := #[{
      name := `Alias
      typeExpr := .ident `Shape
      value := .ident `payload }] }
  match checkObjectGoalConversion sig #[] #[] (.ident `Alias) (.ident `payload) options with
  | .ok conversion =>
      match conversion.steps[0]? with
      | some step => step.kind == .lfDefinitionUnfolding
      | none => false
  | .error _ => false

#guard
  let options : LFDeltaConversionOptions := {
    enabled := true
    compareWithFullFallback := false
    maxDeltaSteps := 0 }
  let sig : HLSignature := {
    name := `DeltaObjectGoalConversionIntroSmoke
    lfObjectDefs := #[{
      name := `Alias
      typeExpr := .ident `Shape
      value := .ident `payload }] }
  let goal : InternalObjectGoal := {
    target := .arrow (some `h) (.ident `Alias) (.ident `payload)
    deltaOptions := options }
  let (_, inner) := autoIntroGoal goal
  inner.deltaOptions.enabled && !inner.deltaOptions.compareWithFullFallback &&
    (findAssumption? sig #[] inner.ctx inner.target inner.deltaOptions).isNone

#guard
  let options : LFDeltaConversionOptions := {
    enabled := true
    compareWithFullFallback := false
    maxDeltaSteps := 0 }
  let sig : HLSignature := {
    name := `DeltaObjectGoalConversionExplicitIntroSmoke
    lfObjectDefs := #[{
      name := `Alias
      typeExpr := .ident `Shape
      value := .ident `payload }] }
  let goal : InternalObjectGoal := {
    target := .arrow (some `h) (.ident `Alias) (.ident `payload)
    deltaOptions := options }
  match introObjectGoal goal `z with
  | .ok inner =>
      inner.deltaOptions.enabled && !inner.deltaOptions.compareWithFullFallback &&
        (findAssumption? sig #[] inner.ctx inner.target inner.deltaOptions).isNone
  | .error _ => false

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let env : LFDeltaConversionEnv := { defs := deltaSmokeDefs, options }
  let r := LFDeltaConversion.convertObjExpr env
    (.app (.lam #[`x] (.ident `x)) (.ident `payload)) (.ident `payload)
  r.accepted && r.stats.deltaSteps == 0

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let sig : HLSignature := {
    name := `DeltaCandidateMatchSmoke
    lfObjectDefs := #[{
      name := `Alias
      typeExpr := .ident `Shape
      value := .ident `payload }] }
  let defs := objectTacticLFDefinitionValues sig
  let candidate := ObjExpr.app (.app (.ident `Rel) (.ident `payload)) (.ident `payload)
  let expected := ObjExpr.app (.app (.ident `Rel) (.ident `Alias)) (.ident `Alias)
  let result := matchObjectCandidateDeltaResult defs {} {} candidate expected options
  result.deltaResult.accepted && result.deltaResult.stats.deltaSteps == 1 &&
    !result.deltaResult.fallbackUsed

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let sig : HLSignature := {
    name := `DeltaCandidatePatternSafetySmoke
    lfObjectDefs := #[{
      name := `Hidden
      typeExpr := .ident `Shape
      value := .ident `x }] }
  let defs := objectTacticLFDefinitionValues sig
  (matchObjectCandidateCheapFirst? defs {} ({`x} : NameSet) (.ident `Hidden) (.ident `payload)
    options).isNone

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := true }
  let sig : HLSignature := {
    name := `DeltaCandidateFallbackCompatibilitySmoke
    lfObjectDefs := #[{
      name := `Hidden
      typeExpr := .ident `Shape
      value := .ident `x }] }
  let defs := objectTacticLFDefinitionValues sig
  (matchObjectCandidateCheapFirst? defs {} ({`x} : NameSet) (.ident `Hidden) (.ident `payload)
    options).isSome

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let env : LFDeltaConversionEnv := { defs := deltaSmokeDefs, options }
  let r := LFDeltaConversion.convertObjExpr env (.fst (.pair (.ident `payload)
    (.ident `other))) (.ident `payload)
  r.accepted && r.stats.deltaSteps == 0

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let env : LFDeltaConversionEnv := {
    defs := deltaSmokeDefs
    locals := ({`y} : NameSet)
    options }
  let lhs := ObjExpr.app (.ident `K) (.ident `y)
  let rhs := ObjExpr.lam #[`z] (.ident `y)
  let r := LFDeltaConversion.convertObjExpr env lhs rhs
  r.accepted && r.stats.deltaSteps == 1

#guard
  let options : LFDeltaConversionOptions := {
    enabled := true
    compareWithFullFallback := false
    maxPairVisits := 0 }
  let env : LFDeltaConversionEnv := { defs := deltaSmokeDefs, options }
  let r := LFDeltaConversion.convertObjExpr env (.ident `Alias)
    (.ident `payload)
  !r.accepted && r.fuelExhausted? == some "pair"

#guard
  let options : LFDeltaConversionOptions := {
    enabled := true
    compareWithFullFallback := true
    maxDeltaSteps := 0 }
  let env : LFDeltaConversionEnv := { defs := deltaSmokeDefs, options }
  let r := LFDeltaConversion.convertObjExprWithFallback env
    (.ident `Alias) (.ident `payload)
  r.accepted && r.fallbackUsed && r.stats.fullFallbacks == 1

set_option internalLean.conversion.delta false

run_cmd do
  let focused ← Lean.Elab.Command.liftCoreM getLFRuleConclusionDeltaConversionOptions
  unless focused.enabled do
    throwError "LR3 focused rule-conclusion delta is disabled unexpectedly"

/-- A small source-level mismatch that focused primitive-rule conclusion delta can solve. -/
def lr3RuleConclusionActual : ObjExpr :=
  .app (.app (.app (.ident `shapeIncl) (.ident `emptyCtx)) (.ident `Alias)) (.ident `Alias)

/-- The matching primitive-rule conclusion before source aliases are unfolded. -/
def lr3RuleConclusionExpected : ObjExpr :=
  .app (.app (.app (.ident `shapeIncl) (.ident `emptyCtx)) (.ident `payload)) (.ident `payload)

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let entry := lfDefinitionComparisonProfileEntryWithOptions "rule_conclusion_match" {}
    deltaSmokeDefs {} lr3RuleConclusionActual lr3RuleConclusionExpected options
  entry.accepted && !entry.fullUnfoldFallback &&
    entry.deltaStats?.map (fun stats => stats.deltaSteps) == some 1 &&
      entry.deltaStats?.bind (fun stats => stats.forcedByName.find? `Alias) == some 1

#guard
  let options : LFDeltaConversionOptions := {
    enabled := true
    compareWithFullFallback := false
    maxDeltaSteps := 0 }
  let entry := lfDefinitionComparisonProfileEntryWithOptions "rule_conclusion_match" {}
    deltaSmokeDefs {} lr3RuleConclusionActual lr3RuleConclusionExpected options
  !entry.accepted && !entry.fullUnfoldFallback && entry.deltaFuelExhausted? == some "delta"

#guard
  let options : LFDeltaConversionOptions := { enabled := true, compareWithFullFallback := false }
  let defs := deltaSmokeDefs.insert `Wrap (.lam #[`x] (.app (.ident `box) (.ident `x)))
  let actual := .app (.ident `Wrap) (.ident `Alias)
  let expected := .app (.ident `Wrap) (.ident `payload)
  let entry := lfDefinitionComparisonProfileEntryWithOptions "rule_conclusion_match" {}
    defs {} actual expected options
  entry.accepted && !entry.fullUnfoldFallback &&
    entry.deltaStats?.bind (fun stats => stats.forcedByName.find? `Alias) == some 1 &&
      entry.deltaStats?.bind (fun stats => stats.forcedByName.find? `Wrap) == none

set_option internalLean.conversion.delta false
set_option internalLean.conversion.delta.compareFallback false
set_option internalLean.conversion.delta.maxDeltaSteps 100000

declare_type_theory LR3FocusedRuleConclusionDeltaSmoke where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque payload : Shape emptyCtx
  lf_def Alias : Shape emptyCtx := payload
  rule shape_refl (S : Shape emptyCtx) where
    conclusion : shapeIncl emptyCtx S S
  judgment_theorem alias_by_payload_rule : shapeIncl emptyCtx Alias Alias :=
    shape_refl payload

set_option internalLean.conversion.delta.maxDeltaSteps 0

/--
error: judgment_theorem 'bad' in type theory 'LR3FocusedRuleConclusionFuelReject' applies rule
'shape_refl' but the statement does not match the rule conclusion after LF-definition normalization:
LF-definition normalization could not match expressions.
actual: shapeIncl emptyCtx Alias Alias
expected: shapeIncl emptyCtx payload payload
normalized actual: shapeIncl emptyCtx payload payload
normalized expected: shapeIncl emptyCtx payload payload
LF definitions mentioned before unfolding: Alias
LF definitions unfolded: Alias
Normalization policy: LF matching unfolds earlier checked `lf_def` values, beta-reduces
explicit LF lambdas, contracts structural eta-redexes, and alpha-renames binders
to avoid local-binder capture.
-/
#guard_msgs (whitespace := lax) in
declare_type_theory LR3FocusedRuleConclusionFuelReject where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque payload : Shape emptyCtx
  lf_def Alias : Shape emptyCtx := payload
  rule shape_refl (S : Shape emptyCtx) where
    conclusion : shapeIncl emptyCtx S S
  judgment_theorem bad : shapeIncl emptyCtx Alias Alias :=
    shape_refl payload

set_option internalLean.conversion.delta.compareFallback true
set_option internalLean.conversion.delta.maxDeltaSteps 100000

declare_type_theory DeltaConversionProfileSmoke where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque payload : Shape emptyCtx
  lf_opaque other : Shape emptyCtx
  lf_def Alias : Shape emptyCtx := payload

set_option internalLean.conversion.delta.compareFallback false

/--
info: LF conversion profile site=delta_conversion, theory=DeltaConversionProfileSmoke,
owner=-:-, heads=Alias/payload, sizes=1/1, normalized_sizes=1/1, elapsed=0ms,
compact=false, fallback=false, accepted=true, unfolded=none, delta=true, delta_accepted=true,
delta_steps=1, pair_visits=1, pair_cache_hits=0, whnf_cache_hits=0, delta_cache_hits=0,
forced=Alias:1, forced_lhs=1, forced_rhs=0, full_fallbacks=0, fuel_exhausted=-
-/
#guard_msgs (whitespace := lax) in
#print_internal_delta_conversion_profile DeltaConversionProfileSmoke (Alias) (payload)

/--
info: LF conversion profile site=delta_candidate, theory=DeltaConversionProfileSmoke,
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=0ms,
compact=false, fallback=false, accepted=true, unfolded=none, delta=true, delta_accepted=true,
delta_steps=1, pair_visits=3, pair_cache_hits=1, whnf_cache_hits=3, delta_cache_hits=0,
forced=Alias:1, forced_lhs=0, forced_rhs=1, full_fallbacks=0, fuel_exhausted=-
-/
#guard_msgs (whitespace := lax) in
#print_internal_delta_candidate_profile DeltaConversionProfileSmoke
  (shapeIncl emptyCtx payload payload) (shapeIncl emptyCtx Alias Alias)

declare_type_theory DeltaObjectGoalConversionSmoke where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque payload : Shape emptyCtx
  lf_def Alias : Shape emptyCtx := payload
  rule shape_refl (S : Shape emptyCtx) where
    conclusion : shapeIncl emptyCtx S S
  judgment_theorem payload_refl : shapeIncl emptyCtx payload payload :=
    shape_refl payload
  judgment_theorem payload_refl_with_arg (S : Shape emptyCtx) :
      shapeIncl emptyCtx payload payload :=
    shape_refl payload

set_option internalLean.conversion.delta true
set_option internalLean.conversion.delta.compareFallback false

internal theorem DeltaObjectGoalConversionSmoke.delta_apply :
    shapeIncl emptyCtx Alias Alias := by
  apply payload_refl

internal theorem DeltaObjectGoalConversionSmoke.delta_change :
    shapeIncl emptyCtx Alias Alias := by
  change shapeIncl emptyCtx payload payload
  exact payload_refl

/--
info: LF conversion profile site=candidate_match, theory=DeltaObjectGoalConversionSmoke,
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=0ms,
compact=false, fallback=false, accepted=true, unfolded=none, delta=true, delta_accepted=true,
delta_steps=1, pair_visits=3, pair_cache_hits=1, whnf_cache_hits=3, delta_cache_hits=0,
forced=Alias:1, forced_lhs=0, forced_rhs=1, full_fallbacks=0, fuel_exhausted=-
-/
#guard_msgs (whitespace := lax) in
#print_internal_candidate_match_profile DeltaObjectGoalConversionSmoke
  (shapeIncl emptyCtx payload payload) (shapeIncl emptyCtx Alias Alias)

/--
info: LF conversion profile site=object_goal_conversion, theory=DeltaObjectGoalConversionSmoke,
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=0ms,
compact=false, fallback=false, accepted=true, unfolded=none, delta=true, delta_accepted=true,
delta_steps=1, pair_visits=3, pair_cache_hits=1, whnf_cache_hits=3, delta_cache_hits=0,
forced=Alias:1, forced_lhs=1, forced_rhs=0, full_fallbacks=0, fuel_exhausted=-
-/
#guard_msgs (whitespace := lax) in
#print_internal_object_conversion_profile DeltaObjectGoalConversionSmoke
  (shapeIncl emptyCtx Alias Alias) (shapeIncl emptyCtx payload payload)

set_option internalLean.conversion.delta.maxDeltaSteps 0

/--
error: native tactic `change` cannot replace the current object goal
  shapeIncl emptyCtx Alias Alias
with
  shapeIncl emptyCtx payload payload

The endpoints are not judgmentally convertible in the active object theory.
This tactic checks object conversion evidence; it does not use Lean equality or an internal equality
proof.

conversion failure: unsupported LF conversion: head-directed delta conversion rejected the endpoints
and full checked LF-definition unfolding fallback is disabled
delta_steps=0, pair_visits=3, forced=none, fuel_exhausted=delta

normalized actual: shapeIncl emptyCtx payload payload
normalized expected: shapeIncl emptyCtx payload payload
LF definitions mentioned before unfolding: Alias
LF definitions unfolded: Alias
-/
#guard_msgs (whitespace := lax) in
internal theorem DeltaObjectGoalConversionSmoke.delta_change_fuel_failure :
    shapeIncl emptyCtx Alias Alias := by
  change shapeIncl emptyCtx payload payload
  exact payload_refl

/--
error: native tactic `apply payload_refl` failed: conclusion
  shapeIncl emptyCtx payload payload
does not match current goal
  shapeIncl emptyCtx Alias Alias

normalized actual: shapeIncl emptyCtx payload payload
normalized expected: shapeIncl emptyCtx payload payload
LF definitions mentioned before unfolding: Alias
LF definitions unfolded: Alias
-/
#guard_msgs (whitespace := lax) in
internal theorem DeltaObjectGoalConversionSmoke.delta_native_apply_fuel_failure :
    shapeIncl emptyCtx Alias Alias := by
  apply payload_refl

/--
error: native tactic `refine payload_refl_with_arg` failed: conclusion
  shapeIncl emptyCtx payload payload
does not match current goal
  shapeIncl emptyCtx Alias Alias

normalized actual: shapeIncl emptyCtx payload payload
normalized expected: shapeIncl emptyCtx payload payload
LF definitions mentioned before unfolding: Alias
LF definitions unfolded: Alias
-/
#guard_msgs (whitespace := lax) in
internal theorem DeltaObjectGoalConversionSmoke.delta_native_refine_fuel_failure :
    shapeIncl emptyCtx Alias Alias := by
  refine payload_refl_with_arg payload

set_option internalLean.conversion.delta.maxDeltaSteps 100000

declare_type_theory DeltaSourceStatementConversionSmoke where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque payload : Shape emptyCtx
  lf_def Alias : Shape emptyCtx := payload
  rule shape_refl (S : Shape emptyCtx) where
    conclusion : shapeIncl emptyCtx S S
  judgment_theorem alias_by_payload_rule : shapeIncl emptyCtx Alias Alias :=
    shape_refl payload

declare_type_theory DeltaSourceRulePremiseConversionSmoke where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque payload : Shape emptyCtx
  lf_def Alias : Shape emptyCtx := payload
  rule shape_refl (S : Shape emptyCtx) where
    conclusion : shapeIncl emptyCtx S S
  rule use_prem (S : Shape emptyCtx) where
    premise h : shapeIncl emptyCtx S S
    conclusion : shapeIncl emptyCtx S S
  judgment_theorem payload_refl : shapeIncl emptyCtx payload payload :=
    shape_refl payload
  judgment_theorem alias_via_premise : shapeIncl emptyCtx Alias Alias :=
    use_prem Alias payload_refl

set_option internalLean.conversion.delta.maxDeltaSteps 0

/--
error: judgment_theorem 'bad' in type theory 'DeltaSourceStatementNoFallbackReject' applies rule
'shape_refl' but the statement does not match the rule conclusion after LF-definition normalization:
LF-definition normalization could not match expressions.
actual: shapeIncl emptyCtx Alias Alias
expected: shapeIncl emptyCtx payload payload
normalized actual: shapeIncl emptyCtx payload payload
normalized expected: shapeIncl emptyCtx payload payload
LF definitions mentioned before unfolding: Alias
LF definitions unfolded: Alias
Normalization policy: LF matching unfolds earlier checked `lf_def` values, beta-reduces
explicit LF lambdas, contracts structural eta-redexes, and alpha-renames binders
to avoid local-binder capture.
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DeltaSourceStatementNoFallbackReject where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque payload : Shape emptyCtx
  lf_def Alias : Shape emptyCtx := payload
  rule shape_refl (S : Shape emptyCtx) where
    conclusion : shapeIncl emptyCtx S S
  judgment_theorem bad : shapeIncl emptyCtx Alias Alias :=
    shape_refl payload

/--
error: judgment_theorem 'bad' in type theory 'DeltaSourceRulePremiseNoFallbackReject' uses premise
theorem 'payload_refl' with a statement that does not match after LF-definition normalization:
LF-definition normalization could not match expressions.
actual: shapeIncl emptyCtx payload payload
expected: shapeIncl emptyCtx Alias Alias
normalized actual: shapeIncl emptyCtx payload payload
normalized expected: shapeIncl emptyCtx payload payload
LF definitions mentioned before unfolding: Alias
LF definitions unfolded: Alias
Normalization policy: LF matching unfolds earlier checked `lf_def` values, beta-reduces
explicit LF lambdas, contracts structural eta-redexes, and alpha-renames binders
to avoid local-binder capture.
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DeltaSourceRulePremiseNoFallbackReject where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque payload : Shape emptyCtx
  lf_def Alias : Shape emptyCtx := payload
  rule shape_refl (S : Shape emptyCtx) where
    conclusion : shapeIncl emptyCtx S S
  rule use_prem (S : Shape emptyCtx) where
    premise h : shapeIncl emptyCtx S S
    conclusion : shapeIncl emptyCtx S S
  judgment_theorem payload_refl : shapeIncl emptyCtx payload payload :=
    shape_refl payload
  judgment_theorem bad : shapeIncl emptyCtx Alias Alias :=
    use_prem Alias payload_refl
