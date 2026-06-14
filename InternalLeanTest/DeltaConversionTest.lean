/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Head-directed delta conversion smoke tests

Focused tests for the option-gated delta-conversion engine.  These tests call the new engine and
manual profile commands directly; ordinary checker/tactic acceptance is integrated in later phases.
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
  let env : LFDeltaConversionEnv := { defs := deltaSmokeDefs, options }
  let r := LFDeltaConversion.convertObjExpr env
    (.app (.lam #[`x] (.ident `x)) (.ident `payload)) (.ident `payload)
  r.accepted && r.stats.deltaSteps == 0

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
