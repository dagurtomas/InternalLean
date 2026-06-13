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

declare_type_theory LFConversionProfileSmoke where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque simplexPayload : Shape emptyCtx
  lf_def Alias : Shape emptyCtx := simplexPayload
  rule simplex_refl_rule (S : Shape emptyCtx) where
    conclusion : shapeIncl emptyCtx S S
  judgment_theorem alias_payload : shapeIncl emptyCtx simplexPayload simplexPayload :=
    simplex_refl_rule Alias

/--
info: LF conversion profile site=object_goal_conversion, theory=LFConversionProfileSmoke,
owner=-:-, heads=shapeIncl/shapeIncl, sizes=7/7, normalized_sizes=7/7, elapsed=-,
compact=false, fallback=true, accepted=true, unfolded=Alias:2
-/
#guard_msgs (whitespace := lax) in
#print_internal_object_conversion_profile LFConversionProfileSmoke
  (shapeIncl emptyCtx Alias Alias) (shapeIncl emptyCtx simplexPayload simplexPayload)
