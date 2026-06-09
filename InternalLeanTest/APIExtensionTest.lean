/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Logical-framework API extension smoke tests

These tests exercise LF metadata declarations for richer object-theory encodings. The direct-LF
checker stores and reports these declarations, derives rule schemas, exercises the trivial
side-condition hook, and checks replay wrappers and the generic conversion-certificate trust
boundary. Custom judgments, rules, nontrivial side-condition solvers, and conversion plugins stay
inside the explicit LF trust boundary.
-/

@[expose] public section

open InternalLean

#guard
  let σ : Instantiation := fun
    | `x => .tmConst `y
    | `A => .tyConst `B
    | n => .leanParam n
  let raw := Raw.scopedBind `ordinary `var `x (.tyMeta `A)
    (.tmApp `body [.leanParam `x, .tyMeta `A])
  raw.instantiate σ == Raw.scopedBind `ordinary `var `x (.tyConst `B)
    (.tmApp `body [.leanParam `x, .tyConst `B])

#guard
  let σ : Instantiation := fun
    | `A => .tyConst `B
    | n => .leanParam n
  let raw := Raw.scopedBind `ordinary `var `x (.tyMeta `A)
    (.tmApp `body [.leanParam `x, .tyMeta `A])
  match raw.instantiateChecked σ with
  | .ok checked => checked == raw.instantiate σ
  | .error _ => false

#guard
  let σ : Instantiation := fun
    | `A => .leanParam `x
    | n => .leanParam n
  let raw := Raw.scopedBind `ordinary `var `x (.tyConst `Ty) (.tyMeta `A)
  match raw.instantiateChecked σ with
  | .ok _ => false
  | .error err => err.contains "instantiating 'A' would capture local 'x' under scoped binder"

#guard
  let xOuter := Lean.addMacroScope `outer `x 1
  let xInner := Lean.addMacroScope `inner `x 2
  let raw := Raw.scopedBind `ordinary `var xOuter (.tyConst `Ty) (.leanParam xInner)
  raw.localRefNames == [xInner]

#guard
  let xOuter := Lean.addMacroScope `outer `x 1
  let xInner := Lean.addMacroScope `inner `x 2
  let σ : Instantiation := fun
    | `A => .leanParam xInner
    | n => .leanParam n
  let raw := Raw.scopedBind `ordinary `var xOuter (.tyConst `Ty) (.tyMeta `A)
  match raw.instantiateChecked σ with
  | .ok checked => checked == raw.instantiate σ
  | .error _ => false

#guard
  let stmt : Judgment := .custom `ok []
  let r : RuleSchema := RuleSchema.mk `ok_rule [] [] [] [] [] stmt
  let cert : KernelLFReplayCertificate :=
    { signature := { name := `SmallReplaySmoke, rules := [r] },
      statement := stmt,
      derivation := .ruleApp `ok_rule stmt {} [] [] }
  match cert.toChecked with
  | .ok checked =>
      checked.statement == stmt && cert.ruleNames == [`ok_rule] && cert.contextNames.isEmpty
  | .error _ => false

#guard
  let stmt : Judgment := .custom `ok []
  let r : RuleSchema := RuleSchema.mk `ok_rule [] [] [] [] [] stmt
  let derivation := KernelLFDerivation.ruleApp `ok_rule stmt {} [] []
  match CheckedKernelLFDerivation.ofDerivation { name := `SmallReplaySmoke, rules := [r] }
      {} derivation with
  | .ok checked =>
      match checked.check with
      | .ok () => checked.statement == stmt
      | .error _ => false
  | .error _ => false

#guard
  let stmt : Judgment := .custom `ok []
  let bad : Judgment := .custom `bad []
  let r : RuleSchema := RuleSchema.mk `ok_rule [] [] [] [] [] stmt
  let cert : KernelLFReplayCertificate :=
    { signature := { name := `SmallReplaySmoke, rules := [r] },
      statement := bad,
      derivation := .ruleApp `ok_rule stmt {} [] [] }
  match cert.toChecked with
  | .ok _ => false
  | .error err => err.contains "rule application 'ok_rule' has conclusion"

#guard
  let metas : List RuleMetaVar := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) },
    { name := `A, sort := .custom `Ty, type? := some (.tyApp `Ty [.tmMeta `Γ]) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value :=
      .tmConst `emptyCtx },
    { name := `A, sort := .custom `Ty, type? := some (.tyApp `Ty [.tmConst `emptyCtx]), value :=
      .tmConst `natTy }] }
  match inst.validateAgainst metas with
  | .ok _ => true
  | .error _ => false

#guard
  let metas : List RuleMetaVar := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) },
    { name := `A, sort := .custom `Ty, type? := some (.tyApp `Ty [.tmMeta `Γ]) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value :=
      .tmConst `emptyCtx },
    { name := `A, sort := .custom `Ty, type? := some (.tyApp `Ty [.tmMeta `Γ]), value :=
      .tmConst `natTy }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error _ => true

#guard
  let metas : List RuleMetaVar := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) },
    { name := `Δ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value :=
      .tmConst `emptyCtx },
    { name := `Δ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value := .leanParam `Γ }] }
  match inst.validateAgainst metas with
  | .ok _ => true
  | .error _ => false

#guard
  let metas : List RuleMetaVar := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) },
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value :=
      .tmConst `emptyCtx },
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value :=
      .tmConst `otherCtx }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err => err.contains "rule metavariable telescope has duplicate name 'Γ'"

#guard
  let metas : List RuleMetaVar := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) },
    { name := `Δ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value :=
      .tmConst `emptyCtx },
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value :=
      .tmConst `otherCtx }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err => err.contains "scoped instantiation has duplicate entry name 'Γ'"

#guard
  let metas : List RuleMetaVar := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) },
    { name := `A, sort := .custom `Ty, type? := some (.tyApp `Ty [.tmMeta `Γ]) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value :=
      .tmConst `emptyCtx },
    { name := `A, sort := .custom `Ty, type? := some (.tyApp `Ty [.tmConst `emptyCtx]), value :=
      .leanParam `Γ }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error _ => true

#guard
  let metas : List RuleMetaVar := [
    { name := `A, sort := .ty, type? := none }]
  let inst : ScopedInstantiation := { entries := [
    { name := `A, sort := .ty, type? := none, value := .tySubst (.tyConst `Nat) .substEmpty }] }
  match inst.validateAgainst metas with
  | .ok _ => true
  | .error _ => false

#guard
  let metas : List RuleMetaVar := [
    { name := `A, sort := .ty, type? := none }]
  let inst : ScopedInstantiation := { entries := [
    { name := `A, sort := .ty, type? := none, value := .tmConst `zero }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err =>
    err.contains "has value headed by sort 'InternalLean.RawMetaSort.tm', expected \
      'InternalLean.RawMetaSort.ty'"

#guard
  let metas : List RuleMetaVar := [
    { name := `σ, sort := .subst, type? := none }]
  let inst : ScopedInstantiation := { entries := [
    { name := `σ, sort := .subst, type? := none, value := .substEmpty }] }
  match inst.validateAgainst metas with
  | .ok _ => true
  | .error _ => false

#guard
  let metas : List RuleMetaVar := [
    { name := `σ, sort := .subst, type? := none }]
  let inst : ScopedInstantiation := { entries := [
    { name := `σ, sort := .subst, type? := none, value := .tyConst `Nat }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err =>
    err.contains "has value headed by sort 'InternalLean.RawMetaSort.ty', expected \
      'InternalLean.RawMetaSort.subst'"

#guard
  let substEvidence := Judgment.wfSubst .ctxNil (.substMeta `σ) .ctxNil
  let metas : List RuleMetaVar := [
    { name := `σ, sort := .subst, type? := none, evidence? := some substEvidence }]
  let inst : ScopedInstantiation := { entries := [
    { name := `σ, sort := .subst, type? := none, evidence? :=
      some (.wfSubst .ctxNil .substEmpty .ctxNil), value := .substEmpty }] }
  match inst.validateAgainst metas with
  | .ok _ => true
  | .error _ => false

#guard
  let substEvidence := Judgment.wfSubst .ctxNil (.substMeta `σ) .ctxNil
  let metas : List RuleMetaVar := [
    { name := `σ, sort := .subst, type? := none, evidence? := some substEvidence }]
  let inst : ScopedInstantiation := { entries := [
    { name := `σ, sort := .subst, type? := none, value := .substEmpty }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err => err.contains "has evidence 'none', expected scoped evidence"

#guard
  let substEvidence := Judgment.wfSubst .ctxNil (.substMeta `σ) .ctxNil
  let metas : List RuleMetaVar := [
    { name := `σ, sort := .subst, type? := none, evidence? := some substEvidence }]
  let inst : ScopedInstantiation := { entries := [
    { name := `σ, sort := .subst, type? := none,
      evidence? := some (.wfSubst .ctxNil (.substId .ctxNil) .ctxNil), value := .substEmpty }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err => err.contains "expected scoped evidence"

#guard
  let metas : List RuleMetaVar := [
    { name := `σ, sort := .subst, type? := none,
      evidence? := some (.wfSubst (.ctxMeta `Γ) (.substMeta `σ) .ctxNil) },
    { name := `Γ, sort := .ctx, type? := none }]
  let inst : ScopedInstantiation := { entries := [
    { name := `σ, sort := .subst, type? := none,
      evidence? := some (.wfSubst .ctxNil .substEmpty .ctxNil), value := .substEmpty },
    { name := `Γ, sort := .ctx, type? := none, value := .ctxNil }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err => err.contains "evidence annotation referencing later metavariable 'Γ'"

#guard
  let metas : List RuleMetaVar := [
    { name := `A, sort := .ty, type? := none }]
  let inst : ScopedInstantiation := { entries := [
    { name := `A, sort := .ty, type? := none, value := .tySubst (.tyConst `Nat) (
      .tmConst `badSubst) }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err =>
    err.contains "tySubst substitution argument headed by sort 'InternalLean.RawMetaSort.tm', \
      expected 'InternalLean.RawMetaSort.subst'"

#guard
  let metas : List RuleMetaVar := [
    { name := `τ, sort := .subst, type? := none }]
  let inst : ScopedInstantiation := { entries := [
    { name := `τ, sort := .subst, type? := none, value := .substExt (.substEmpty) (
      .tyConst `BadTerm) }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err =>
    err.contains "substExt term argument headed by sort 'InternalLean.RawMetaSort.ty', expected \
      'InternalLean.RawMetaSort.tm'"

#guard
  let metas : List RuleMetaVar := [
    { name := `τ, sort := .subst, type? := none }]
  let inst : ScopedInstantiation := { entries := [
    { name := `τ, sort := .subst, type? := none, value := .substId (.tmConst `badCtx) }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err =>
    err.contains "substId context argument headed by sort 'InternalLean.RawMetaSort.tm', expected \
      'InternalLean.RawMetaSort.ctx'"

#guard
  let metas : List RuleMetaVar := [
    { name := `τ, sort := .subst, type? := none }]
  let inst : ScopedInstantiation := { entries := [
    { name := `τ, sort := .subst, type? := none, value :=
      .substComp .substEmpty (.tyConst `badSubst) }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err =>
    err.contains "substComp right substitution argument headed by sort \
      'InternalLean.RawMetaSort.ty', expected 'InternalLean.RawMetaSort.subst'"

#guard
  let constants : List LFConstantSchema := [
    { name := `emptyCtx, params := [], resultType := .tyConst `Ctx },
    { name := `mkShape,
      params := [{ name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) }],
      resultType := .tyApp `Shape [.tmMeta `Γ] }]
  let metas : List RuleMetaVar := [
    { name := `S, sort := .custom `Shape, type? := some (.tyApp `Shape [.tmConst `emptyCtx]) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `S, sort := .custom `Shape, type? := some (.tyApp `Shape [.tmConst `emptyCtx]),
      value := .tmApp `mkShape [.tmConst `emptyCtx] }] }
  match inst.validateAgainstWithConstants constants metas with
  | .ok _ => true
  | .error _ => false

#guard
  let constants : List LFConstantSchema := [
    { name := `emptyCtx, params := [], resultType := .tyConst `Ctx },
    { name := `other, params := [], resultType := .tyConst `OtherCtx },
    { name := `mkShape,
      params := [{ name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) }],
      resultType := .tyApp `Shape [.tmMeta `Γ] }]
  let metas : List RuleMetaVar := [
    { name := `S, sort := .custom `Shape, type? := some (.tyApp `Shape [.tmConst `emptyCtx]) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `S, sort := .custom `Shape, type? := some (.tyApp `Shape [.tmConst `emptyCtx]),
      value := .tmApp `mkShape [.tmConst `other] }] }
  match inst.validateAgainstWithConstants constants metas with
  | .ok _ => false
  | .error err =>
      err.contains "argument 1 of typed LF constant 'mkShape'" &&
      err.contains "expected 'InternalLean.Raw.tyConst `Ctx'"

#guard
  let constants : List LFConstantSchema := [
    { name := `mkShape,
      params := [{ name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) }],
      resultType := .tyApp `Shape [.tmMeta `Γ] }]
  let metas : List RuleMetaVar := [
    { name := `S, sort := .custom `Shape, type? := some (.tyApp `Shape [.tmConst `emptyCtx]) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `S, sort := .custom `Shape, type? := some (.tyApp `Shape [.tmConst `emptyCtx]),
      value := .tmConst `mkShape }] }
  match inst.validateAgainstWithConstants constants metas with
  | .ok _ => false
  | .error err =>
    err.contains "typed LF constant 'mkShape' is used with 0 argument(s), expected 1 argument(s)"

#guard
  let constants : List LFConstantSchema := [
    { name := `emptyCtx, params := [], resultType := .tyConst `Ctx },
    { name := `emptyCtx, params := [], resultType := .tyConst `Ctx }]
  let metas : List RuleMetaVar := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value :=
      .tmConst `emptyCtx }] }
  match inst.validateAgainstWithConstants constants metas with
  | .ok _ => false
  | .error err => err.contains "typed LF constant 'emptyCtx' with 0 argument(s) is ambiguous"

#guard
  let constants : List LFConstantSchema := [
    { name := `emptyCtx, params := [], resultType := .tyConst `Ctx },
    { name := `mkDependent,
      params := [
        { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) },
        { name := `S, sort := .custom `Shape, type? := some (.tyApp `Shape [.tmMeta `Γ]) }],
      resultType := .tyApp `Shape [.tmMeta `Γ] }]
  let metas : List RuleMetaVar := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) },
    { name := `S, sort := .custom `Shape, type? := some (.tyApp `Shape [.tmMeta `Γ]) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value :=
      .tmConst `emptyCtx },
    { name := `S, sort := .custom `Shape, type? := some (.tyApp `Shape [.tmConst `emptyCtx]),
      value := .tmApp `mkDependent [.tmConst `emptyCtx, .leanParam `Γ] }] }
  match inst.validateAgainstWithConstants constants metas with
  | .ok _ => false
  | .error err => err.contains "argument 2 of typed LF constant 'mkDependent'"

#guard
  let metas : List RuleMetaVar := [
    { name := `S, sort := .custom `Shape, type? := some (.tyConst `Shape) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `S, sort := .custom `Shape, type? := some (.tyConst `Shape), value :=
      .leanParam `missing }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err => err.contains "unknown or out-of-scope local 'missing'"

#guard
  let metas : List RuleMetaVar := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx) },
    { name := `A, sort := .custom `Ty, type? := some (.tyApp `Ty [.tmMeta `Γ]) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `Γ, sort := .custom `Ctx, type? := some (.tyConst `Ctx), value := .leanParam `A },
    { name := `A, sort := .custom `Ty, type? := some (.tyApp `Ty [.leanParam `Γ]), value :=
      .tmConst `natTy }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err => err.contains "referencing later metavariable 'A'"

#guard
  let metas : List RuleMetaVar := [
    { name := `A, sort := .custom `Ty, type? := some (.tyApp `Ty [.leanParam `missing]) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `A, sort := .custom `Ty, type? := some (.tyApp `Ty [.leanParam `missing]), value :=
      .tmConst `natTy }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error err => err.contains "type annotation referencing unknown or out-of-scope local 'missing'"

#guard
  let metas : List RuleMetaVar := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun) }]
  let escaped := Raw.tmApp `pair [
    .scopedBind `ordinary `ordinary_var `x (.tyConst `Tm) (.leanParam `x),
    .leanParam `x]
  let inst : ScopedInstantiation := { entries := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun), value := escaped }] }
  match inst.validateAgainstWithSignature []
      [{ name := `ordinary, sort := .custom `Ctx }]
      [{ name := `ordinary_var, zone := `ordinary, boundSort := .custom `Tm }]
      metas with
  | .ok _ => false
  | .error err => err.contains "value referencing unknown or out-of-scope local 'x'"

#guard
  let metas : List RuleMetaVar := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun),
      value := .scopedBind `ordinary `ordinary_var `x (.tyConst `Tm) (.leanParam `x) }] }
  match inst.validateAgainstWithSignature []
      [{ name := `ordinary, sort := .custom `Ctx }]
      [{ name := `ordinary_var, zone := `ordinary, boundSort := .custom `Tm }]
      metas with
  | .ok _ => true
  | .error _ => false

#guard
  let x₁ := Lean.addMacroScope `shadowA `x 1
  let x₂ := Lean.addMacroScope `shadowB `x 2
  let metas : List RuleMetaVar := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun),
      value := .scopedBind `ordinary `ordinary_var x₁ (.tyConst `Tm)
        (.scopedBind `ordinary `ordinary_var x₂ (.tyConst `Tm) (.leanParam x₂)) }] }
  match inst.validateAgainstWithSignature []
      [{ name := `ordinary, sort := .custom `Ctx }]
      [{ name := `ordinary_var, zone := `ordinary, boundSort := .custom `Tm }]
      metas with
  | .ok _ => false
  | .error err =>
      err.contains "scoped binder #2 named 'x'" &&
      err.contains "shadowing earlier binder identity"

#guard
  let x₁ := Lean.addMacroScope `ambientA `x 1
  let x₂ := Lean.addMacroScope `ambientB `x 2
  let metas : List RuleMetaVar := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun), value := .leanParam `x }] }
  match inst.validateAgainstWithConstants [] metas [x₁, x₂] with
  | .ok _ => false
  | .error err => err.contains "ambiguous local binder 'x'"
    && err.contains "available local identities"

#guard
  let x₁ := Lean.addMacroScope `ambientA `x 1
  let metas : List RuleMetaVar := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun), value := .leanParam `x }] }
  match inst.validateAgainstWithConstants [] metas [x₁] with
  | .ok _ => false
  | .error err => err.contains "referencing stale local 'x'"

#guard
  let metas : List RuleMetaVar := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun),
      value := .scopedBind `ordinary `ordinary_var `x (.tyConst `Wrong) (.leanParam `x) }] }
  match inst.validateAgainstWithSignature []
      [{ name := `ordinary, sort := .custom `Ctx }]
      [{ name := `ordinary_var, zone := `ordinary, boundSort := .custom `Tm }]
      metas with
  | .ok _ => false
  | .error err => err.contains "expected bound sort"

#guard
  let metas : List RuleMetaVar := [
    { name := `Γ, sort := .custom `Ctx, zone? := some `ordinary, type? := some (.tyConst `Ctx) }]
  let inst : ScopedInstantiation := { entries := [
    { name := `Γ, sort := .custom `Ctx, zone? := none, type? := some (.tyConst `Ctx), value :=
      .tmConst `emptyCtx }] }
  match inst.validateAgainst metas with
  | .ok _ => false
  | .error _ => true

#guard
  let r : RuleSchema := RuleSchema.mk `ctx_rule
    [{ name := `Γ, sort := .custom `Ctx, zone? := some `ordinary, type? := some (.tyConst `Ctx) }]
    [] [] [] [] (.custom `J [.leanParam `Γ])
  let entry : ScopedInstantiationEntry := {
    name := `Γ
    sort := .custom `Ctx
    zone? := some `ordinary
    type? := some (.tyConst `Ctx)
    value := .tmConst `emptyCtx
  }
  let inst : ScopedInstantiation := { entries := [entry] }
  let d := KernelLFDerivation.ruleApp `ctx_rule (.custom `J [.tmConst `emptyCtx]) inst [] []
  let zone : ContextZoneSchema := { name := `ordinary, sort := .custom `Ctx }
  let sig : Signature := { name := `T, contextZones := [zone], rules := [r] }
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J [.tmConst `emptyCtx]) with
  | .ok _ => true
  | .error _ => false

#guard
  let r : RuleSchema := RuleSchema.mk `ctx_rule
    [{ name := `Γ, sort := .custom `Ctx, zone? := some `ordinary, type? := some (.tyConst `Ctx) }]
    [] [] [] [] (.custom `J [.leanParam `Γ])
  let entry : ScopedInstantiationEntry := {
    name := `Γ
    sort := .custom `Ctx
    zone? := some `ordinary
    type? := some (.tyConst `Ctx)
    value := .tmConst `emptyCtx
  }
  let inst : ScopedInstantiation := { entries := [entry] }
  let d := KernelLFDerivation.ruleApp `ctx_rule (.custom `J [.tmConst `emptyCtx]) inst [] []
  let sig : Signature := { name := `T, rules := [r] }
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J [.tmConst `emptyCtx]) with
  | .ok _ => false
  | .error err => err.contains "unknown context zone 'ordinary'"

#guard
  let r : RuleSchema := RuleSchema.mk `capture_rule
    [ { name := `x, sort := .custom `Tm, type? := some (.tyConst `Tm) },
      { name := `A, sort := .custom `Tm, type? := some (.tyConst `Tm) } ]
    [] [] [] [] (.custom `J [Raw.scopedBind `ordinary `ordinary_var `x (.tyConst `Tm) (.tmMeta `A)])
  let inst : ScopedInstantiation := { entries := [
    { name := `x, sort := .custom `Tm, type? := some (.tyConst `Tm), value := .tmConst `externalX },
    { name := `A, sort := .custom `Tm, type? := some (.tyConst `Tm), value := .leanParam `x } ] }
  let sig : Signature := {
    name := `T,
    contextZones := [{ name := `ordinary, sort := .custom `Ctx }],
    binderClasses := [{ name := `ordinary_var, zone := `ordinary, boundSort := .custom `Tm }],
    rules := [r] }
  let d := KernelLFDerivation.ruleApp `capture_rule (.custom `J [.tmConst `captured]) inst [] []
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J [.tmConst `captured]) with
  | .ok _ => false
  | .error err => err.contains "capture-unsafe conclusion instantiation"
    && err.contains "would capture local 'x'"

#guard
  let r : RuleSchema := RuleSchema.mk `ctx_rule
    [{ name := `Γ, sort := .custom `Ctx, zone? := some `ordinary, type? := some (.tyConst `Ctx) }]
    [] [] [] [] (.custom `J [.leanParam `Γ])
  let entry : ScopedInstantiationEntry := {
    name := `Γ
    sort := .custom `Ctx
    zone? := some `ordinary
    type? := some (.tyConst `Ctx)
    value := .tmConst `emptyCtx
  }
  let inst : ScopedInstantiation := { entries := [entry] }
  let d := KernelLFDerivation.ruleApp `ctx_rule (.custom `J [.tmConst `emptyCtx]) inst [] []
  let zone : ContextZoneSchema := { name := `ordinary, sort := .custom `OtherCtx }
  let sig : Signature := { name := `T, contextZones := [zone], rules := [r] }
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J [.tmConst `emptyCtx]) with
  | .ok _ => false
  | .error err => err.contains "expected zone sort"

#guard
  let evidenceTemplate := Judgment.custom `P
    [Raw.scopedBind `ordinary `ordinary_var `x (.tyConst `Tm) (.tmMeta `A)]
  let metas : List RuleMetaVar := [
    { name := `x, sort := .custom `Tm, type? := some (.tyConst `Tm) },
    { name := `A, sort := .custom `Tm, type? := some (.tyConst `Tm), evidence? :=
      some evidenceTemplate }]
  let inst : ScopedInstantiation := { entries := [
    { name := `x, sort := .custom `Tm, type? := some (.tyConst `Tm), value := .tmConst `externalX },
    { name := `A, sort := .custom `Tm, type? := some (.tyConst `Tm),
      evidence? := some (.custom `P [.tmConst `payload]), value := .leanParam `x }] }
  match inst.validateAgainstWithSignature []
      [{ name := `ordinary, sort := .custom `Ctx }]
      [{ name := `ordinary_var, zone := `ordinary, boundSort := .custom `Tm }]
      metas with
  | .ok _ => false
  | .error err => err.contains "capture-unsafe evidence annotation"
    && err.contains "would capture local 'x'"

#guard
  let premiseTemplate := Judgment.custom `P
    [Raw.scopedBind `ordinary `ordinary_var `x (.tyConst `Tm) (.tmMeta `A)]
  let r : RuleSchema := RuleSchema.mk `capture_premise_rule
    [ { name := `x, sort := .custom `Tm, type? := some (.tyConst `Tm) },
      { name := `A, sort := .custom `Tm, type? := some (.tyConst `Tm) } ]
    [premiseTemplate] [] [] [] (.custom `J [])
  let inst : ScopedInstantiation := { entries := [
    { name := `x, sort := .custom `Tm, type? := some (.tyConst `Tm), value := .tmConst `externalX },
    { name := `A, sort := .custom `Tm, type? := some (.tyConst `Tm), value := .leanParam `x } ] }
  let sig : Signature := {
    name := `T,
    contextZones := [{ name := `ordinary, sort := .custom `Ctx }],
    binderClasses := [{ name := `ordinary_var, zone := `ordinary, boundSort := .custom `Tm }],
    rules := [r] }
  let d := KernelLFDerivation.ruleApp `capture_premise_rule (.custom `J []) inst
    [.theoremRef `hidden (.custom `P [.tmConst `payload])] []
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J []) with
  | .ok _ => false
  | .error err => err.contains "capture-unsafe premise instantiation"
    && err.contains "would capture local 'x'"

#guard
  let conditionTemplate : SideCondition :=
    { name := `capture_side, args := [Raw.scopedBind `ordinary `ordinary_var `x (.tyConst `Tm) (
      .tmMeta `A)] }
  let r : RuleSchema := RuleSchema.mk `capture_side_condition_rule
    [ { name := `x, sort := .custom `Tm, type? := some (.tyConst `Tm) },
      { name := `A, sort := .custom `Tm, type? := some (.tyConst `Tm) } ]
    [] [conditionTemplate]
    [{ name := `slot, condition := conditionTemplate }]
    [{ name := `capture_cert, condition := conditionTemplate, kind := .builtinTrivial }]
    (.custom `J [])
  let inst : ScopedInstantiation := { entries := [
    { name := `x, sort := .custom `Tm, type? := some (.tyConst `Tm), value := .tmConst `externalX },
    { name := `A, sort := .custom `Tm, type? := some (.tyConst `Tm), value := .leanParam `x } ] }
  let sig : Signature := {
    name := `T,
    contextZones := [{ name := `ordinary, sort := .custom `Ctx }],
    binderClasses := [{ name := `ordinary_var, zone := `ordinary, boundSort := .custom `Tm }],
    rules := [r] }
  let d :=
    KernelLFDerivation.ruleApp `capture_side_condition_rule (.custom `J []) inst [] [`capture_cert]
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J []) with
  | .ok _ => false
  | .error err => err.contains "capture-unsafe side-condition instantiation"
    && err.contains "would capture local 'x'"

#guard
  let r : RuleSchema := RuleSchema.mk `plain [] [] [] [] [] (.custom `J [])
  let sig : Signature :=
    { name := `T, contextZones := [{ name := `ordinary }, { name := `ordinary }], rules := [r] }
  let d := KernelLFDerivation.ruleApp `plain (.custom `J []) {} [] []
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J []) with
  | .ok _ => false
  | .error err => err.contains "duplicate context-zone schema 'ordinary'"

#guard
  let r : RuleSchema := RuleSchema.mk `plain [] [] [] [] [] (.custom `J [])
  let sig : Signature :=
    { name := `T, contextZones := [{ name := `late, dependsOn := [`earlier] }, { name :=
      `earlier }], rules := [r] }
  let d := KernelLFDerivation.ruleApp `plain (.custom `J []) {} [] []
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J []) with
  | .ok _ => false
  | .error err => err.contains "depends on unknown or later zone 'earlier'"

#guard
  let r : RuleSchema := RuleSchema.mk `plain [] [] [] [] [] (.custom `J [])
  let sig : Signature :=
    { name := `T, binderClasses := [{ name := `var, zone := `missing }], rules := [r] }
  let d := KernelLFDerivation.ruleApp `plain (.custom `J []) {} [] []
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J []) with
  | .ok _ => false
  | .error err => err.contains "uses unknown context zone 'missing'"

#guard
  let bad := Raw.tySubst (.tyConst `Nat) (.tmConst `badSubst)
  let r : RuleSchema := RuleSchema.mk `bad_subst_rule [] [] [] [] [] (.custom `J [bad])
  let sig : Signature := { name := `T, rules := [r] }
  let d := KernelLFDerivation.ruleApp `bad_subst_rule (.custom `J [bad]) {} [] []
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J [bad]) with
  | .ok _ => false
  | .error err =>
    err.contains "tySubst substitution argument headed by sort 'InternalLean.RawMetaSort.tm', \
      expected 'InternalLean.RawMetaSort.subst'"

#guard
  let bad := Raw.tmSubst (.tyConst `badTerm) .substEmpty
  let r : RuleSchema := RuleSchema.mk `bad_tm_subst_rule [] [] [] [] [] (.custom `J [bad])
  let sig : Signature := { name := `T, rules := [r] }
  let d := KernelLFDerivation.ruleApp `bad_tm_subst_rule (.custom `J [bad]) {} [] []
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J [bad]) with
  | .ok _ => false
  | .error err =>
    err.contains "tmSubst term argument headed by sort 'InternalLean.RawMetaSort.ty', expected \
      'InternalLean.RawMetaSort.tm'"

#guard
  let badPremise := Judgment.custom `J [Raw.tySubst (.tyConst `Nat) (.tmConst `badSubst)]
  let r : RuleSchema := RuleSchema.mk `bad_premise_rule [] [badPremise] [] [] [] (.custom `J [])
  let sig : Signature := { name := `T, rules := [r] }
  let d :=
    KernelLFDerivation.ruleApp `bad_premise_rule (.custom `J []) {} [.theoremRef `premise
      badPremise] []
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J []) with
  | .ok _ => false
  | .error err =>
    err.contains "tySubst substitution argument headed by sort 'InternalLean.RawMetaSort.tm', \
      expected 'InternalLean.RawMetaSort.subst'"

#guard
  let badCondition : SideCondition := { name := `bad_solver, args := [Raw.tySubst (.tyConst `Nat) (
    .tmConst `badSubst)] }
  let r : RuleSchema := RuleSchema.mk `bad_side_condition_rule [] [] [badCondition]
    [{ name := `bad, condition := badCondition }]
    [{ name := `bad_cert, condition := badCondition, kind := .builtinTrivial }]
    (.custom `J [])
  let sig : Signature := { name := `T, rules := [r] }
  let d := KernelLFDerivation.ruleApp `bad_side_condition_rule (.custom `J []) {} [] [`bad_cert]
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J []) with
  | .ok _ => false
  | .error err => err.contains "instantiated side-condition 'bad_solver'" &&
      err.contains "tySubst substitution argument headed by sort 'InternalLean.RawMetaSort.tm', \
        expected 'InternalLean.RawMetaSort.subst'"

#guard
  let condition : SideCondition := { name := `opaque_solver, args := [.tmConst `payload] }
  let r : RuleSchema := RuleSchema.mk `uncertified_side_condition_rule [] [] [condition]
    [{ name := `opaque, condition := condition }]
    []
    (.custom `J [])
  let sig : Signature := { name := `T, rules := [r] }
  let d := KernelLFDerivation.ruleApp `uncertified_side_condition_rule (.custom `J []) {} [] []
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J []) with
  | .ok _ => false
  | .error err =>
    err.contains "1 side-condition certificate slot(s) but only 0 checked certificate(s)"

#guard
  let condition : SideCondition := { name := `side, args := [.tmConst `payload] }
  let cert : SideConditionCertificate := { name := `cert, condition := condition, kind :=
    .builtinTrivial }
  let r : RuleSchema := RuleSchema.mk `dup_side_condition_rule [] [] [condition, condition]
    [{ name := `side1, condition := condition }, { name := `side2, condition := condition }]
    [cert, { cert with name := `cert2 }]
    (.custom `J [])
  let sig : Signature := { name := `T, rules := [r] }
  let d := KernelLFDerivation.ruleApp `dup_side_condition_rule (.custom `J []) {} [] [`cert, `cert2]
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J []) with
  | .ok _ => false
  | .error err => err.contains "duplicate side-condition name 'side'"

#guard
  let condition : SideCondition := { name := `side, args := [.tmConst `payload] }
  let cert : SideConditionCertificate := { name := `cert, condition := condition, kind :=
    .builtinTrivial }
  let r : RuleSchema := RuleSchema.mk `dup_side_condition_slot_rule [] [] [condition,
    { condition with name := `other }]
    [{ name := `slot, condition := condition }, { name := `slot, condition :=
      { condition with name := `other } }]
    [cert, { cert with name := `cert2, condition := { condition with name := `other } }]
    (.custom `J [])
  let sig : Signature := { name := `T, rules := [r] }
  let d := KernelLFDerivation.ruleApp `dup_side_condition_slot_rule (.custom `J []) {} [] [`cert,
    `cert2]
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J []) with
  | .ok _ => false
  | .error err => err.contains "duplicate side-condition certificate slot name 'slot'"

#guard
  let condition₁ : SideCondition := { name := `side1, args := [.tmConst `payload1] }
  let condition₂ : SideCondition := { name := `side2, args := [.tmConst `payload2] }
  let cert₁ : SideConditionCertificate := { name := `cert1, condition := condition₁, kind :=
    .builtinTrivial }
  let cert₂ : SideConditionCertificate := { name := `cert2, condition := condition₁, kind :=
    .builtinTrivial }
  let r : RuleSchema := RuleSchema.mk `missing_matching_side_cert_rule [] [] [condition₁,
    condition₂]
    [{ name := `slot1, condition := condition₁ }, { name := `slot2, condition := condition₂ }]
    [cert₁, cert₂]
    (.custom `J [])
  let sig : Signature := { name := `T, rules := [r] }
  let d :=
    KernelLFDerivation.ruleApp `missing_matching_side_cert_rule (.custom `J []) {} [] [`cert1,
    `cert2]
  match KernelLFDerivation.checkWithContext {} sig d (.custom `J []) with
  | .ok _ => false
  | .error err =>
    err.contains "side-condition certificate slot 'slot1' with multiple matching checked \
      certificates" ||
      err.contains "side-condition certificate slot 'slot2' with no matching checked certificate"

#guard
  let r : RuleSchema := RuleSchema.mk `bind_rule
    [{ name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun) }]
    [] [] [] [] (.custom `J [.leanParam `F])
  let badValue := Raw.scopedBind `ordinary `missing_var `x (.tyConst `Tm) (.leanParam `x)
  let entry : ScopedInstantiationEntry := {
    name := `F
    sort := .custom `Fun
    type? := some (.tyConst `Fun)
    value := badValue
  }
  let inst : ScopedInstantiation := { entries := [entry] }
  let zone : ContextZoneSchema := { name := `ordinary, sort := .custom `Ctx }
  let sig : Signature := { name := `T, contextZones := [zone], rules := [r] }
  match KernelLFDerivation.validateRuleApplicationAgainstRule sig `bind_rule r (.custom `J
    [badValue]) inst 0 [] with
  | .ok _ => false
  | .error err => err.contains "unknown binder class 'missing_var'"

#guard
  let r : RuleSchema := RuleSchema.mk `ctx_rule
    [{ name := `Γ, sort := .custom `Ctx, zone? := some `ordinary, type? := some (.tyConst `Ctx) }]
    [] [] [] [] (.custom `J [.leanParam `Γ])
  let inst : ScopedInstantiation := { entries := [
    { name := `Γ, sort := .custom `Ctx, zone? := some `ordinary, type? := some (.tyConst `Ctx),
      value := .tmConst `emptyCtx }] }
  let zones : List ContextZoneSchema := [
    { name := `ordinary, sort := .custom `Ctx },
    { name := `ordinary, sort := .custom `Ctx }]
  let sig : Signature := { name := `T, contextZones := zones, rules := [r] }
  match KernelLFDerivation.validateRuleApplicationAgainstRule sig `ctx_rule r (.custom `J [.tmConst
    `emptyCtx]) inst 0 [] with
  | .ok _ => false
  | .error err => err.contains "duplicate context-zone schema 'ordinary'"

#guard
  let metas : List RuleMetaVar := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun) }]
  let value := Raw.scopedBind `ordinary `ordinary_var `x (.tyConst `Tm) (.leanParam `x)
  let inst : ScopedInstantiation := { entries := [
    { name := `F, sort := .custom `Fun, type? := some (.tyConst `Fun), value := value }] }
  match inst.validateAgainstWithSignature []
      [{ name := `ordinary, sort := .custom `Ctx }]
      [{ name := `ordinary_var, zone := `ordinary, boundSort := .custom `Tm },
       { name := `ordinary_var, zone := `ordinary, boundSort := .custom `Tm }]
      metas with
  | .ok _ => false
  | .error err => err.contains "ambiguous binder class 'ordinary_var'"

#guard
  let r : RuleSchema := RuleSchema.mk `dup_rule [] [] [] [] [] (.custom `J [])
  let sig : Signature := { name := `T, rules := [r, r] }
  match KernelLFDerivation.checkWithContext {} sig (.ruleApp `dup_rule (.custom `J []) {} [] []) (
    .custom `J []) with
  | .ok _ => false
  | .error err => err.contains "duplicate rule schemas"

#guard
  let stmt := Judgment.custom `J [.tmConst `a]
  let recorded := Judgment.custom `J [.tmConst `b]
  let ctx : KernelLFCheckContext := { theorems := [{ name := `thm, statement := recorded }] }
  match KernelLFDerivation.checkWithContext ctx { name := `T } (.theoremRef `thm stmt) stmt with
  | .ok _ => false
  | .error _ => true

#guard
  let stmt := Judgment.custom `J [.tmConst `a]
  let ctx : KernelLFCheckContext := {}
  match KernelLFDerivation.checkWithContext ctx { name := `T } (.theoremRef `missing stmt) stmt with
  | .ok _ => false
  | .error err => err.contains "theorem reference 'missing' is not available"

#guard
  let stmt := Judgment.custom `J [.tmConst `a]
  let ctx : KernelLFCheckContext := { theorems := [
    { name := `thm, statement := stmt },
    { name := `thm, statement := stmt }] }
  match KernelLFDerivation.checkWithContext ctx { name := `T } (.theoremRef `thm stmt) stmt with
  | .ok _ => false
  | .error err => err.contains "duplicate theorem entries"

#guard
  let stmt := Judgment.custom `J [.tmConst `a]
  let recorded := Judgment.custom `J [.tmConst `b]
  let ctx : KernelLFCheckContext := {
    certificates := [{ name := `cert, statement := recorded, certificateName := `expected }] }
  match KernelLFDerivation.checkWithContext ctx { name := `T }
    (.certificate `cert stmt `expected) stmt with
  | .ok _ => false
  | .error _ => true

#guard
  let stmt := Judgment.custom `J [.tmConst `a]
  let ctx : KernelLFCheckContext := {}
  match KernelLFDerivation.checkWithContext ctx { name := `T }
    (.certificate `missing stmt `expected) stmt with
  | .ok _ => false
  | .error err => err.contains "certificate-backed derivation 'missing' is not available"

#guard
  let stmt := Judgment.custom `J [.tmConst `a]
  let ctx : KernelLFCheckContext := {
    certificates := [
      { name := `cert, statement := stmt, certificateName := `expected },
      { name := `cert, statement := stmt, certificateName := `expected }] }
  match KernelLFDerivation.checkWithContext ctx { name := `T }
    (.certificate `cert stmt `expected) stmt with
  | .ok _ => false
  | .error err => err.contains "duplicate entries"

#guard
  let stmt := Judgment.custom `J [.tmConst `a]
  let ctx : KernelLFCheckContext := {
    certificates := [{ name := `cert, statement := stmt, certificateName := `expected }] }
  match KernelLFDerivation.checkWithContext ctx { name := `T }
    (.certificate `cert stmt `actual) stmt with
  | .ok _ => false
  | .error _ => true

#guard
  let lhs := Raw.tmApp `_app [.tmApp `lam [.leanParam `x, .leanParam `x], .tmConst `a]
  let stmt : ConversionStatement := { plugin := `conv, lhs := lhs, rhs := .tmConst `a }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .executableChecked, supportedSteps := [.beta] }] }
  match KernelLFConversionCertificate.check sig (.pluginStep stmt .beta none [] "") stmt with
  | .ok _ => true
  | .error _ => false

#guard
  let stmt : ConversionStatement := { plugin := `conv, lhs := .tmConst `a, rhs := .tmConst `b }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .executableChecked, supportedSteps := [.beta] }] }
  match KernelLFConversionCertificate.checkDetailed sig
      (.pluginStep stmt .beta none [] "") stmt with
  | .ok _ => false
  | .error err =>
      err.kind == .malformedCertificate && err.message.contains "expected a raw `_app` redex"

#guard
  let stmt : ConversionStatement := { plugin := `conv, lhs := .tmConst `a, rhs := .tmConst `b }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .executableChecked, supportedSteps := [.eta] }] }
  match KernelLFConversionCertificate.checkDetailed sig
      (.pluginStep stmt .beta none [] "") stmt with
  | .ok _ => false
  | .error err =>
      err.kind == .unsupportedConversion && err.message.contains "does not support step 'beta'"

#guard
  let stmt : ConversionStatement := { plugin := `conv, lhs := .tmConst `a, rhs := .tmConst `b }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .opaqueAssumption, supportedSteps := [.pluginAxiom] }] }
  match KernelLFConversionCertificate.check sig (.pluginStep stmt .pluginAxiom none []
    "trusted by external profile") stmt with
  | .ok _ => true
  | .error _ => false

#guard
  let stmt : ConversionStatement := { plugin := `conv, lhs := .tmConst `a, rhs := .tmConst `b }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .opaqueAssumption, supportedSteps := [.pluginAxiom] }] }
  match KernelLFConversionCertificate.checkDetailed sig
      (.pluginStep stmt .pluginAxiom none [] "") stmt with
  | .ok _ => false
  | .error err =>
      err.kind == .opaquePlugin && err.message.contains "requires a visible nonempty payload"

#guard
  let stmt : ConversionStatement := { plugin := `conv, lhs := .tmConst `a, rhs := .tmConst `b }
  let ctx : KernelLFCheckContext := { conversionCertificates := [
    { certificateName := `cert, statement := stmt, stepKind := .reindexing }] }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .externalCertificate, supportedSteps := [.reindexing] }] }
  match KernelLFConversionCertificate.checkWithContext ctx sig (.pluginStep stmt .reindexing (some
    `cert) [] "") stmt with
  | .ok _ => true
  | .error _ => false

#guard
  let stmt : ConversionStatement := { plugin := `conv, lhs := .tmConst `a, rhs := .tmConst `b }
  let wrongStmt : ConversionStatement := { plugin := `conv, lhs := .tmConst `a, rhs := .tmConst `c }
  let ctx : KernelLFCheckContext := { conversionCertificates := [
    { certificateName := `cert, statement := wrongStmt, stepKind := .reindexing }] }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .externalCertificate, supportedSteps := [.reindexing] }] }
  match KernelLFConversionCertificate.checkWithContext ctx sig (.pluginStep stmt .reindexing (some
    `cert) [] "") stmt with
  | .ok _ => false
  | .error err => err.contains "certifies statement"

#guard
  let stmt : ConversionStatement := { plugin := `conv, lhs := .tmConst `a, rhs := .tmConst `b }
  let ctx : KernelLFCheckContext := {
    certificates := [{ name := `side, statement := .custom `J [.tmConst `a], certificateName :=
      `sideCert }] }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .executableChecked, supportedSteps := [.sideCondition] }] }
  match KernelLFConversionCertificate.checkWithContextDetailed ctx sig
      (.pluginStep stmt .sideCondition none [`sideCert] "") stmt with
  | .ok _ => false
  | .error err =>
      err.kind == .unsupportedConversion &&
        err.message.contains "no generic executable engine for step 'side_condition'"

#guard
  let stmt : ConversionStatement := { plugin := `conv, lhs := .tmConst `a, rhs := .tmConst `b }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .executableChecked, supportedSteps := [.sideCondition] }] }
  match KernelLFConversionCertificate.check sig (.pluginStep stmt .sideCondition none
    [`missingCert] "") stmt with
  | .ok _ => false
  | .error err => err.contains "references unavailable side-condition certificate"

#guard
  let stmt : ConversionStatement := { plugin := `conv, lhs := .tmConst `a, rhs := .tmConst `b }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .executableChecked, supportedSteps := [.beta] }] }
  match KernelLFConversionCertificate.check sig (.refl stmt) stmt with
  | .ok _ => false
  | .error err => err.contains "non-identical endpoints"

#guard
  let stmt : ConversionStatement := {
    plugin := `structural, lhs := .tmConst `a, rhs := .tmConst `a }
  let sig : Signature := { name := `T }
  match CheckedKernelLFConversionCertificate.check sig {} stmt (.refl stmt) with
  | .ok checked => checked.statement == stmt
  | .error _ => false

#guard
  let eqHead : CheckedLFHead := { name := `eqTm, kind := .judgment }
  let checked : CheckedSignature := {
    name := `RoleSmoke,
    lfSyntaxSortRoles := #[{ sortName := `Tm, kind := `term_sort }],
    lfJudgmentRoles := #[{ judgmentName := `eqTm, kind := `term_conversion }],
    lfJudgments := #[{ name := `eqTm }],
    lfRuleRoles := #[{ ruleName := `beta, kind := `computation }],
    lfRewriteRelations := #[{ relationName := `eqTm, lhsParam := `t, rhsParam := `u }],
    lfTransportRules := #[{
      ruleName := `transport, relationName := `eqTm,
      evidencePremise := `e, sourcePremise := `src }],
    lfRules := #[{ name := `beta, conclusionExpr := .ident `eqTm, conclusionHead := eqHead }] }
  let profile := checked.roleAutomationProfile
  checked.syntaxSortRoleKinds `Tm == #[`term_sort] &&
    checked.judgmentHasConversionClass `eqTm .termConversion &&
    checked.ruleHasAutomationClass `beta .computation &&
    profile.rewriteCandidateRules == #[`beta] &&
    profile.evidenceRewriteRelations == #[`eqTm] &&
    profile.evidenceTransportRules == #[`transport]

#guard
  let eqHead : CheckedLFHead := { name := `wfTm, kind := .judgment }
  let checked : CheckedSignature := {
    name := `AmbiguousRoleSmoke,
    lfRuleRoles := #[
      { ruleName := `bad, kind := `introduction },
      { ruleName := `bad, kind := `elimination }],
    lfRules := #[{ name := `bad, conclusionExpr := .ident `wfTm, conclusionHead := eqHead }] }
  let profile := checked.roleAutomationProfile
  profile.diagnostics.any fun d =>
    d.kind == .ambiguous && d.declaration? == some `bad &&
      d.message.contains "multiple automation roles"

declare_type_theory LogicalFrameworkSmoke where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  syntax_sort Tm (Γ : Ctx) (A : Ty Γ)
  syntax_sort_role Ctx : context
  syntax_sort_role Ty : type_sort
  syntax_sort_role Tm : term_sort
  context_zone ordinary : Ctx
  context_zone dependent : Ctx depends_on ordinary
  binder_class ordinary_var : Tm in ordinary
  binder_class dependent_var : Tm in dependent depends_on ordinary

  judgment wfCtx (Γ : Ctx)
  judgment wfTy (Γ : Ctx) (A : Ty Γ)
  judgment wfTm (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A)
  judgment eqTm (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A) (u : Tm Γ A)
  judgment_role wfCtx : context_wellformedness
  judgment_role wfTy : type_formation
  judgment_role wfTm : term_typing
  judgment_role eqTm : term_conversion
  rewrite_relation eqTm [t, u]

  rule ty_refl (Γ : Ctx) (A : Ty Γ) : wfTy Γ A
  rule_role ty_refl : formation
  side_condition_solver toy_side_condition
  side_condition_solver trivial_side_condition
  conversion_plugin toy_conversion
  conversion_plugin toy_external external_certificate
  conversion_plugin toy_checked executable
  conversion_plugin toy_beta executable [beta]

  rule checked_tm (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A) where
    premise ctx : wfCtx Γ
    premise ty : wfTy Γ A
    side_condition toy by toy_side_condition : wfTm Γ A t
    conclusion : wfTm Γ A t
  rule_role checked_tm : introduction

  rule checked_tm_builtin (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A) where
    premise ctx : wfCtx Γ
    premise ty : wfTy Γ A
    side_condition trivial by trivial_side_condition : wfTm Γ A t
    conclusion : wfTm Γ A t
  rule_role checked_tm_builtin : introduction

  rule tm_refl_eq (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A) where
    premise tm : wfTm Γ A t
    conclusion : eqTm Γ A t t
  rule_role tm_refl_eq : computation

  rule eqTm_symm (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A) (u : Tm Γ A) where
    premise e : eqTm Γ A t u
    conclusion : eqTm Γ A u t
  rewrite_symmetry eqTm_symm for eqTm [e]

  rule eqTm_transport (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A) (u : Tm Γ A) where
    premise e : eqTm Γ A t u
    premise src : wfTm Γ A t
    conclusion : wfTm Γ A u
  rule_role eqTm_transport : elimination
  transport_rule eqTm_transport for eqTm [e, src]
  transport_position eqTm_transport : wfTm [2]

#print_type_theories
#print_type_theory LogicalFrameworkSmoke
#print_logical_framework_metadata LogicalFrameworkSmoke
#print_logical_framework_roles LogicalFrameworkSmoke
#check_type_theory LogicalFrameworkSmoke
#print_lf_role_automation LogicalFrameworkSmoke
#print_lf_rewrite_metadata LogicalFrameworkSmoke
#print_checked_logical_framework_environment LogicalFrameworkSmoke
#print_logical_framework_rule_schemas LogicalFrameworkSmoke
#print_logical_framework_kernel_rule_schemas LogicalFrameworkSmoke
#print_logical_framework_context_zones LogicalFrameworkSmoke

/-- error: transport_position 'tr' in type theory 'BadLFTransportPositionSameArgument'
does not change argument 1 of 'Rel' -/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFTransportPositionSameArgument where
  syntax_sort Obj
  judgment Rel (x : Obj) (y : Obj)
  judgment EqObj (x : Obj) (y : Obj)
  rewrite_relation EqObj [x, y]
  rule tr (x : Obj) (y : Obj) (z : Obj) where
    premise e : EqObj x y
    premise source : Rel y z
    conclusion : Rel x z
  transport_rule tr for EqObj [e, source]
  transport_position tr : Rel [1]

/-- error: rewrite_symmetry 'symm' in type theory 'BadLFRewriteSymmetryNoSwap'
does not swap endpoints 'x' and 'y' -/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFRewriteSymmetryNoSwap where
  syntax_sort Obj
  judgment EqObj (x : Obj) (y : Obj)
  rewrite_relation EqObj [x, y]
  rule symm (x : Obj) (y : Obj) where
    premise e : EqObj x y
    conclusion : EqObj x y
  rewrite_symmetry symm for EqObj [e]

/-- error: rewrite_congruence 'congr' in type theory 'BadLFRewriteCongruenceNoLift'
does not lift endpoints through 'f[0]' -/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFRewriteCongruenceNoLift where
  syntax_sort Obj
  judgment EqObj (x : Obj) (y : Obj)
  rewrite_relation EqObj [x, y]
  lf_opaque f (x : Obj) : Obj
  rule congr (x : Obj) (y : Obj) where
    premise e : EqObj x y
    conclusion : EqObj (f x) (f x)
  rewrite_congruence congr for EqObj under f [0] [e]

#print_logical_framework_side_condition_hooks LogicalFrameworkSmoke

declare_type_theory Phase4TwoLayerSmoke where
  syntax_sort CubeCtx
  syntax_sort CubeTm (Ξ : CubeCtx)
  syntax_sort TyCtx (Ξ : CubeCtx)
  syntax_sort Ty (Ξ : CubeCtx) (Γ : TyCtx Ξ)
  context_zone cube : CubeCtx
  context_zone typeZone : TyCtx depends_on cube
  binder_class cube_var : CubeTm in cube
  binder_class type_var : Ty in typeZone depends_on cube
  judgment wfCubeCtx (Ξ : CubeCtx)
  judgment wfTyCtx (Ξ : CubeCtx) (Γ : TyCtx Ξ)
  judgment wfTy (Ξ : CubeCtx) (Γ : TyCtx Ξ) (A : Ty Ξ Γ)
  rule two_layer_rule (Ξ : CubeCtx) (Γ : TyCtx Ξ) (A : Ty Ξ Γ) where
    premise cube_ok : wfCubeCtx Ξ
    premise ctx_ok : wfTyCtx Ξ Γ
    conclusion : wfTy Ξ Γ A

#check_type_theory Phase4TwoLayerSmoke
#print_logical_framework_context_zones Phase4TwoLayerSmoke
#print_logical_framework_rule_schemas Phase4TwoLayerSmoke

/- Object-level substitution can be declared as ordinary LF syntax and judgments;
raw `Raw.subst*` constructors are a separate low-level replay syntax. -/
declare_type_theory LFObjectSubstitutionJudgmentSmoke where
  syntax_sort Ctx
  syntax_sort Subst (Δ : Ctx) (Γ : Ctx)

  syntax_sort_role Ctx : context
  syntax_sort_role Subst : substitution

  judgment wfCtx (Γ : Ctx)
  judgment wfSubst (Δ : Ctx) (Γ : Ctx) (σ : Subst Δ Γ)

  judgment_role wfCtx : context_wellformedness
  judgment_role wfSubst : substitution_wellformedness

  lf_opaque emptyCtx : Ctx
  lf_opaque idSubst (Γ : Ctx) : Subst Γ Γ

  rule empty_ctx where
    conclusion : wfCtx emptyCtx

  rule id_subst (Γ : Ctx) where
    premise ctx : wfCtx Γ
    conclusion : wfSubst Γ Γ (idSubst Γ)

#check_type_theory LFObjectSubstitutionJudgmentSmoke
#print_logical_framework_metadata LFObjectSubstitutionJudgmentSmoke

/- Rule-parameter evidence surfaces the low-level scoped-instantiation evidence lane.
Here `σ` is still ordinary object-level LF syntax (`Subst Γ Γ`). The `evidence` item is
also a named premise, so theorem proofs must supply a derivation of the instantiated
judgment that is recorded on the kernel replay entry. -/
declare_type_theory LFRuleParameterEvidenceSmoke where
  syntax_sort Ctx
  syntax_sort Subst (Δ : Ctx) (Γ : Ctx)
  judgment wfSubst (Δ : Ctx) (Γ : Ctx) (σ : Subst Δ Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque idSubst (Γ : Ctx) : Subst Γ Γ

  rule id_subst_empty : wfSubst emptyCtx emptyCtx (idSubst emptyCtx)

  rule subst_evidence_rule (Γ : Ctx) (σ : Subst Γ Γ) where
    evidence σ_wf for σ : wfSubst Γ Γ σ
    conclusion : wfSubst Γ Γ σ

  judgment_theorem id_subst_empty_thm : wfSubst emptyCtx emptyCtx (idSubst emptyCtx) :=
    id_subst_empty

  judgment_theorem subst_evidence_replay : wfSubst emptyCtx emptyCtx (idSubst emptyCtx) :=
    subst_evidence_rule emptyCtx (idSubst emptyCtx) id_subst_empty

  judgment_theorem subst_evidence_replay_by_theorem :
    wfSubst emptyCtx emptyCtx (idSubst emptyCtx) :=
    subst_evidence_rule emptyCtx (idSubst emptyCtx) id_subst_empty_thm

#check_type_theory LFRuleParameterEvidenceSmoke
#print_logical_framework_definitions LFRuleParameterEvidenceSmoke

/- Locally quantified `judgment_theorem`s expose LF parameters and theorem assumptions to
statement/proof replay.  The last theorem is dependent-context-shaped: it is replayed under an
extended context and uses a declared term variable plus a local typing hypothesis. -/
declare_type_theory LFLocalTheoremReplaySmoke where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  syntax_sort Tm (Γ : Ctx) (A : Ty Γ)
  context_zone ordinary : Ctx
  binder_class ordinary_var : Tm in ordinary
  judgment wfCtx (Γ : Ctx)
  judgment wfTy (Γ : Ctx) (A : Ty Γ)
  judgment wfTm (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A)
  lf_opaque ext (Γ : Ctx) (A : Ty Γ) : Ctx

  rule ctx_ext (Γ : Ctx) (A : Ty Γ) where
    premise ctx : wfCtx Γ
    premise ty : wfTy Γ A
    conclusion : wfCtx (ext Γ A)

  rule tm_from_hyp (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A) where
    premise hyp : wfTm Γ A t
    conclusion : wfTm Γ A t

  judgment_theorem local_ctx_ext (Γ : Ctx) (A : Ty Γ)
      (Γ_ok : wfCtx Γ) (A_ok : wfTy Γ A) : wfCtx (ext Γ A) :=
    ctx_ext Γ A Γ_ok A_ok

  judgment_theorem local_hyp_direct (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A)
      (h : wfTm Γ A t) : wfTm Γ A t :=
    h

  judgment_theorem local_hyp_as_rule_premise (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A)
      (h : wfTm Γ A t) : wfTm Γ A t :=
    tm_from_hyp Γ A t h

  judgment_theorem local_hyp_by_theorem (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A)
      (h : wfTm Γ A t) : wfTm Γ A t :=
    local_hyp_direct Γ A t h

  judgment_theorem local_tm_in_extended_context (Γ : Ctx) (A : Ty Γ) (B : Ty (ext Γ A))
      (x : Tm (ext Γ A) B) (x_ok : wfTm (ext Γ A) B x) : wfTm (ext Γ A) B x :=
    x_ok

#check_type_theory LFLocalTheoremReplaySmoke
#print_logical_framework_definitions LFLocalTheoremReplaySmoke
generate_lf_model_structure LFLocalTheoremReplaySmoke as LFLocalTheoremReplayModel
#print_lf_model_derived_statements LFLocalTheoremReplaySmoke for LFLocalTheoremReplayModel
#print_lf_model_derived_theorems LFLocalTheoremReplaySmoke for LFLocalTheoremReplayModel
#check_lf_model_derived_theorems LFLocalTheoremReplaySmoke for LFLocalTheoremReplayModel
generate_lf_model_derived_theorems LFLocalTheoremReplaySmoke for LFLocalTheoremReplayModel
#check LFLocalTheoremReplaySmoke.LFLocalTheoremReplayModel.local_ctx_ext
#check LFLocalTheoremReplaySmoke.LFLocalTheoremReplayModel.local_hyp_by_theorem
#check LFLocalTheoremReplaySmoke.LFLocalTheoremReplayModel.local_tm_in_extended_context

/-- error: judgment_theorem 'bad' in type theory 'BadLFLocalTheoremNonJudgmentProof' uses local
parameter 'Γ' as a proof, but that local is not a judgment assumption -/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFLocalTheoremNonJudgmentProof where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  judgment_theorem bad (Γ : Ctx) : wfCtx Γ := Γ

/-- error: judgment_theorem 'bad' in type theory 'BadLFLocalTheoremAssumptionMismatch' uses local
theorem assumption 'h' with statement 'wfCtx Γ', expected 'wfTy Γ A' -/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFLocalTheoremAssumptionMismatch where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  judgment wfCtx (Γ : Ctx)
  judgment wfTy (Γ : Ctx) (A : Ty Γ)
  judgment_theorem bad (Γ : Ctx) (A : Ty Γ) (h : wfCtx Γ) : wfTy Γ A := h

/-- error: judgment_theorem 'bad_replay' supplied 0 trailing proof/certificate argument(s) to
application 'subst_evidence_rule' in proof, expected 1 -/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFRuleEvidenceMissingProof where
  syntax_sort Ctx
  syntax_sort Subst (Δ : Ctx) (Γ : Ctx)
  judgment wfSubst (Δ : Ctx) (Γ : Ctx) (σ : Subst Δ Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque idSubst (Γ : Ctx) : Subst Γ Γ
  rule subst_evidence_rule (Γ : Ctx) (σ : Subst Γ Γ) where
    evidence σ_wf for σ : wfSubst Γ Γ σ
    conclusion : wfSubst Γ Γ σ
  judgment_theorem bad_replay : wfSubst emptyCtx emptyCtx (idSubst emptyCtx) :=
    subst_evidence_rule emptyCtx (idSubst emptyCtx)

/-- error: judgment_theorem 'bad_replay' in type theory 'BadLFRuleEvidenceFutureTheoremProof' uses
premise theorem 'id_subst_empty_thm' before it is available -/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFRuleEvidenceFutureTheoremProof where
  syntax_sort Ctx
  syntax_sort Subst (Δ : Ctx) (Γ : Ctx)
  judgment wfSubst (Δ : Ctx) (Γ : Ctx) (σ : Subst Δ Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque idSubst (Γ : Ctx) : Subst Γ Γ
  rule id_subst_empty : wfSubst emptyCtx emptyCtx (idSubst emptyCtx)
  rule subst_evidence_rule (Γ : Ctx) (σ : Subst Γ Γ) where
    evidence σ_wf for σ : wfSubst Γ Γ σ
    conclusion : wfSubst Γ Γ σ
  judgment_theorem bad_replay : wfSubst emptyCtx emptyCtx (idSubst emptyCtx) :=
    subst_evidence_rule emptyCtx (idSubst emptyCtx) id_subst_empty_thm
  judgment_theorem id_subst_empty_thm : wfSubst emptyCtx emptyCtx (idSubst emptyCtx) :=
    id_subst_empty

/--
error: judgment_theorem 'bad_replay' in type theory 'BadLFRuleEvidenceTheoremStatementMismatch' uses
premise theorem 'other_subst_thm' with statement 'wfSubst emptyCtx emptyCtx otherSubst', expected
'wfSubst emptyCtx emptyCtx (idSubst emptyCtx)'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFRuleEvidenceTheoremStatementMismatch where
  syntax_sort Ctx
  syntax_sort Subst (Δ : Ctx) (Γ : Ctx)
  judgment wfSubst (Δ : Ctx) (Γ : Ctx) (σ : Subst Δ Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque idSubst (Γ : Ctx) : Subst Γ Γ
  lf_opaque otherSubst : Subst emptyCtx emptyCtx
  rule other_subst : wfSubst emptyCtx emptyCtx otherSubst
  rule subst_evidence_rule (Γ : Ctx) (σ : Subst Γ Γ) where
    evidence σ_wf for σ : wfSubst Γ Γ σ
    conclusion : wfSubst Γ Γ σ
  judgment_theorem other_subst_thm : wfSubst emptyCtx emptyCtx otherSubst :=
    other_subst
  judgment_theorem bad_replay : wfSubst emptyCtx emptyCtx (idSubst emptyCtx) :=
    subst_evidence_rule emptyCtx (idSubst emptyCtx) other_subst_thm

/--
error: judgment_theorem 'bad_replay' in type theory 'BadLFRuleEvidenceWrongContextProof' uses
premise theorem 'other_subst_thm' with statement 'wfSubst otherCtx otherCtx (idSubst otherCtx)',
expected 'wfSubst emptyCtx emptyCtx (idSubst emptyCtx)'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFRuleEvidenceWrongContextProof where
  syntax_sort Ctx
  syntax_sort Subst (Δ : Ctx) (Γ : Ctx)
  judgment wfSubst (Δ : Ctx) (Γ : Ctx) (σ : Subst Δ Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque otherCtx : Ctx
  lf_opaque idSubst (Γ : Ctx) : Subst Γ Γ
  rule other_subst : wfSubst otherCtx otherCtx (idSubst otherCtx)
  rule subst_evidence_rule (Γ : Ctx) (σ : Subst Γ Γ) where
    evidence σ_wf for σ : wfSubst Γ Γ σ
    conclusion : wfSubst Γ Γ σ
  judgment_theorem other_subst_thm : wfSubst otherCtx otherCtx (idSubst otherCtx) :=
    other_subst
  judgment_theorem bad_replay : wfSubst emptyCtx emptyCtx (idSubst emptyCtx) :=
    subst_evidence_rule emptyCtx (idSubst emptyCtx) other_subst_thm

/-- error: rule 'bad' in type theory 'BadLFRuleEvidenceUnknownParam' has evidence for unknown
parameter 'σ' -/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFRuleEvidenceUnknownParam where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  rule bad (Γ : Ctx) where
    evidence σ_wf for σ : wfCtx Γ
    conclusion : wfCtx Γ

/-- error: rule 'bad' in type theory 'BadLFRuleEvidenceLaterParam' has evidence for parameter 'σ'
referencing later parameter 'Γ' -/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFRuleEvidenceLaterParam where
  syntax_sort Ctx
  syntax_sort Subst (Δ : Ctx) (Γ : Ctx)
  judgment wfSubst (Δ : Ctx) (Γ : Ctx) (σ : Subst Δ Γ)
  lf_opaque emptyCtx : Ctx
  rule bad (σ : Subst emptyCtx emptyCtx) (Γ : Ctx) where
    evidence σ_wf for σ : wfSubst Γ Γ σ
    conclusion : wfSubst emptyCtx emptyCtx σ

declare_type_theory LFShapeDefinitionTheoremSmoke where
  side_condition_solver trivial_side_condition
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque simplexPayload : Shape emptyCtx
  lf_opaque boundaryPayload : Shape emptyCtx
  lf_opaque incl_input / 2
  lf_def Simplex : Shape emptyCtx := simplexPayload
  lf_def Boundary : Shape emptyCtx := boundaryPayload
  rule boundary_in_simplex_rule where
    side_condition ok by trivial_side_condition : incl_input Boundary Simplex
    conclusion : shapeIncl emptyCtx Boundary Simplex
  judgment_theorem boundary_in_simplex : shapeIncl emptyCtx Boundary Simplex :=
    boundary_in_simplex_rule

#check_type_theory LFShapeDefinitionTheoremSmoke
#print_checked_type_theory LFShapeDefinitionTheoremSmoke
#print_logical_framework_definitions LFShapeDefinitionTheoremSmoke

declare_type_theory TypedExtensionFormerLFSmoke where
  side_condition_solver trivial_side_condition
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  syntax_sort Ty (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque simplexPayload : Shape emptyCtx
  lf_opaque boundaryPayload : Shape emptyCtx
  lf_opaque Ext (Γ : Ctx) (S : Shape Γ) (T : Shape Γ) : Ty Γ
  lf_opaque incl_input / 2
  lf_def Simplex : Shape emptyCtx := simplexPayload
  lf_def Boundary : Shape emptyCtx := boundaryPayload
  rule boundary_in_simplex_rule where
    side_condition ok by trivial_side_condition : incl_input Boundary Simplex
    conclusion : shapeIncl emptyCtx Boundary Simplex
  judgment_theorem boundary_in_simplex : shapeIncl emptyCtx Boundary Simplex :=
    boundary_in_simplex_rule
  lf_def BoundaryExtension : Ty emptyCtx := Ext emptyCtx Boundary Simplex

#check_type_theory TypedExtensionFormerLFSmoke
#print_logical_framework_definitions TypedExtensionFormerLFSmoke

declare_type_theory LFInternalDefinitionSmoke where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_def Simplex : Shape emptyCtx := simplexPayload
  rule simplex_refl_rule where
    conclusion : shapeIncl emptyCtx Simplex Simplex
  judgment_theorem simplex_refl : shapeIncl emptyCtx Simplex Simplex := simplex_refl_rule

#check_type_theory LFInternalDefinitionSmoke
#print_logical_framework_definitions LFInternalDefinitionSmoke

declare_type_theory LFDefinitionReferenceTypeSmoke where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_def Simplex : Shape emptyCtx := simplexPayload
  lf_def SimplexAlias : Shape emptyCtx := Simplex
  rule simplex_alias_refl_rule where
    conclusion : shapeIncl emptyCtx SimplexAlias Simplex
  judgment_theorem simplex_alias_refl : shapeIncl emptyCtx SimplexAlias Simplex :=
    simplex_alias_refl_rule

#check_type_theory LFDefinitionReferenceTypeSmoke
#print_logical_framework_definitions LFDefinitionReferenceTypeSmoke

/--
error: lf_def 'BadLFDefinitionReferenceType' in type theory 'BadLFDefinitionReferenceType' has value
with type 'OtherShape emptyCtx', expected 'Shape emptyCtx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFDefinitionReferenceType where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  syntax_sort OtherShape (Γ : Ctx)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_opaque otherPayload / 0
  lf_def Other : OtherShape emptyCtx := otherPayload
  lf_def BadLFDefinitionReferenceType : Shape emptyCtx := Other

/--
error: lf_def 'Bad' in type theory 'BadLFNestedFutureDefinitionReference' references LF definition
'Later' before it is available in value
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFNestedFutureDefinitionReference where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_opaque wrap (S : Shape emptyCtx) : Shape emptyCtx
  lf_def Bad : Shape emptyCtx := wrap Later
  lf_def Later : Shape emptyCtx := simplexPayload

/--
error: judgment_theorem 'bad' in type theory 'BadLFJudgmentArgumentType' has statement for judgment
'shapeIncl' argument 'Other' with type 'OtherShape emptyCtx', expected 'Shape emptyCtx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFJudgmentArgumentType where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  syntax_sort OtherShape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque otherPayload / 0
  lf_opaque proofPayload / 0
  lf_def Other : OtherShape emptyCtx := otherPayload
  judgment_theorem bad : shapeIncl emptyCtx Other Other := proofPayload

/--
error: lf_def 'Bad' in type theory 'BadLFSyntaxSortArgumentType' has type for syntax_sort 'Shape'
argument 'Other' with type 'OtherCtx', expected 'Ctx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFSyntaxSortArgumentType where
  syntax_sort Ctx
  syntax_sort OtherCtx
  syntax_sort Shape (Γ : Ctx)
  lf_opaque otherCtxPayload / 0
  lf_opaque shapePayload / 0
  lf_def Other : OtherCtx := otherCtxPayload
  lf_def Bad : Shape Other := shapePayload

/--
error: lf_def 'Bad' in type theory 'BadLFConstructorApplicationSyntaxSortArgumentType' has type for
syntax_sort 'Shape' argument 'mkOther' with type 'OtherCtx', expected 'ObjCtx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFConstructorApplicationSyntaxSortArgumentType where
  syntax_sort ObjCtx
  syntax_sort OtherCtx
  syntax_sort Shape (Γ : ObjCtx)
  lf_opaque mkOther : OtherCtx
  lf_opaque shapePayload / 0
  lf_def Bad : Shape mkOther := shapePayload

/--
error: lf_def 'Bad' in type theory 'BadLFNestedConstructorApplicationSyntaxSortArgumentType' has
type for syntax_sort 'Shape' argument 'wrapOther mkOther' with type 'OtherCtx', expected 'ObjCtx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFNestedConstructorApplicationSyntaxSortArgumentType where
  syntax_sort ObjCtx
  syntax_sort OtherCtx
  syntax_sort Shape (Γ : ObjCtx)
  lf_opaque mkOther : OtherCtx
  lf_opaque wrapOther (x : OtherCtx) : OtherCtx
  lf_opaque shapePayload / 0
  lf_def Bad : Shape (wrapOther mkOther) := shapePayload

/--
error: lf_def 'Bad' in type theory 'BadLFConstructorInternalArgumentType' has type for syntax_sort
'Shape' argument 'wrapOther mkObj' for constructor 'wrapOther' parameter 'x' with type 'ObjCtx',
expected 'OtherCtx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFConstructorInternalArgumentType where
  syntax_sort ObjCtx
  syntax_sort OtherCtx
  syntax_sort Shape (Γ : ObjCtx)
  lf_opaque mkObj : ObjCtx
  lf_opaque wrapOther (x : OtherCtx) : OtherCtx
  lf_opaque shapePayload / 0
  lf_def Bad : Shape (wrapOther mkObj) := shapePayload

/--
error: rule 'bad' in type theory 'BadLFRuleParameterSyntaxSortArgumentType' has parameter 'S' type
for syntax_sort 'Shape' argument 'Γ' with type 'OtherCtx', expected 'Ctx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFRuleParameterSyntaxSortArgumentType where
  syntax_sort Ctx
  syntax_sort OtherCtx
  syntax_sort Shape (Γ : Ctx)
  judgment wfShape (Γ : Ctx) (S : Shape Γ)
  rule bad (Γ : OtherCtx) (S : Shape Γ) : wfShape Γ S

/--
error: judgment_theorem 'bad' in type theory 'BadLFRuleApplicationArgumentType' has proof argument
for rule 'ignore_shape' parameter 'A' argument 'Other' with type 'OtherShape emptyCtx', expected
'Shape emptyCtx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFRuleApplicationArgumentType where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  syntax_sort OtherShape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_opaque otherPayload / 0
  lf_def Simplex : Shape emptyCtx := simplexPayload
  lf_def Other : OtherShape emptyCtx := otherPayload
  rule ignore_shape (A : Shape emptyCtx) : shapeIncl emptyCtx Simplex Simplex
  judgment_theorem bad : shapeIncl emptyCtx Simplex Simplex := ignore_shape Other

declare_type_theory TypedLFOpaqueConstructorSmoke where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  lf_opaque emptyCtx : Ctx
  lf_opaque mkShape (Γ : Ctx) : Shape Γ
  lf_def Simplex : Shape emptyCtx := mkShape emptyCtx

#check_type_theory TypedLFOpaqueConstructorSmoke
#print_checked_logical_framework_metadata TypedLFOpaqueConstructorSmoke

/--
error: lf_opaque 'Bad' in type theory 'BadTypedLFOpaqueResultSyntaxSortArgumentType' has result type
for syntax_sort 'Shape' argument 'mkOther' with type 'OtherCtx', expected 'ObjCtx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadTypedLFOpaqueResultSyntaxSortArgumentType where
  syntax_sort ObjCtx
  syntax_sort OtherCtx
  syntax_sort Shape (Γ : ObjCtx)
  lf_opaque mkOther : OtherCtx
  lf_opaque Bad : Shape mkOther

/--
error: lf_def 'Bad' in type theory 'BadTypedLFOpaqueConstructorArgumentType' has value for
constructor 'mkShape' parameter 'Γ' argument 'mkOther' with type 'OtherCtx', expected 'ObjCtx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadTypedLFOpaqueConstructorArgumentType where
  syntax_sort ObjCtx
  syntax_sort OtherCtx
  syntax_sort Shape (Γ : ObjCtx)
  lf_opaque mkObj : ObjCtx
  lf_opaque mkOther : OtherCtx
  lf_opaque mkShape (Γ : ObjCtx) : Shape Γ
  lf_def Bad : Shape mkObj := mkShape mkOther

/--
error: lf_def 'Bad' omits explicit argument 'Γ' in application 'mkShape' in value
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadTypedLFOpaqueConstructorArity where
  syntax_sort ObjCtx
  syntax_sort Shape (Γ : ObjCtx)
  lf_opaque mkObj : ObjCtx
  lf_opaque mkShape (Γ : ObjCtx) : Shape Γ
  lf_def Bad : Shape mkObj := mkShape

/--
error: lf_def 'Bad' in type theory 'BadLFDefinitionValueType' has value with type 'OtherShape
mkObj', expected 'Shape mkObj'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFDefinitionValueType where
  syntax_sort ObjCtx
  syntax_sort Shape (Γ : ObjCtx)
  syntax_sort OtherShape (Γ : ObjCtx)
  lf_opaque mkObj : ObjCtx
  lf_opaque mkOtherShape (Γ : ObjCtx) : OtherShape Γ
  lf_def Bad : Shape mkObj := mkOtherShape mkObj

declare_type_theory LFRuleApplicationProofSmoke where
  side_condition_solver trivial_side_condition
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_opaque incl_input / 2
  lf_def Simplex : Shape emptyCtx := simplexPayload
  rule simplex_refl_rule where
    side_condition ok by trivial_side_condition : incl_input Simplex Simplex
    conclusion : shapeIncl emptyCtx Simplex Simplex
  judgment_theorem simplex_refl : shapeIncl emptyCtx Simplex Simplex := simplex_refl_rule

#check_type_theory LFRuleApplicationProofSmoke
#print_logical_framework_definitions LFRuleApplicationProofSmoke

declare_type_theory LFTheoremReferenceProofSmoke where
  side_condition_solver trivial_side_condition
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_opaque incl_input / 2
  lf_def Simplex : Shape emptyCtx := simplexPayload
  rule simplex_refl_rule where
    side_condition ok by trivial_side_condition : incl_input Simplex Simplex
    conclusion : shapeIncl emptyCtx Simplex Simplex
  judgment_theorem simplex_refl : shapeIncl emptyCtx Simplex Simplex := simplex_refl_rule
  judgment_theorem simplex_refl_again : shapeIncl emptyCtx Simplex Simplex := simplex_refl

#check_type_theory LFTheoremReferenceProofSmoke
#print_logical_framework_definitions LFTheoremReferenceProofSmoke
#print_lf_replay_trust_dependencies LFTheoremReferenceProofSmoke simplex_refl_again
#print_lf_replay_trust_summary LFTheoremReferenceProofSmoke

declare_type_theory LFNestedRuleApplicationProofSmoke where
  side_condition_solver trivial_side_condition
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_opaque incl_input / 2
  lf_def Simplex : Shape emptyCtx := simplexPayload
  rule simplex_refl_rule where
    side_condition ok by trivial_side_condition : incl_input Simplex Simplex
    conclusion : shapeIncl emptyCtx Simplex Simplex
  rule simplex_trans_rule (A : Shape emptyCtx) (B : Shape emptyCtx) (C : Shape emptyCtx) where
    premise left : shapeIncl emptyCtx A B
    premise right : shapeIncl emptyCtx B C
    conclusion : shapeIncl emptyCtx A C
  judgment_theorem simplex_nested : shapeIncl emptyCtx Simplex Simplex :=
    simplex_trans_rule Simplex Simplex Simplex simplex_refl_rule simplex_refl_rule

#check_type_theory LFNestedRuleApplicationProofSmoke
#print_logical_framework_definitions LFNestedRuleApplicationProofSmoke

declare_type_theory LFNestedTheoremReferencePremiseSmoke where
  side_condition_solver trivial_side_condition
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque simplexPayload : Shape emptyCtx
  lf_opaque incl_input / 2
  lf_def Simplex : Shape emptyCtx := simplexPayload
  rule simplex_refl_rule (S : Shape emptyCtx) (T : Shape emptyCtx) where
    side_condition ok by trivial_side_condition : incl_input S T
    conclusion : shapeIncl emptyCtx S T
  rule simplex_trans_rule (A : Shape emptyCtx) (B : Shape emptyCtx) (C : Shape emptyCtx) where
    premise left : shapeIncl emptyCtx A B
    premise right : shapeIncl emptyCtx B C
    conclusion : shapeIncl emptyCtx A C
  judgment_theorem simplex_refl : shapeIncl emptyCtx Simplex Simplex :=
    simplex_refl_rule Simplex Simplex
  judgment_theorem simplex_nested_by_theorems : shapeIncl emptyCtx Simplex Simplex :=
    simplex_trans_rule Simplex Simplex Simplex simplex_refl simplex_refl

#check_type_theory LFNestedTheoremReferencePremiseSmoke
#print_logical_framework_definitions LFNestedTheoremReferencePremiseSmoke
generate_lf_model_structure LFNestedTheoremReferencePremiseSmoke as
  LFNestedTheoremReferencePremiseModel
#print_lf_model_derived_theorems LFNestedTheoremReferencePremiseSmoke for
  LFNestedTheoremReferencePremiseModel
#check_lf_model_derived_theorems LFNestedTheoremReferencePremiseSmoke for
  LFNestedTheoremReferencePremiseModel
generate_lf_model_derived_theorems LFNestedTheoremReferencePremiseSmoke for
  LFNestedTheoremReferencePremiseModel
namespace LFNestedTheoremReferencePremiseSmoke

#check LFNestedTheoremReferencePremiseModel.simplex_nested_by_theorems

end LFNestedTheoremReferencePremiseSmoke

declare_type_theory UniverseLevelMetadataSmoke {u} where
  syntax_sort Obj (A : Type u)
  judgment Has (A : Type u) (x : Obj A)
  lf_opaque id {A : Type u} (x : Obj A) : Obj A
  rule has_id {A : Type u} (x : Obj A) : Has A (id x)

#check_type_theory UniverseLevelMetadataSmoke
#print_checked_logical_framework_environment UniverseLevelMetadataSmoke
generate_lf_model_structure UniverseLevelMetadataSmoke as UniverseLevelMetadataModel
#check UniverseLevelMetadataSmoke.UniverseLevelMetadataModel.Obj
#check UniverseLevelMetadataSmoke.UniverseLevelMetadataModel.id

declare_type_theory LFNestedFunctionDefUnfoldSmoke where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque simplexPayload : Shape emptyCtx
  lf_def Simplex : Shape emptyCtx := simplexPayload
  lf_def idShape : Shape emptyCtx ⇒ Shape emptyCtx := fun S => S
  rule simplex_refl_rule (S : Shape emptyCtx) where
    conclusion : shapeIncl emptyCtx S S
  rule simplex_trans_rule (A : Shape emptyCtx) (B : Shape emptyCtx) (C : Shape emptyCtx) where
    premise left : shapeIncl emptyCtx A B
    premise right : shapeIncl emptyCtx B C
    conclusion : shapeIncl emptyCtx A C
  judgment_theorem simplex_refl : shapeIncl emptyCtx Simplex Simplex :=
    simplex_refl_rule Simplex
  judgment_theorem nested_function_unfold : shapeIncl emptyCtx Simplex Simplex :=
    simplex_trans_rule (idShape Simplex) (idShape Simplex) (idShape Simplex)
      (simplex_refl_rule (idShape Simplex)) (simplex_refl_rule (idShape Simplex))

#check_type_theory LFNestedFunctionDefUnfoldSmoke
#print_logical_framework_definitions LFNestedFunctionDefUnfoldSmoke
generate_lf_model_structure LFNestedFunctionDefUnfoldSmoke as LFNestedFunctionDefUnfoldModel
#check_lf_model_derived_theorems LFNestedFunctionDefUnfoldSmoke for LFNestedFunctionDefUnfoldModel

/--
error: syntax_sort 'Obj' in type theory 'BadUndeclaredLFLevelParam' uses undeclared universe level
parameter 'u' in parameter 'A' type; declare it in the theory-level parameter list containing 'u' or
use a numeric level. Currently declared level parameter(s): none
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadUndeclaredLFLevelParam where
  syntax_sort Obj (A : Type u)

/--
error: judgment_theorem 'bad' in type theory 'BadLFDefinitionNormalizationMismatch' applies
rule 'simplex_refl_rule' but the statement does not match the rule conclusion after LF-definition
normalization:
LF-definition normalization could not match expressions.
actual: shapeIncl emptyCtx Alias Other
expected: shapeIncl emptyCtx Alias Alias
normalized actual: shapeIncl emptyCtx simplexPayload otherPayload
normalized expected: shapeIncl emptyCtx simplexPayload simplexPayload
LF definitions mentioned before unfolding: Alias, Other
LF definitions unfolded: Alias, Other
Normalization policy: LF matching unfolds earlier checked `lf_def` values, beta-reduces
explicit LF lambdas, contracts structural eta-redexes, and alpha-renames binders
to avoid local-binder capture.
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFDefinitionNormalizationMismatch where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx : Ctx
  lf_opaque simplexPayload : Shape emptyCtx
  lf_opaque otherPayload : Shape emptyCtx
  lf_def Alias : Shape emptyCtx := simplexPayload
  lf_def Other : Shape emptyCtx := otherPayload
  rule simplex_refl_rule (S : Shape emptyCtx) where
    conclusion : shapeIncl emptyCtx S S
  judgment_theorem bad : shapeIncl emptyCtx Alias Other := simplex_refl_rule Alias

/--
error: unknown identifier 'missingPayload' in value of lf_def 'BadLFDefUnknownValue' in type theory
'BadLFDefUnknownValue'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFDefUnknownValue where
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  lf_opaque emptyCtx / 0
  lf_def BadLFDefUnknownValue : Shape emptyCtx := missingPayload

/--
error: unknown identifier 'missingJudgment' in statement of judgment_theorem 'bad_theorem' in type
theory 'BadLFJudgmentTheoremUnknownJudgment'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFJudgmentTheoremUnknownJudgment where
  lf_opaque proofPayload / 0
  judgment_theorem bad_theorem : missingJudgment := proofPayload

/--
error: judgment_theorem 'bad' in type theory 'BadLFTheoremReferenceStatementMismatch' uses
premise theorem 'simplex_refl' with a statement that does not match after LF-definition
normalization:
LF-definition normalization could not match expressions.
actual: shapeIncl emptyCtx Simplex Simplex
expected: shapeIncl emptyCtx Simplex Other
normalized actual: shapeIncl emptyCtx simplexPayload simplexPayload
normalized expected: shapeIncl emptyCtx simplexPayload otherPayload
LF definitions mentioned before unfolding: Simplex, Other
LF definitions unfolded: Simplex, Other
Normalization policy: LF matching unfolds earlier checked `lf_def` values, beta-reduces
explicit LF lambdas, contracts structural eta-redexes, and alpha-renames binders
to avoid local-binder capture.
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFTheoremReferenceStatementMismatch where
  side_condition_solver trivial_side_condition
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_opaque otherPayload / 0
  lf_opaque incl_input / 2
  lf_def Simplex : Shape emptyCtx := simplexPayload
  lf_def Other : Shape emptyCtx := otherPayload
  rule simplex_refl_rule where
    side_condition ok by trivial_side_condition : incl_input Simplex Simplex
    conclusion : shapeIncl emptyCtx Simplex Simplex
  judgment_theorem simplex_refl : shapeIncl emptyCtx Simplex Simplex := simplex_refl_rule
  judgment_theorem bad : shapeIncl emptyCtx Simplex Other := simplex_refl

/--
error: judgment_theorem 'bad' in type theory 'BadLFFutureTheoremReference' uses premise theorem
'later' before it is available
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFFutureTheoremReference where
  side_condition_solver trivial_side_condition
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_opaque incl_input / 2
  lf_def Simplex : Shape emptyCtx := simplexPayload
  rule simplex_refl_rule where
    side_condition ok by trivial_side_condition : incl_input Simplex Simplex
    conclusion : shapeIncl emptyCtx Simplex Simplex
  judgment_theorem bad : shapeIncl emptyCtx Simplex Simplex := later
  judgment_theorem later : shapeIncl emptyCtx Simplex Simplex := simplex_refl_rule

/--
error: judgment_theorem 'bad_nested' in type theory 'BadLFNestedTheoremReferencePremiseFuture' uses
premise theorem 'simplex_refl' before it is available
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFNestedTheoremReferencePremiseFuture where
  side_condition_solver trivial_side_condition
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_opaque incl_input / 2
  lf_def Simplex : Shape emptyCtx := simplexPayload
  rule simplex_refl_rule where
    side_condition ok by trivial_side_condition : incl_input Simplex Simplex
    conclusion : shapeIncl emptyCtx Simplex Simplex
  rule simplex_trans_rule (A : Shape emptyCtx) (B : Shape emptyCtx) (C : Shape emptyCtx) where
    premise left : shapeIncl emptyCtx A B
    premise right : shapeIncl emptyCtx B C
    conclusion : shapeIncl emptyCtx A C
  judgment_theorem bad_nested : shapeIncl emptyCtx Simplex Simplex :=
    simplex_trans_rule Simplex Simplex Simplex simplex_refl simplex_refl
  judgment_theorem simplex_refl : shapeIncl emptyCtx Simplex Simplex :=
    simplex_refl_rule

/--
error: judgment_theorem 'bad_nested' in type theory 'BadLFNestedTheoremReferencePremiseMismatch'
uses premise theorem 'other_refl' with a statement that does not match after LF-definition
normalization:
LF-definition normalization could not match expressions.
actual: shapeIncl emptyCtx Other Other
expected: shapeIncl emptyCtx Simplex Simplex
normalized actual: shapeIncl emptyCtx otherPayload otherPayload
normalized expected: shapeIncl emptyCtx simplexPayload simplexPayload
LF definitions mentioned before unfolding: Other, Simplex
LF definitions unfolded: Other, Simplex
Normalization policy: LF matching unfolds earlier checked `lf_def` values, beta-reduces
explicit LF lambdas, contracts structural eta-redexes, and alpha-renames binders
to avoid local-binder capture.
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFNestedTheoremReferencePremiseMismatch where
  side_condition_solver trivial_side_condition
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_opaque otherPayload / 0
  lf_opaque incl_input / 2
  lf_def Simplex : Shape emptyCtx := simplexPayload
  lf_def Other : Shape emptyCtx := otherPayload
  rule simplex_refl_rule where
    side_condition ok by trivial_side_condition : incl_input Simplex Simplex
    conclusion : shapeIncl emptyCtx Simplex Simplex
  rule other_refl_rule where
    side_condition ok by trivial_side_condition : incl_input Other Other
    conclusion : shapeIncl emptyCtx Other Other
  rule simplex_trans_rule (A : Shape emptyCtx) (B : Shape emptyCtx) (C : Shape emptyCtx) where
    premise left : shapeIncl emptyCtx A B
    premise right : shapeIncl emptyCtx B C
    conclusion : shapeIncl emptyCtx A C
  judgment_theorem simplex_refl : shapeIncl emptyCtx Simplex Simplex :=
    simplex_refl_rule
  judgment_theorem other_refl : shapeIncl emptyCtx Other Other :=
    other_refl_rule
  judgment_theorem bad_nested : shapeIncl emptyCtx Simplex Simplex :=
    simplex_trans_rule Simplex Simplex Simplex other_refl simplex_refl

/--
error: judgment_theorem 'bad' in type theory 'BadLFRuleApplicationOpaqueSideCondition' applies rule
'bad_rule' but side-condition 'opaque_ok' uses opaque solver 'opaque_solver' with no checked
certificate
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFRuleApplicationOpaqueSideCondition where
  side_condition_solver opaque_solver
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  lf_opaque emptyCtx / 0
  lf_opaque side / 0
  rule bad_rule where
    side_condition opaque_ok by opaque_solver : side
    conclusion : wfCtx emptyCtx
  judgment_theorem bad : wfCtx emptyCtx := bad_rule

/--
error: judgment_theorem 'bad_nested' in type theory 'BadLFNestedRuleApplicationPremiseMismatch'
applies rule 'simplex_refl_rule' but the statement does not match the rule conclusion after
LF-definition normalization:
LF-definition normalization could not match expressions.
actual: shapeIncl emptyCtx Simplex Other
expected: shapeIncl emptyCtx Simplex Simplex
normalized actual: shapeIncl emptyCtx simplexPayload otherPayload
normalized expected: shapeIncl emptyCtx simplexPayload simplexPayload
LF definitions mentioned before unfolding: Simplex, Other
LF definitions unfolded: Simplex, Other
Normalization policy: LF matching unfolds earlier checked `lf_def` values, beta-reduces
explicit LF lambdas, contracts structural eta-redexes, and alpha-renames binders
to avoid local-binder capture.
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFNestedRuleApplicationPremiseMismatch where
  side_condition_solver trivial_side_condition
  syntax_sort Ctx
  syntax_sort Shape (Γ : Ctx)
  judgment shapeIncl (Γ : Ctx) (S : Shape Γ) (T : Shape Γ)
  lf_opaque emptyCtx / 0
  lf_opaque simplexPayload / 0
  lf_opaque otherPayload / 0
  lf_opaque incl_input / 2
  lf_def Simplex : Shape emptyCtx := simplexPayload
  lf_def Other : Shape emptyCtx := otherPayload
  rule simplex_refl_rule where
    side_condition ok by trivial_side_condition : incl_input Simplex Simplex
    conclusion : shapeIncl emptyCtx Simplex Simplex
  rule simplex_trans_rule (A : Shape emptyCtx) (B : Shape emptyCtx) (C : Shape emptyCtx) where
    premise left : shapeIncl emptyCtx A B
    premise right : shapeIncl emptyCtx B C
    conclusion : shapeIncl emptyCtx A C
  judgment_theorem bad_nested : shapeIncl emptyCtx Simplex Simplex :=
    simplex_trans_rule Simplex Other Simplex simplex_refl_rule simplex_refl_rule

/--
error: unknown identifier 'missingJudgment' in premise 'bad' of rule 'bad_rule' in type theory
'BadRuleUnknownPremiseJudgment'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleUnknownPremiseJudgment where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  rule bad_rule (Γ : Ctx) where
    premise bad : missingJudgment Γ
    conclusion : wfCtx Γ

/--
error: unknown identifier 'missingJudgment' in conclusion of rule 'bad_rule' in type theory
'BadRuleUnknownConclusionJudgment'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleUnknownConclusionJudgment where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  rule bad_rule (Γ : Ctx) : missingJudgment Γ

/--
error: rule 'bad_rule' omits explicit argument 'Γ' in application 'wfCtx' in premise 'bad'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRulePremiseArity where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  rule bad_rule (Γ : Ctx) where
    premise bad : wfCtx
    conclusion : wfCtx Γ

/--
error: rule 'bad_rule' supplied too many explicit argument(s) to application 'wfCtx' in conclusion;
expected 1 total argument slot(s) after elaboration
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleConclusionArity where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  rule bad_rule (Γ : Ctx) : wfCtx Γ Γ

/--
error: judgment 'bad' omits explicit argument 'Γ' in application 'Ty' in parameter 'A' type
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadJudgmentSyntaxSortArity where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  judgment bad (A : Ty)

/--
error: syntax_sort 'Tm' omits explicit argument 'Γ' in application 'Ty' in parameter 'A' type
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxSortParamSyntaxSortArity where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  syntax_sort Tm (A : Ty)

/--
error: rule 'bad_rule' omits explicit argument 'Γ' in application 'Ty' in parameter 'A' type
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleParamSyntaxSortArity where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  judgment wfCtx (Γ : Ctx)
  rule bad_rule (A : Ty) : wfCtx CtxEmpty

/--
error: duplicate parameter name 'Γ' in syntax_sort 'BadSort' of type theory
'DuplicateSyntaxSortParam'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DuplicateSyntaxSortParam where
  syntax_sort Ctx
  syntax_sort BadSort (Γ : Ctx) (Γ : Ctx)

/--
error: duplicate parameter name 'Γ' in judgment 'bad' of type theory 'DuplicateJudgmentParam'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DuplicateJudgmentParam where
  syntax_sort Ctx
  judgment bad (Γ : Ctx) (Γ : Ctx)

/--
error: duplicate parameter name 'Γ' in rule 'bad_rule' of type theory 'DuplicateRuleParam'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DuplicateRuleParam where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  rule bad_rule (Γ : Ctx) (Γ : Ctx) : wfCtx Γ

/--
error: unknown identifier 'missing' in conclusion of rule 'bad_rule' in type theory
'BadRuleUnknownConclusionIdentifier'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleUnknownConclusionIdentifier where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  rule bad_rule (Γ : Ctx) : wfCtx missing

/--
error: unknown identifier 'missingPredicate' in side-condition 'bad' of rule 'bad_rule' in type
theory 'BadRuleUnknownSideConditionIdentifier'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleUnknownSideConditionIdentifier where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  side_condition_solver toy
  rule bad_rule (Γ : Ctx) where
    side_condition bad by toy : missingPredicate Γ
    conclusion : wfCtx Γ

/--
error: rule 'bad_rule' in type theory 'BadRuleLocalSideConditionHead' has side-condition 'bad'
headed by local parameter 'P'; declare a judgment or lf_opaque placeholder instead
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleLocalSideConditionHead where
  syntax_sort Ctx
  syntax_sort Predicate
  judgment wfCtx (Γ : Ctx)
  side_condition_solver toy
  rule bad_rule (Γ : Ctx) (P : Predicate) where
    side_condition bad by toy : P Γ
    conclusion : wfCtx Γ

/--
error: rule 'bad_rule' in type theory 'BadLFOpaqueArity' uses lf_opaque 'mkCtx' in conclusion with 0
argument(s), expected 1
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLFOpaqueArity where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  lf_opaque mkCtx / 1
  rule bad_rule : wfCtx mkCtx

/--
error: rule 'bad_rule' omits explicit argument 'Γ' in application 'Ty' in conclusion argument 'A' of
'bad'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleExpressionSyntaxSortArity where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  judgment bad (Γ : Ctx) (A : Ty Γ)
  rule bad_rule (Γ : Ctx) : bad Γ Ty

/--
error: rule 'bad_rule' in type theory 'BadRuleLocalArgumentSortMismatch' has premise 'bad' for
judgment 'wfTy' argument 'A' with type 'Ty Γ', expected 'Ty Δ'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleLocalArgumentSortMismatch where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  judgment wfTy (Γ : Ctx) (A : Ty Γ)
  rule bad_rule (Γ : Ctx) (Δ : Ctx) (A : Ty Γ) where
    premise bad : wfTy Δ A
    conclusion : wfTy Γ A

/--
error: duplicate lambda binder 'x' in conclusion of rule 'bad_rule' in type theory
'BadRuleDuplicateLambdaBinder'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleDuplicateLambdaBinder where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  lf_opaque test / 1
  rule bad_rule (Γ : Ctx) : wfCtx (test (fun x x => Γ))

/--
error: rule 'bad_rule' in type theory 'BadRuleUnknownSolver' uses unknown side-condition solver
'missing_solver'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleUnknownSolver where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  rule bad_rule (Γ : Ctx) where
    side_condition bad by missing_solver : wfCtx Γ
    conclusion : wfCtx Γ

/--
error: duplicate side-condition solver declaration 'toy' in type-theory block
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DuplicateSideConditionSolver where
  side_condition_solver toy
  side_condition_solver toy

/--
error: duplicate conversion plugin declaration 'conv' in type-theory block
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DuplicateConversionPlugin where
  conversion_plugin conv
  conversion_plugin conv

/--
error: duplicate conversion_plugin step 'beta' for plugin 'c' in type theory 'DupConvStep'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DupConvStep where
  conversion_plugin c executable [beta, beta]

/--
error: judgment_role for unknown judgment 'missingJudgment' in type theory 'BadJudgmentRole'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadJudgmentRole where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  judgment_role missingJudgment : term_typing

/--
error: duplicate judgment_role 'term_typing' for judgment 'wfCtx' in type theory
'DuplicateJudgmentRole'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DuplicateJudgmentRole where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  judgment_role wfCtx : term_typing
  judgment_role wfCtx : term_typing

/--
error: syntax_sort_role for unknown syntax family 'MissingSort' in type theory 'BadSyntaxSortRole'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxSortRole where
  syntax_sort Ctx
  syntax_sort_role MissingSort : context

/--
error: duplicate syntax_sort_role 'context' for syntax sort 'Ctx' in type theory
'DuplicateSyntaxSortRole'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DuplicateSyntaxSortRole where
  syntax_sort Ctx
  syntax_sort_role Ctx : context
  syntax_sort_role Ctx : context

/--
error: context_zone 'ordinary' in type theory 'BadContextZoneSort' uses unknown syntax sort
'MissingSort'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadContextZoneSort where
  syntax_sort Ctx
  context_zone ordinary : MissingSort

/--
error: context_zone 'tope' in type theory 'BadContextZoneDependency' depends on unknown or later
zone 'cube'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadContextZoneDependency where
  syntax_sort Ctx
  context_zone tope : Ctx depends_on cube

/--
error: duplicate context-zone declaration 'ordinary' in type-theory block
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DuplicateContextZone where
  syntax_sort Ctx
  context_zone ordinary : Ctx
  context_zone ordinary : Ctx

/--
error: context_zone 'tope' in type theory 'DuplicateContextZoneDependency' has duplicate dependency
'cube'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DuplicateContextZoneDependency where
  syntax_sort Ctx
  context_zone cube : Ctx
  context_zone tope : Ctx depends_on cube, cube

/--
error: binder_class 'bad' in type theory 'BadBinderClassSort' uses unknown syntax sort 'MissingSort'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadBinderClassSort where
  syntax_sort Ctx
  context_zone ordinary : Ctx
  binder_class bad : MissingSort in ordinary

/--
error: binder_class 'bad' in type theory 'BadBinderClassZone' uses unknown context zone
'missingZone'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadBinderClassZone where
  syntax_sort Ctx
  syntax_sort Tm
  context_zone ordinary : Ctx
  binder_class bad : Tm in missingZone

/--
error: binder_class 'bad' in type theory 'DuplicateBinderClassDependency' has duplicate dependency
'ordinary'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DuplicateBinderClassDependency where
  syntax_sort Ctx
  syntax_sort Tm
  context_zone ordinary : Ctx
  binder_class bad : Tm in ordinary depends_on ordinary, ordinary

/--
error: binder_class 'bad' in type theory 'BadBinderClassDependency' depends on unknown context zone
'missingZone'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadBinderClassDependency where
  syntax_sort Ctx
  syntax_sort Tm
  context_zone ordinary : Ctx
  binder_class bad : Tm in ordinary depends_on missingZone

/--
error: rule_role for unknown rule 'missing_rule' in type theory 'BadRuleRole'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadRuleRole where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  rule good_rule (Γ : Ctx) : wfCtx Γ
  rule_role missing_rule : formation

/--
error: duplicate rule_role 'formation' for rule 'good_rule' in type theory 'DuplicateRuleRole'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory DuplicateRuleRole where
  syntax_sort Ctx
  judgment wfCtx (Γ : Ctx)
  rule good_rule (Γ : Ctx) : wfCtx Γ
  rule_role good_rule : formation
  rule_role good_rule : formation
