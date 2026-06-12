/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Quoted-stub dependency-order tests

These tests cover staged quoted-LF stub emission.  The LF checker remains the acceptance gate;
the generated Lean stubs are only elaboration/navigation handles.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

namespace QuotedStubDependencyOrderTest

/-- Fetch a generated quote-stub declaration type. -/
def quoteStubType (declName : Name) : CommandElabM Expr := do
  let some info := (← getEnv).find? declName
    | throwError "missing generated quote stub '{declName}'"
  pure info.type

/-- Assert that a generated quote stub is not the unindexed marker and mentions a dependency. -/
def assertPreciseStubMentions (declName dependency : Name) : CommandElabM Unit := do
  let type ← quoteStubType declName
  if type == mkConst ``LFQuoteTerm then
    throwError "expected precise quote stub for '{declName}', got LFQuoteTerm"
  unless (reprStr type).contains dependency.toString do
    throwError "expected quote stub '{declName}' to mention dependency '{dependency}', got {type}"

/-- Assert that a generated quote stub is exactly the unindexed marker. -/
def assertMarkerStub (declName : Name) : CommandElabM Unit := do
  let type ← quoteStubType declName
  unless type == mkConst ``LFQuoteTerm do
    throwError "expected marker quote stub for '{declName}', got {type}"

/-- Drop leading `forall` binders in a generated quote-stub type. -/
partial def dropForalls : Expr → Nat → Expr
  | type, 0 => type
  | .forallE _ _ body _, n + 1 => dropForalls body n
  | type, _ => type

/-- Check whether one of the first binders in a generated quote-stub type is unindexed. -/
partial def hasUntypedBinderWithin : Expr → Nat → Bool
  | _, 0 => false
  | .forallE _ domain body _, n + 1 =>
      domain == mkConst ``LFQuoteTerm || hasUntypedBinderWithin body n
  | _, _ => false

/-- Assert that a generated quote-stub parameter/result path still contains marker slots. -/
def assertMarkerBinderAndResult (declName : Name) (arity : Nat) : CommandElabM Unit := do
  let type ← quoteStubType declName
  unless hasUntypedBinderWithin type arity do
    throwError "expected quote stub '{declName}' to contain an LFQuoteTerm binder, got {type}"
  unless dropForalls type arity == mkConst ``LFQuoteTerm do
    throwError "expected quote stub '{declName}' to return LFQuoteTerm, got {type}"

end QuotedStubDependencyOrderTest

open QuotedStubDependencyOrderTest

declare_type_theory Q1StubOrderSmoke where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  syntax_sort Subst (Δ : Ctx) (Γ : Ctx)
  syntax_sort Tm (Γ : Ctx) (A : Ty Γ)
  lf_opaque extendCtx (Γ : Ctx) (A : Ty Γ) : Ctx
  lf_opaque weakenSub (Γ : Ctx) (A : Ty Γ) : Subst (extendCtx Γ A) Γ
  lf_opaque substTy {Γ : Ctx} {Δ : Ctx} (A : Ty Γ) (sub : Subst Δ Γ) : Ty Δ
  lf_def weakenTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒ Ty (extendCtx Γ A) :=
    fun Γ A B => substTy B (weakenSub Γ A)
  lf_opaque varTop (Γ : Ctx) (A : Ty Γ) : Tm (extendCtx Γ A) (weakenTy Γ A A)
  judgment EqTm {Γ : Ctx} {A : Ty Γ} (a : Tm Γ A) (b : Tm Γ A)
  rule refl {Γ : Ctx} {A : Ty Γ} (a : Tm Γ A) : EqTm a a

run_cmd do
  assertPreciseStubMentions `Q1StubOrderSmoke.LFQuote.varTop `weakenTy

namespace Q1StubOrderSmoke

internal def test : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Tm (extendCtx Γ A) (weakenTy Γ A A) :=
  fun Γ A => varTop Γ A

internal theorem testRefl (Γ : Ctx) (A : Ty Γ) : EqTm (varTop Γ A) (varTop Γ A) :=
  refl (varTop Γ A)

end Q1StubOrderSmoke

declare_type_theory Q1StubOrderExtendBase where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  syntax_sort Subst (Δ : Ctx) (Γ : Ctx)
  syntax_sort Tm (Γ : Ctx) (A : Ty Γ)
  lf_opaque extendCtx (Γ : Ctx) (A : Ty Γ) : Ctx
  lf_opaque weakenSub (Γ : Ctx) (A : Ty Γ) : Subst (extendCtx Γ A) Γ
  lf_opaque substTy {Γ : Ctx} {Δ : Ctx} (A : Ty Γ) (sub : Subst Δ Γ) : Ty Δ

extend_type_theory Q1StubOrderExtendBase where
  lf_def weakenTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒ Ty (extendCtx Γ A) :=
    fun Γ A B => substTy B (weakenSub Γ A)
  lf_opaque varTop (Γ : Ctx) (A : Ty Γ) : Tm (extendCtx Γ A) (weakenTy Γ A A)

run_cmd do
  assertPreciseStubMentions `Q1StubOrderExtendBase.LFQuote.varTop `weakenTy

declare_type_theory Q1StubOrderChild extends Q1StubOrderSmoke where

run_cmd do
  assertPreciseStubMentions `Q1StubOrderChild.LFQuote.varTop `weakenTy

run_cmd do
  let before ← quoteStubType `Q1StubOrderSmoke.LFQuote.varTop
  let some sig ← liftCoreM <| getCheckedHLSignature? `Q1StubOrderSmoke
    | throwError "missing checked signature for Q1StubOrderSmoke"
  addLFQuoteStubsForHLSignatureIfMissing `Q1StubOrderSmoke sig
  let after ← quoteStubType `Q1StubOrderSmoke.LFQuote.varTop
  unless before == after do
    throwError "ensure-present quote-stub pass changed an existing stub type"

extract_theory_fragment Q1StubOrderFragment from Q1StubOrderSmoke for test

run_cmd do
  assertPreciseStubMentions `Q1StubOrderFragment.LFQuote.varTop `weakenTy

declare_type_theory Q1UnderAppliedMarkerSmoke where
  syntax_sort U
  syntax_sort El (A : U)
  syntax_sort T {A : U} (x : El A)
  syntax_sort Box {A : U} {x : El A} (p : T x)

/-- warning: internal declaration 'Q1UnderAppliedMarkerSmoke.fallbackParam' was admitted by
`sorry`; the annotation was checked in theory 'Q1UnderAppliedMarkerSmoke', but the body was not
checked. Use `#lint_type_theory_sorries Q1UnderAppliedMarkerSmoke` to list current admissions. -/
#guard_msgs (whitespace := lax) in
internal def Q1UnderAppliedMarkerSmoke.fallbackParam (A : U) (x : El A) (p : T x) : Box p :=
  sorry

run_cmd do
  assertMarkerBinderAndResult `Q1UnderAppliedMarkerSmoke.LFQuote.fallbackParam 3

declare_type_theory Q1ProjectionMarkerSmoke where
  syntax_sort U
  syntax_sort Fam (A : U)
  lf_opaque pairUU : U × U
  lf_opaque projected : Fam (Sigma.fst pairUU)

run_cmd do
  assertMarkerStub `Q1ProjectionMarkerSmoke.LFQuote.projected

extend_type_theory Q1ProjectionMarkerSmoke where
  syntax_sort Box (x : Fam (Sigma.fst pairUU))
  lf_opaque later : Box projected

run_cmd do
  assertMarkerStub `Q1ProjectionMarkerSmoke.LFQuote.later

#check Q1StubOrderSmoke.test
#check Q1StubOrderSmoke.testRefl
#check Q1StubOrderFragment.test
