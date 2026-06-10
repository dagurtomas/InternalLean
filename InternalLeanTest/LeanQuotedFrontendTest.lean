/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Lean-elaborated quoted LF frontend tests

These tests cover the experimental `internal_lean def` frontend.  Lean elaborates the term body
against generated `T.LFQuote` stubs; InternalLean reflects the elaborated expression back to LF and
then runs the ordinary LF checker.
-/

@[expose] public section

open InternalLean

declare_type_theory LeanQuotedFrontendSmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  lf_opaque id (x : Obj) : Obj
  judgment IsObj (x : Obj)
  rule mkObj (x : Obj) : IsObj x

#check LeanQuotedFrontendSmoke.LFQuote.Obj
#check LeanQuotedFrontendSmoke.LFQuote.o
#check LeanQuotedFrontendSmoke.LFQuote.id
#check LeanQuotedFrontendSmoke.LFQuote.mkObj

run_cmd do
  let env ← Lean.getEnv
  let theoryName := `LeanQuotedStagedOnly
  let sourceName := `Obj
  let decl ← Lean.Elab.Command.liftCoreM <|
    mkLFQuoteStubDeclaration env theoryName sourceName #[] none
  let stagedEnv ← Lean.Elab.Command.liftCoreM <| addLFQuoteStubToEnv env decl
  let declName := lfQuoteDeclName theoryName sourceName
  unless Lean.Environment.contains stagedEnv declName do
    throwError "staged quote-stub environment did not contain '{declName}'"
  unless Lean.Environment.isNamespace stagedEnv (lfQuoteNamespace theoryName) do
    throwError "staged quote-stub environment did not register namespace \
      '{lfQuoteNamespace theoryName}'"
  if Lean.Environment.contains (← Lean.getEnv) declName then
    throwError "staged quote stub '{declName}' was committed to the command environment"

/--
info: quoted LF stubs for LeanQuotedFrontendSmoke:
syntax_sort Obj -> LeanQuotedFrontendSmoke.LFQuote.Obj / 0 parameter(s)
judgment IsObj -> LeanQuotedFrontendSmoke.LFQuote.IsObj / 1 parameter(s)
rule mkObj -> LeanQuotedFrontendSmoke.LFQuote.mkObj / 1 parameter(s)
lf_opaque o -> LeanQuotedFrontendSmoke.LFQuote.o / 0 parameter(s)
lf_opaque id -> LeanQuotedFrontendSmoke.LFQuote.id / 1 parameter(s)
-/
#guard_msgs (whitespace := lax) in
#print_lf_quote_stubs LeanQuotedFrontendSmoke

/--
info: reflected LF term in type theory 'LeanQuotedFrontendSmoke':
  id o
-/
#guard_msgs (whitespace := lax) in
#reflect_lf_quote LeanQuotedFrontendSmoke : id LeanQuotedFrontendSmoke.LFQuote.o

/--
info: reflected LF term in type theory 'LeanQuotedFrontendSmoke':
  Obj × Obj
-/
#guard_msgs (whitespace := lax) in
#reflect_lf_quote LeanQuotedFrontendSmoke : prod Obj Obj

/--
info: reflected LF term in type theory 'LeanQuotedFrontendSmoke':
  Obj ≡ Obj
-/
#guard_msgs (whitespace := lax) in
#reflect_lf_quote LeanQuotedFrontendSmoke : jeq Obj Obj

/--
info: reflected LF term in type theory 'LeanQuotedFrontendSmoke':
  Σ x : Obj, Obj
-/
#guard_msgs (whitespace := lax) in
#reflect_lf_quote LeanQuotedFrontendSmoke : sigma Obj (fun _ => Obj)

/--
info: reflected LF term in type theory 'LeanQuotedFrontendSmoke':
  Obj → Obj
-/
#guard_msgs (whitespace := lax) in
#reflect_lf_quote LeanQuotedFrontendSmoke : funArrow Obj Obj

/--
info: reflected LF term in type theory 'LeanQuotedFrontendSmoke':
  Obj ⇒ Obj
-/
#guard_msgs (whitespace := lax) in
#reflect_lf_quote LeanQuotedFrontendSmoke : arrow Obj Obj

declare_type_theory LeanQuotedImplicitSmoke where
  syntax_sort Obj
  syntax_sort El (A : Obj)
  judgment Has (A : Obj) (x : El A)
  lf_opaque A : Obj
  lf_opaque a : El A
  lf_opaque id {A : Obj} (x : El A) : El A
  rule has_id {A : Obj} (x : El A) : Has A (id x)

/--
info: reflected LF term in type theory 'LeanQuotedImplicitSmoke':
  id A a
-/
#guard_msgs (whitespace := lax) in
#reflect_lf_quote LeanQuotedImplicitSmoke : id a

run_cmd do
  let some sig ← Lean.Elab.Command.liftCoreM <| getCheckedHLSignature? `LeanQuotedImplicitSmoke
    | throwError "missing checked signature for LeanQuotedImplicitSmoke"
  let term ← `(term| id a)
  let expected : ObjExpr := .app (.ident `El) (.ident `A)
  let reflected ← elabLeanQuotedObjTerm `LeanQuotedImplicitSmoke sig #[] (some expected) term
  let expectedReflected : ObjExpr := .app (.app (.ident `id) (.ident `A)) (.ident `a)
  unless reflected == expectedReflected do
    throwError "expected reusable quoted elaborator to reflect {expectedReflected}, got \
      {reflected}"

namespace LeanQuotedImplicitSmoke

internal_lean def id_a : El A := id a
internal_lean theorem has_id_a : Has A (id a) := has_id a

end LeanQuotedImplicitSmoke

declare_type_theory LeanQuoteUntypedLocalFallbackSmoke where
  syntax_sort U
  syntax_sort El (A : U)
  syntax_sort T {A : U} (x : El A)
  syntax_sort Box {A : U} {x : El A} (p : T x)

namespace LeanQuoteUntypedLocalFallbackSmoke

/--
warning: internal declaration 'LeanQuoteUntypedLocalFallbackSmoke.fallbackParam' was admitted by
`sorry`; the annotation was checked in theory 'LeanQuoteUntypedLocalFallbackSmoke', but the body was
not checked. Use `#lint_type_theory_sorries LeanQuoteUntypedLocalFallbackSmoke` to list current
admissions.
-/
#guard_msgs (whitespace := lax) in
internal_defs where
  def fallbackParam (A : U) (x : El A) (p : T x) : Box p := sorry

end LeanQuoteUntypedLocalFallbackSmoke

/--
info: LeanQuoteUntypedLocalFallbackSmoke.LFQuote.fallbackParam
  (A : LFQuoteOf LeanQuoteUntypedLocalFallbackSmoke.LFQuote.U)
  (x : LFQuoteOf (LeanQuoteUntypedLocalFallbackSmoke.LFQuote.El A))
  (p : LFQuoteTerm) : LFQuoteTerm
-/
#guard_msgs (whitespace := lax) in
#check LeanQuoteUntypedLocalFallbackSmoke.LFQuote.fallbackParam

set_option internalLean.requireLeanQuotedTheoryBlocks true in
declare_type_theory LeanQuotedTheoryBlockSmoke where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  lf_opaque empty : Ctx
  lf_opaque base : Ty empty
  lf_opaque ext {Γ : Ctx} (A : Ty Γ) : Ctx
  lf_opaque top {Γ : Ctx} (A : Ty Γ) : Ty (ext (Γ := Γ) A)
  lf_def topBase : Ty (ext (Γ := empty) base) := top base
  judgment IsTy {Γ : Ctx} (A : Ty Γ)
  rule mkTy {Γ : Ctx} (A : Ty Γ) : IsTy A
  judgment_theorem topBase_ok : IsTy topBase := mkTy topBase

#check LeanQuotedTheoryBlockSmoke.LFQuote.topBase
#check LeanQuotedTheoryBlockSmoke.LFQuote.topBase_ok

set_option internalLean.requireLeanQuotedTheoryBlocks true in
extend_type_theory LeanQuotedTheoryBlockSmoke where
  lf_def topBaseAlias : Ty (ext (Γ := empty) base) := topBase
  judgment_theorem topBaseAlias_ok : IsTy topBaseAlias := mkTy topBaseAlias

#check LeanQuotedTheoryBlockSmoke.LFQuote.topBaseAlias
#check LeanQuotedTheoryBlockSmoke.LFQuote.topBaseAlias_ok

namespace LeanQuotedFrontendSmoke

internal_lean def d : Obj := o
internal_lean def e : Obj := LFQuote.id o
internal_lean def eUnqualified : Obj := id o
internal_lean def f (x : Obj) : Obj := LFQuote.id x
internal_lean def dAlias : Obj := LFQuote.d
internal_lean def idObj : Obj → Obj := fun x => x
internal_lean def idObjUnqualified : Obj → Obj := fun x => id x
internal_lean def byExactObj : Obj := by exact o
internal_lean def pairOO : Obj × Obj := pair o o
internal_lean def pairOOFst : Obj := projFst pairOO
internal_lean def pairOOSnd : Obj := projSnd pairOO
internal_lean def dependentPairOO : Σ x : Obj, Obj := pair o o
internal_lean def applyLocal (g : Obj → Obj) (x : Obj) : Obj := g x
internal_lean def o_ok : IsObj o := LFQuote.mkObj o
internal_lean theorem o_ok_theorem : IsObj o := LFQuote.mkObj o
internal_lean theorem local_ok_theorem (x : Obj) (h : IsObj x) : IsObj x := h
internal_lean theorem byExactTheorem : IsObj o := by exact mkObj o
internal_lean theorem byApplyTheorem : IsObj o := by
  apply mkObj
internal_lean theorem byExactLocal (x : Obj) (h : IsObj x) : IsObj x := by exact h
internal_lean theorem byAssumptionLocal (x : Obj) (h : IsObj x) : IsObj x := by
  assumption
set_option internalLean.preferLeanQuotedFrontend true in
internal def canonicalQuotedObj : Obj := LFQuote.o
set_option internalLean.preferLeanQuotedFrontend true in
internal def canonicalQuotedBinder (x : Obj) : Obj := x
set_option internalLean.preferLeanQuotedFrontend true in
internal theorem canonicalQuotedTheorem : IsObj o := LFQuote.mkObj o
internal_raw def rawObj : Obj := o
internal_raw theorem rawObjOk : IsObj o := mkObj o
internal_raw def rawObjOkBy : IsObj o := by
  exact mkObj o
/--
warning: internal declaration 'LeanQuotedFrontendSmoke.admittedObj' was admitted by `sorry`; the
annotation was checked in theory 'LeanQuotedFrontendSmoke', but the body was not checked. Use
`#lint_type_theory_sorries LeanQuotedFrontendSmoke` to list current admissions.
-/
#guard_msgs (whitespace := lax) in
internal_lean def admittedObj : Obj := sorry

/--
warning: internal declaration 'LeanQuotedFrontendSmoke.admittedObjBy' was admitted by `sorry`; the
annotation was checked in theory 'LeanQuotedFrontendSmoke', but the body was not checked. Use
`#lint_type_theory_sorries LeanQuotedFrontendSmoke` to list current admissions.
-/
#guard_msgs (whitespace := lax) in
internal_lean def admittedObjBy : Obj := by
  sorry

/--
warning: internal declaration 'LeanQuotedFrontendSmoke.admittedBinder' was admitted by `sorry`; the
annotation was checked in theory 'LeanQuotedFrontendSmoke', but the body was not checked. Use
`#lint_type_theory_sorries LeanQuotedFrontendSmoke` to list current admissions.
-/
#guard_msgs (whitespace := lax) in
internal_lean def admittedBinder (x : Obj) : Obj := sorry

/--
warning: internal declaration 'LeanQuotedFrontendSmoke.admittedBinderBy' was admitted by `sorry`;
the annotation was checked in theory 'LeanQuotedFrontendSmoke', but the body was not checked. Use
`#lint_type_theory_sorries LeanQuotedFrontendSmoke` to list current admissions.
-/
#guard_msgs (whitespace := lax) in
internal_lean def admittedBinderBy (x : Obj) : Obj := by
  sorry

#check d
#check e
#check eUnqualified
#check f
#check dAlias
#check idObj
#check idObjUnqualified
#check byExactObj
#check pairOO
#check pairOOFst
#check pairOOSnd
#check dependentPairOO
#check applyLocal
#check o_ok
#check o_ok_theorem
#check local_ok_theorem
#check byExactTheorem
#check byApplyTheorem
#check byExactLocal
#check byAssumptionLocal
#check canonicalQuotedObj
#check canonicalQuotedBinder
#check canonicalQuotedTheorem
#check rawObj
#check rawObjOk
#check rawObjOkBy
#check admittedObj
#check admittedObjBy
#check admittedBinder
#check admittedBinderBy

/--
warning: type theory 'LeanQuotedFrontendSmoke' has 4 admitted internal declaration(s):
admitted internal def LeanQuotedFrontendSmoke.admittedObj : Obj [missing doc]
admitted internal def LeanQuotedFrontendSmoke.admittedObjBy : Obj [missing doc]
admitted internal def LeanQuotedFrontendSmoke.admittedBinder (x : Obj) : Obj [missing doc]
admitted internal def LeanQuotedFrontendSmoke.admittedBinderBy (x : Obj) : Obj [missing doc]
-/
#guard_msgs (whitespace := lax) in
#lint_type_theory_sorries LeanQuotedFrontendSmoke

end LeanQuotedFrontendSmoke

declare_type_theory LeanQuotedParentSmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj

declare_type_theory LeanQuotedChildSmoke extends LeanQuotedParentSmoke where
  judgment IsObj (x : Obj)
  rule mkObj (x : Obj) : IsObj x

namespace LeanQuotedChildSmoke

internal_lean def inheritedObj : Obj := o
internal_lean theorem inheritedObjOk : IsObj o := mkObj o

#check inheritedObj
#check inheritedObjOk

end LeanQuotedChildSmoke

declare_type_theory LeanQuotedBinderShadowSmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  lf_opaque x : Obj

namespace LeanQuotedBinderShadowSmoke

internal_lean def shadowLocal : Obj → Obj := fun x => x
internal_lean def shadowLocalApplied : Obj := (fun x => x) o
internal_lean def useGlobalX : Obj := x

#check shadowLocal
#check shadowLocalApplied
#check useGlobalX

end LeanQuotedBinderShadowSmoke

declare_type_theory LeanQuotedTheoremSorrySmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  judgment IsObj (x : Obj)

namespace LeanQuotedTheoremSorrySmoke

/--
warning: internal theorem 'LeanQuotedTheoremSorrySmoke.a' was admitted by `sorry`; the statement
was checked in theory 'LeanQuotedTheoremSorrySmoke', but the proof was not checked. Use
`#lint_type_theory_sorries LeanQuotedTheoremSorrySmoke` to list current admissions.
-/
#guard_msgs (whitespace := lax) in
internal_lean theorem a : IsObj o := sorry

/--
warning: internal theorem 'LeanQuotedTheoremSorrySmoke.b' was admitted by `sorry`; the statement
was checked in theory 'LeanQuotedTheoremSorrySmoke', but the proof was not checked. Use
`#lint_type_theory_sorries LeanQuotedTheoremSorrySmoke` to list current admissions.
-/
#guard_msgs (whitespace := lax) in
internal_lean theorem b (x : Obj) : IsObj x := by
  sorry

/--
warning: type theory 'LeanQuotedTheoremSorrySmoke' has 2 admitted internal declaration(s):
admitted internal theorem LeanQuotedTheoremSorrySmoke.a : IsObj o [missing doc]
admitted internal theorem LeanQuotedTheoremSorrySmoke.b (x : Obj) : IsObj x [missing doc]
-/
#guard_msgs (whitespace := lax) in
#lint_type_theory_sorries LeanQuotedTheoremSorrySmoke

end LeanQuotedTheoremSorrySmoke

namespace LeanQuotedFrontendSmoke

/--
error: Lean-elaborated LF term uses Lean constant 'InternalLean.LFQuoteTerm.mk', which is not
part of the quoted LF signature for type theory 'LeanQuotedFrontendSmoke'. Use a generated
declaration in namespace 'LeanQuotedFrontendSmoke.LFQuote', or an LF declaration name available in
the checked theory.
-/
#guard_msgs (whitespace := lax) in
internal_lean def bad : Obj := InternalLean.LFQuoteTerm.mk

end LeanQuotedFrontendSmoke
