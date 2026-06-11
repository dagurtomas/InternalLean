/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Examples.UniverseHierarchy

/-!
# Object-language universe hierarchy encoding tests

These regressions exercise the hand-written universe-hierarchy prelude from
`Examples.UniverseHierarchy`.  Object levels remain ordinary LF syntax; all acceptance still flows
through checked LF replay and generated model obligations.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

#check UniverseHierarchy.Model
#check UniverseHierarchy.syntacticModel
#check UniverseHierarchy.natModel
#check UniverseHierarchy.zero_le_succ_zero
#check UniverseHierarchy.liftedZeroUniv
#check UniverseHierarchy.liftedZeroUniv_wf
#check UniverseHierarchy.unitToUnitPi
#check UniverseHierarchy.LFQuote.Pi
#check UniverseHierarchy.LFQuote.Sigma
#check UniverseHierarchy.LFQuote.UnitTy

example : UniverseHierarchy.natModel.Le UniverseHierarchy.natModel.zero
    (UniverseHierarchy.natModel.succ UniverseHierarchy.natModel.zero) :=
  UniverseHierarchy.natModel.le_succ UniverseHierarchy.natModel.zero

example : UniverseHierarchy.natModel.IsTy
    (UniverseHierarchy.natModel.Univ UniverseHierarchy.natModel.zero) :=
  UniverseHierarchy.natModel.univ_wf UniverseHierarchy.natModel.zero

-- Native-tactic goals for the hierarchy render through the mirror display backend.
run_cmd do
  let target : InternalDefTarget := {
    theoryName := `UniverseHierarchy
    localName := `zero_le_succ_zero
    anchorName := `UniverseHierarchy.zero_le_succ_zero }
  let targetExpr : ObjExpr :=
    .app (.app (.ident `Le) (.ident `zero)) (.app (.ident `succ) (.ident `zero))
  let snapshot ← liftTermElabM do
    let displayCtx ← prepareInternalGoalDisplayContext target
    let goal := mkInternalGoalDisplayGoal #[] targetExpr
    mkInternalObjectGoalDisplaySnapshotWithContext target displayCtx #[goal]
  unless snapshot.fallbacks.isEmpty do
    throwError "universe hierarchy goal display unexpectedly used fallback"
  let some mvarId := snapshot.goals.head? | throwError "missing hierarchy display goal"
  let mvarDecl := snapshot.mctx.getDecl mvarId
  match mvarDecl.type.getAppFn with
  | .const n _ =>
      unless n == lfMirrorDeclName `UniverseHierarchy `Le do
        throwError "hierarchy display goal has unexpected head '{n}'"
  | _ => throwError "hierarchy display goal is not headed by a mirror constant"

/--
info: reflected LF term in type theory 'UniverseHierarchy':
  lift (succ zero) (succ (succ zero)) (Univ zero)
-/
#guard_msgs (whitespace := lax) in
#reflect_lf_quote UniverseHierarchy :
  lift (i := succ zero) (j := succ (succ zero)) (Univ zero)

/--
info: reflected LF term in type theory 'UniverseHierarchy':
  Pi zero zero (UnitTy zero) (fun x => UnitTy zero)
-/
#guard_msgs (whitespace := lax) in
#reflect_lf_quote UniverseHierarchy :
  Pi (i := zero) (j := zero) (UnitTy (i := zero)) fun _ => UnitTy (i := zero)

/--
error: syntax_def 'Bad' in type theory 'BadUniverseHierarchySyntaxDef' has value in universe
'Type 1', expected 'Type'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadUniverseHierarchySyntaxDef where
  syntax_sort Level : Type
  syntax_sort Ty (i : Level) : Type 1
  lf_opaque zero : Level
  syntax_def Bad : Type := Ty zero
