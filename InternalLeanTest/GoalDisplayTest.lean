/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Mirror-backed goal display tests

These checks are non-LSP smoke tests for the Phase 7 goal renderer.  They inspect the isolated
metavariable context stored in a display snapshot rather than querying an editor.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

declare_type_theory GoalDisplaySmoke{u} where
  syntax_sort Obj : Type u
  judgment Good {A : Obj} (x : Obj)
  lf_opaque o : Obj
  rule good_o : Good (A := o) o

namespace GoalDisplaySmoke

internal theorem goalDisplayQuotedBy : Good (A := o) o := by
  exact good_o

internal def goalDisplayQuotedTerm : Obj := o

end GoalDisplaySmoke

-- Assert that mirror-backed display goals use isolated synthetic-opaque metavariables whose
-- context preserves implicit binder visibility and universe-polymorphic mirror constants.
run_cmd do
  let goalDisplayTestTarget : InternalDefTarget := {
    theoryName := `GoalDisplaySmoke
    localName := `displayProbe
    anchorName := `GoalDisplaySmoke.displayProbe }
  let ctx : Array HLBinding := #[
    { name := `A, typeExpr := .ident `Obj, visibility := .implicit },
    { name := `x, typeExpr := .ident `Obj, visibility := .explicit }]
  let targetExpr : ObjExpr := .app (.app (.ident `Good) (.ident `A)) (.ident `x)
  let (snapshot, leaked?) ← liftTermElabM do
    let displayCtx ← prepareInternalGoalDisplayContext goalDisplayTestTarget
    let goal := mkInternalGoalDisplayGoal ctx targetExpr
    let snapshot ← mkInternalObjectGoalDisplaySnapshotWithContext goalDisplayTestTarget
      displayCtx #[goal]
    let leaked? := (← getMCtx).findDecl? snapshot.goals.head! |>.isSome
    pure (snapshot, leaked?)
  if leaked? then
    throwError "display metavariable leaked into the ambient elaboration context"
  unless snapshot.fallbacks.isEmpty do
    throwError "representative mirror display goal unexpectedly used fallback"
  let some mvarId := snapshot.goals.head? | throwError "missing display goal metavariable"
  let mvarDecl := snapshot.mctx.getDecl mvarId
  match mvarDecl.kind with
  | .syntheticOpaque => pure ()
  | _ => throwError "display metavariable is not syntheticOpaque"
  let some ADecl := mvarDecl.lctx.findFromUserName? `A
    | throwError "display local context is missing implicit binder A"
  unless ADecl.binderInfo == BinderInfo.implicit do
    throwError "display local A did not preserve implicit binder visibility"
  match ADecl.type with
  | .const n levels =>
      unless n == lfMirrorDeclName `GoalDisplaySmoke `Obj do
        throwError "display local A has unexpected mirror type head '{n}'"
      if levels.isEmpty then
        throwError "Type u-sorted mirror sort Obj was rendered without a universe argument"
  | _ => throwError "display local A type is not a mirror constant"
  match mvarDecl.type.getAppFn with
  | .const n _ =>
      unless n == lfMirrorDeclName `GoalDisplaySmoke `Good do
        throwError "display goal target has unexpected head '{n}'"
  | _ => throwError "display goal target is not headed by a mirror constant"
  let some sourceAnchor ← liftCoreM <| lfMirrorSourceDeclAnchorName? `GoalDisplaySmoke `Good
    | throwError "missing source anchor for GoalDisplaySmoke.Good"
  let some sourceRanges ← liftCoreM <| findDeclarationRanges? sourceAnchor
    | throwError "source anchor for GoalDisplaySmoke.Good has no ranges"
  let mirrorName := lfMirrorDeclName `GoalDisplaySmoke `Good
  let some mirrorRanges ← liftCoreM <| findDeclarationRanges? mirrorName
    | throwError "mirror declaration for GoalDisplaySmoke.Good has no ranges"
  unless sourceRanges.selectionRange == mirrorRanges.selectionRange do
    throwError "mirror declaration range does not point at the source declaration"

-- Assert that stale quoted-`by` simulations get an explicit display-only note.
run_cmd do
  let goalDisplayTestTarget : InternalDefTarget := {
    theoryName := `GoalDisplaySmoke
    localName := `displayProbe
    anchorName := `GoalDisplaySmoke.displayProbe }
  let targetExpr : ObjExpr := .app (.app (.ident `Good) (.ident `o)) (.ident `o)
  let snapshot ← liftTermElabM do
    let displayCtx ← prepareInternalGoalDisplayContext goalDisplayTestTarget
    let goal := mkInternalGoalDisplayGoal #[] targetExpr (stale := true)
    mkInternalObjectGoalDisplaySnapshotWithContext goalDisplayTestTarget displayCtx #[goal]
  let some mvarId := snapshot.goals.head? | throwError "missing stale display goal"
  let mvarDecl := snapshot.mctx.getDecl mvarId
  let some noteDecl := mvarDecl.lctx.findFromUserName? `note
    | throwError "stale display goal is missing the note local"
  match noteDecl.type with
  | .const n _ =>
      unless n == ``InternalGoalDisplayStaleNote do
        throwError "stale note has unexpected type '{n}'"
  | _ => throwError "stale note type is not a constant"

declare_type_theory GoalDisplayPrepareOnceSmoke{u} where
  syntax_sort Obj : Type u
  judgment Good (x : Obj)
  lf_opaque o : Obj
  rule good_o : Good o

-- Assert that a prepared display context creates the theory mirror once and snapshot rendering
-- reuses that context without adding more mirror declarations.
run_cmd do
  let target : InternalDefTarget := {
    theoryName := `GoalDisplayPrepareOnceSmoke
    localName := `displayProbe
    anchorName := `GoalDisplayPrepareOnceSmoke.displayProbe }
  let mirrorNames := #[`Obj, `Good, `o, `good_o].map fun n =>
    lfMirrorDeclName `GoalDisplayPrepareOnceSmoke n
  let presentCountCore : CoreM Nat := do
    let env ← getEnv
    pure <| mirrorNames.foldl (init := 0) fun count n =>
      if env.contains n then count + 1 else count
  let before ← liftCoreM presentCountCore
  unless before == 0 do
    throwError "prepare-once smoke theory already had mirror declarations before display prep"
  let (afterPrepare, afterSnapshots) ← liftTermElabM do
    let displayCtx ← prepareInternalGoalDisplayContext target
    let countPresent : TermElabM Nat := do
      let env ← getEnv
      pure <| mirrorNames.foldl (init := 0) fun count n =>
        if env.contains n then count + 1 else count
    let afterPrepare ← countPresent
    let goal := mkInternalGoalDisplayGoal #[] (.app (.ident `Good) (.ident `o))
    let snapshot₁ ← mkInternalObjectGoalDisplaySnapshotWithContext target displayCtx #[goal]
    let snapshot₂ ← mkInternalObjectGoalDisplaySnapshotWithContext target displayCtx #[goal]
    unless snapshot₁.fallbacks.isEmpty && snapshot₂.fallbacks.isEmpty do
      throwError "prepare-once display snapshots unexpectedly used fallback"
    let afterSnapshots ← countPresent
    pure (afterPrepare, afterSnapshots)
  unless afterPrepare == mirrorNames.size do
    throwError "display prep did not create every expected mirror declaration"
  unless afterSnapshots == afterPrepare do
    throwError "display snapshot rendering added mirror declarations after preparation"

-- Assert that unsupported mirror translations fall back to the legacy string-marker goal view.
run_cmd do
  let goalDisplayTestTarget : InternalDefTarget := {
    theoryName := `GoalDisplaySmoke
    localName := `displayProbe
    anchorName := `GoalDisplaySmoke.displayProbe }
  let targetExpr : ObjExpr := .jeq (.ident `o) (.ident `o)
  let snapshot ← liftTermElabM do
    let displayCtx ← prepareInternalGoalDisplayContext goalDisplayTestTarget
    let goal := mkInternalGoalDisplayGoal #[] targetExpr
    mkInternalObjectGoalDisplaySnapshotWithContext goalDisplayTestTarget displayCtx #[goal]
  unless snapshot.fallbacks.any (fun fallback => fallback.kind == `goalTranslation) do
    throwError "judgmental-equality display goal did not record a goal-translation fallback"
  let some mvarId := snapshot.goals.head? | throwError "missing fallback display goal"
  let mvarDecl := snapshot.mctx.getDecl mvarId
  match mvarDecl.type.getAppFn with
  | .const n _ =>
      unless n == ``InternalObjectGoalView do
        throwError "fallback display target has unexpected head '{n}'"
  | _ => throwError "fallback display target is not headed by InternalObjectGoalView"

run_cmd do
  recordInternalGoalDisplayFallbacks (← getRef) #[{
    kind := `unitTest
    message := m!"profile smoke" }]

/--
info: internal goal-display fallback profile for current file:
  unitTest: 1
-/
#guard_msgs in
#print_internal_goal_display_fallback_profile
