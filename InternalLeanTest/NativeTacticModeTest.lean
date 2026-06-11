/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command
public import Lean.Elab.Tactic

/-!
# Phase 9a native tactic-mode skeleton tests

These tests keep native tactic mode opt-in and check that the Phase 9a live-goal skeleton does
not accept LF declarations before a later milestone finalizes explicit InternalLean proof terms.
-/

@[expose] public section

open Lean Elab Command InternalLean

partial def infoTreeContainsTacticGoal (goal : MVarId) : InfoTree → Bool
  | .context _ tree => infoTreeContainsTacticGoal goal tree
  | .node (.ofTacticInfo info) children =>
      info.goalsBefore.any (· == goal) ||
        children.foldl (fun found tree => found || infoTreeContainsTacticGoal goal tree) false
  | .node _ children =>
      children.foldl (fun found tree => found || infoTreeContainsTacticGoal goal tree) false
  | .hole _ => false

def infoStateContainsTacticGoal (goal : MVarId) (state : InfoState) : Bool :=
  state.trees.foldl (fun found tree => found || infoTreeContainsTacticGoal goal tree) false

declare_type_theory NativeTacticModeSmoke where
  syntax_sort Obj
  judgment Good (x : Obj)
  lf_opaque o : Obj
  rule good_o : Good o

namespace NativeTacticModeSmoke

/--
error: InternalLean native tactic mode is enabled, but Phase 9a only installs the live-goal
skeleton; the tactic block left unsolved InternalLean native goal(s). Core object tactics are
enabled in later Phase 9 milestones.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def skip_incomplete : Good o := by
  skip

/--
error: tactic `decide` is not part of InternalLean native tactic mode yet; supported Phase 9a
skeleton tactic: `skip`. Core object tactics are enabled in later Phase 9 milestones.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def decide_rejected : Good o := by
  decide

/--
error: tactic `constructor` is not part of InternalLean native tactic mode yet; supported Phase 9a
skeleton tactic: `skip`. Core object tactics are enabled in later Phase 9 milestones.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def constructor_rejected : Good o := by
  constructor

/--
error: tactic `try` is not part of InternalLean native tactic mode yet; supported Phase 9a
skeleton tactic: `skip`. Core object tactics are enabled in later Phase 9 milestones.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def try_rejected : Good o := by
  try skip

/--
error: this `by` block parsed as the legacy InternalLean object-tactic language; Phase 9a native
tactic mode only accepts Lean tactic syntax through the quoted body path. Disable
`internalLean.nativeTacticMode` to use the legacy object-tactic compiler.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def legacy_exact_rejected : Good o := by
  exact good_o

syntax (name := nativeTacticModeMacroSorry) "native_macro_sorry" : tactic
macro_rules
  | `(tactic| native_macro_sorry) => `(tactic| exact sorry)

/--
error: tactic `native_macro_sorry` is not part of InternalLean native tactic mode yet; supported
Phase 9a skeleton tactic: `skip`. Core object tactics are enabled in later Phase 9 milestones.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def macro_sorry_rejected : Good o := by
  native_macro_sorry

run_cmd do
  if (← getEnv).contains `NativeTacticModeSmoke.macro_sorry_rejected then
    throwError "macro-generated sorry produced an InternalLean declaration"

run_cmd do
  let target : InternalDefTarget := {
    theoryName := `NativeTacticModeSmoke
    localName := `native_skeleton_probe
    anchorName := `NativeTacticModeSmoke.native_skeleton_probe }
  let some sig ← liftCoreM <| getTheory? target.theoryName
    | throwError "missing test theory"
  let flatSig ← liftCoreM <| flattenSignature sig
  let typeStx ← `(ttExpr| Good o)
  let typeExpr ← elabObjExpr typeStx
  let step ← `(tactic| skip)
  let result ← runInternalNativeTacticSkeleton target flatSig #[] #[] typeExpr #[step.raw]
  if result.session.displayCtx.mirrorError?.isSome then
    throwError "native skeleton test theory unexpectedly used fallback display goals"
  unless result.finalGoals.length == 1 do
    throwError "native skeleton did not preserve the live unsolved display goal"
  let some decl := result.mctx.findDecl? result.initialGoal
    | throwError "native skeleton display metavariable missing from returned context"
  match decl.kind with
  | .syntheticOpaque => pure ()
  | other => throwError "native skeleton display metavariable was not syntheticOpaque: {repr other}"
  unless (result.session.goals.find? result.initialGoal.name).isSome do
    throwError "native skeleton session lost ownership of its display metavariable"
  let infoState ← getInfoState
  unless infoStateContainsTacticGoal result.initialGoal infoState do
    throwError "native skeleton did not emit TacticInfo for the live display metavariable"

set_option internalLean.nativeTacticMode true in
example : True := by
  exact True.intro

end NativeTacticModeSmoke
