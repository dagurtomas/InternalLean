/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command
public import Lean.Elab.Tactic

/-!
# Phase 9 native tactic-mode tests

These tests keep native tactic mode opt-in, check that Lean-native tactics build LF terms only
through InternalLean handlers, and keep unsupported Lean tactics from solving display goals.
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
  judgment Rel (x : Obj) (y : Obj)
  lf_opaque o : Obj
  lf_opaque p : Obj
  rule good_o : Good o
  rule good_twice where
    premise left : Good o
    premise right : Good o
    conclusion : Good o
  rule rel_refl (x : Obj) : Rel x x

namespace NativeTacticModeSmoke

/-- error: InternalLean native tactic block left unsolved object goal(s) -/
#guard_msgs in
set_option internalLean.nativeTacticMode true in
internal def skip_incomplete : Good o := by
  skip

set_option internalLean.nativeTacticMode true in
internal def exact_good : Good o := by
  exact good_o

set_option internalLean.nativeTacticMode true in
internal def intro_id : (x : Obj) → Obj := by
  intro x
  exact x

set_option internalLean.nativeTacticMode true in
internal def intros_const : (x : Obj) → (y : Obj) → Obj := by
  intros x y
  exact x

set_option internalLean.nativeTacticMode true in
internal def assumption_good (h : Good o) : Good o := by
  assumption

set_option internalLean.nativeTacticMode true in
internal def show_good : Good o := by
  show Good o
  exact good_o

set_option internalLean.nativeTacticMode true in
internal def change_good : Good o := by
  change Good o
  exact good_o

set_option internalLean.nativeTacticMode true in
internal def have_good : Good o := by
  have h : Good o := good_o
  exact h

set_option internalLean.nativeTacticMode true in
internal def apply_refl : Rel o o := by
  apply rel_refl

set_option internalLean.nativeTacticMode true in
internal def apply_twice : Good o := by
  apply good_twice
  exact good_o
  exact good_o

set_option internalLean.nativeTacticMode true in
internal theorem exact_theorem : Good o := by
  exact good_o

#check exact_good
#check intro_id
#check intros_const
#check assumption_good
#check show_good
#check change_good
#check have_good
#check apply_refl
#check apply_twice
#check exact_theorem

/--
warning: internal declaration 'NativeTacticModeSmoke.direct_sorry_admitted' was admitted by
`sorry`; the annotation was checked in theory 'NativeTacticModeSmoke', but the body was not checked.
Use `#lint_type_theory_sorries NativeTacticModeSmoke` to list current admissions.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def direct_sorry_admitted : Good o := by
  sorry

/--
error: tactic `decide` is not part of InternalLean native tactic mode yet; supported native tactics
in this milestone: `intro`, `intros`, `exact`, `apply`, `assumption`, `show`, `change`, term-form
`have`, and `skip`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def decide_rejected : Good o := by
  decide

/--
error: tactic `constructor` is not part of InternalLean native tactic mode yet; supported native
tactics in this milestone: `intro`, `intros`, `exact`, `apply`, `assumption`, `show`, `change`,
term-form `have`, and `skip`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def constructor_rejected : Good o := by
  constructor

/--
error: tactic `try` is not part of InternalLean native tactic mode yet; supported native tactics in
this milestone: `intro`, `intros`, `exact`, `apply`, `assumption`, `show`, `change`, term-form
`have`, and `skip`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def try_rejected : Good o := by
  try skip

/--
error: tactic `rfl` is not part of InternalLean native tactic mode yet; supported native tactics in
this milestone: `intro`, `intros`, `exact`, `apply`, `assumption`, `show`, `change`, term-form
`have`, and `skip`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def rfl_rejected : Good o := by
  rfl

syntax (name := nativeTacticModeMacroSorry) "native_macro_sorry" : tactic
macro_rules
  | `(tactic| native_macro_sorry) => `(tactic| exact sorry)

/--
error: tactic `native_macro_sorry` is not part of InternalLean native tactic mode yet; supported
native tactics in this milestone: `intro`, `intros`, `exact`, `apply`, `assumption`, `show`,
`change`, term-form `have`, and `skip`.
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
