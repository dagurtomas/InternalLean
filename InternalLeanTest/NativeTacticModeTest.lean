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
internal def apply_twice_bullets : Good o := by
  apply good_twice
  · exact good_o
  · exact good_o

set_option internalLean.nativeTacticMode true in
internal def refine_twice_bullets : Good o := by
  refine good_twice ?_ ?_
  · exact good_o
  · exact good_o

set_option internalLean.nativeTacticMode true in
internal def apply_twice_focus_lean : Good o := (by
  apply good_twice
  · exact good_o
  · exact good_o)

set_option internalLean.nativeTacticMode true in
internal def refine_twice_focus_lean : Good o := (by
  refine good_twice ?left ?right
  · exact good_o
  · exact good_o)

set_option internalLean.nativeTacticMode true in
internal def have_good_by_end : Good o := by
  have h : Good o := by
    exact good_o
  end
  exact h

set_option internalLean.nativeTacticMode true in
internal def have_good_by_lean : Good o := (by
  have h : Good o := by
    exact good_o
  exact h)

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
#check apply_twice_bullets
#check refine_twice_bullets
#check apply_twice_focus_lean
#check refine_twice_focus_lean
#check have_good_by_end
#check have_good_by_lean
#check exact_theorem

/--
error: native tactic `refine good_twice` cannot infer placeholder `_` for a premise; write an
explicit proof term or `?_`.

Omitted explicit arguments are never turned into subgoals. Use `_` only for inferable parameters,
and write `?_` exactly where `refine` should create an object-theory subgoal.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def refine_infer_placeholder_rejected : Good o := by
  refine good_twice _ _
  exact good_o
  exact good_o

/--
error: tactic `decide` is not part of InternalLean native tactic mode yet; supported native tactics
in this milestone: `intro`, `intros`, `exact`, `apply`, `refine`, `assumption`, `show`,
`change`, `rw`, `simp`, term- and tactic-form `have`, focus bullets, and `skip`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def nested_have_decide_rejected : Good o := (by
  have h : Good o := by
    decide
  exact h)

/--
error: tactic `try` is not part of InternalLean native tactic mode yet; supported native tactics in
this milestone: `intro`, `intros`, `exact`, `apply`, `refine`, `assumption`, `show`,
`change`, `rw`, `simp`, term- and tactic-form `have`, focus bullets, and `skip`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def nested_have_try_rejected : Good o := (by
  have h : Good o := by
    try skip
  exact h)

/--
error: tactic `decide` is not part of InternalLean native tactic mode yet; supported native tactics
in this milestone: `intro`, `intros`, `exact`, `apply`, `refine`, `assumption`, `show`,
`change`, `rw`, `simp`, term- and tactic-form `have`, focus bullets, and `skip`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def focused_apply_decide_rejected : Good o := (by
  apply good_twice
  · decide
  · exact good_o)

/--
error: tactic `try` is not part of InternalLean native tactic mode yet; supported native tactics in
this milestone: `intro`, `intros`, `exact`, `apply`, `refine`, `assumption`, `show`,
`change`, `rw`, `simp`, term- and tactic-form `have`, focus bullets, and `skip`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def focused_refine_try_rejected : Good o := (by
  refine good_twice ?left ?right
  · try skip
  · exact good_o)

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
in this milestone: `intro`, `intros`, `exact`, `apply`, `refine`, `assumption`, `show`,
`change`, `rw`, `simp`, term- and tactic-form `have`, focus bullets, and `skip`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def decide_rejected : Good o := by
  decide

/--
error: tactic `constructor` is not part of InternalLean native tactic mode yet; supported native
tactics in this milestone: `intro`, `intros`, `exact`, `apply`, `refine`, `assumption`,
`show`, `change`, `rw`, `simp`, term- and tactic-form `have`, focus bullets, and `skip`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def constructor_rejected : Good o := by
  constructor

/--
error: tactic `try` is not part of InternalLean native tactic mode yet; supported native tactics in
this milestone: `intro`, `intros`, `exact`, `apply`, `refine`, `assumption`, `show`,
`change`, `rw`, `simp`, term- and tactic-form `have`, focus bullets, and `skip`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def try_rejected : Good o := by
  try skip

/--
error: tactic `rfl` is not part of InternalLean native tactic mode yet; supported native tactics in
this milestone: `intro`, `intros`, `exact`, `apply`, `refine`, `assumption`, `show`,
`change`, `rw`, `simp`, term- and tactic-form `have`, focus bullets, and `skip`.
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
native tactics in this milestone: `intro`, `intros`, `exact`, `apply`, `refine`,
`assumption`, `show`, `change`, `rw`, `simp`, term- and tactic-form `have`, focus bullets,
and `skip`.
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

declare_type_theory NativeTacticModeRewriteSmoke where
  syntax_sort Obj
  judgment Rel (x : Obj) (y : Obj)
  judgment EqObj (x : Obj) (y : Obj)
  judgment Wf (x : Obj)
  judgment Cert (x : Obj)
  judgment_role EqObj : term_conversion
  rewrite_relation EqObj [x, y]
  side_condition_solver trivial_side_condition
  lf_opaque a : Obj
  lf_opaque b : Obj
  lf_opaque f (x : Obj) : Obj
  lf_def aliasA : Obj := a
  rule rel_refl (x : Obj) : Rel x x
  rule rel_fb : Rel (f b) b
  rule wf_a : Wf a
  rule wf_b : Wf b
  rule wf_f (x : Obj) where
    premise source : Wf x
    conclusion : Wf (f x)
  rule rel_transport_left (x : Obj) (y : Obj) (z : Obj) where
    premise eq : EqObj x y
    premise source : Rel y z
    premise target_ok : Wf x
    side_condition ok by trivial_side_condition : Cert x
    conclusion : Rel x z
  transport_rule rel_transport_left for EqObj [eq, source]
  transport_position rel_transport_left : Rel [0]
  rule eq_symm (x : Obj) (y : Obj) where
    premise e : EqObj x y
    premise target_ok : Wf y
    side_condition ok by trivial_side_condition : Cert y
    conclusion : EqObj y x
  rewrite_symmetry eq_symm for EqObj [e]
  rule eq_f_congr (x : Obj) (y : Obj) where
    premise e : EqObj x y
    premise source_ok : Wf x
    side_condition ok by trivial_side_condition : Cert x
    conclusion : EqObj (f x) (f y)
  rewrite_congruence eq_f_congr for EqObj under f [0] [e]
  rule eq_aliasA_to_a : EqObj aliasA a
  rule_role eq_aliasA_to_a : computation
  rule eq_a_to_b : EqObj a b
  rule_role eq_a_to_b : computation

namespace NativeTacticModeRewriteSmoke

set_option internalLean.nativeTacticMode true in
internal def rw_alias_lean : Rel aliasA aliasA := (by
  rw [eq_aliasA_to_a]
  exact rel_refl a)

set_option internalLean.nativeTacticMode true in
internal def rw_alias_legacy : Rel aliasA aliasA := by
  rw eq_aliasA_to_a
  exact rel_refl a

set_option internalLean.nativeTacticMode true in
internal def rw_transport_lean : Rel a b := (by
  rw [eq_a_to_b]
  exact rel_refl b)

set_option internalLean.nativeTacticMode true in
internal def rw_reverse_transport_lean : Rel b b := (by
  rw [← eq_a_to_b]
  exact rw_transport_lean)

set_option internalLean.nativeTacticMode true in
internal def rw_nested_congr_transport_lean : Rel (f a) b := (by
  rw [eq_a_to_b]
  exact rel_fb)

set_option internalLean.nativeTacticMode true in
internal def simp_transport_lean : Rel a b := (by
  simp [eq_a_to_b]
  exact rel_refl b)

set_option internalLean.nativeTacticMode true in
internal def simp_only_definition_lean : Rel aliasA aliasA := (by
  simp only [aliasA]
  exact rel_refl a)

set_option internalLean.nativeTacticMode true in
internal def simp_nested_congr_transport_lean : Rel (f a) b := (by
  simp only [eq_a_to_b]
  exact rel_fb)

/-- error: object tactic `rw []` failed: rewrite list is empty -/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def rw_empty_rejected : Rel a a := (by
  rw []
  exact rel_refl a)

/-- error: native tactic `simp` supports only `simp`, `simp [name, ...]`, and
`simp only [name, ...]` in this milestone; unsupported Lean simp features include wildcard
simp sets (`*`), erased lemmas (`-foo`), reverse lemmas (`← foo`), configurations/dischargers,
and `simp at` locations. -/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def simp_star_rejected : Rel aliasA aliasA := (by
  simp [*]
  exact rel_refl aliasA)

/-- error: native tactic `simp` supports only `simp`, `simp [name, ...]`, and
`simp only [name, ...]` in this milestone; unsupported Lean simp features include wildcard
simp sets (`*`), erased lemmas (`-foo`), reverse lemmas (`← foo`), configurations/dischargers,
and `simp at` locations. -/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def simp_only_star_rejected : Rel aliasA aliasA := (by
  simp only [*, aliasA]
  exact rel_refl aliasA)

/-- error: native tactic `simp` supports only `simp`, `simp [name, ...]`, and
`simp only [name, ...]` in this milestone; unsupported Lean simp features include wildcard
simp sets (`*`), erased lemmas (`-foo`), reverse lemmas (`← foo`), configurations/dischargers,
and `simp at` locations. -/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def simp_erase_rejected : Rel aliasA aliasA := (by
  simp [-aliasA]
  exact rel_refl aliasA)

/-- error: native tactic `simp` supports only `simp`, `simp [name, ...]`, and
`simp only [name, ...]` in this milestone; unsupported Lean simp features include wildcard
simp sets (`*`), erased lemmas (`-foo`), reverse lemmas (`← foo`), configurations/dischargers,
and `simp at` locations. -/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def simp_reverse_rejected : Rel aliasA aliasA := (by
  simp [← aliasA]
  exact rel_refl aliasA)

/-- error: native tactic `simp` supports only `simp`, `simp [name, ...]`, and
`simp only [name, ...]` in this milestone; unsupported Lean simp features include wildcard
simp sets (`*`), erased lemmas (`-foo`), reverse lemmas (`← foo`), configurations/dischargers,
and `simp at` locations. -/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def simp_config_rejected : Rel aliasA aliasA := (by
  simp (config := {}) [aliasA]
  exact rel_refl aliasA)

/-- error: native tactic `simp` supports only `simp`, `simp [name, ...]`, and
`simp only [name, ...]` in this milestone; unsupported Lean simp features include wildcard
simp sets (`*`), erased lemmas (`-foo`), reverse lemmas (`← foo`), configurations/dischargers,
and `simp at` locations. -/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def simp_discharger_rejected : Rel aliasA aliasA := (by
  simp (discharger := assumption) [aliasA]
  exact rel_refl aliasA)

/-- error: native tactic `simp` supports only `simp`, `simp [name, ...]`, and
`simp only [name, ...]` in this milestone; unsupported Lean simp features include wildcard
simp sets (`*`), erased lemmas (`-foo`), reverse lemmas (`← foo`), configurations/dischargers,
and `simp at` locations. -/
#guard_msgs (whitespace := lax) in
set_option internalLean.nativeTacticMode true in
internal def simp_at_rejected : Rel aliasA aliasA := (by
  have h : Rel aliasA aliasA := rel_refl aliasA
  simp at h
  exact h)

#check rw_alias_lean
#check rw_alias_legacy
#check rw_transport_lean
#check rw_reverse_transport_lean
#check rw_nested_congr_transport_lean
#check simp_transport_lean
#check simp_only_definition_lean
#check simp_nested_congr_transport_lean

run_cmd do
  let target : InternalDefTarget := {
    theoryName := `NativeTacticModeRewriteSmoke
    localName := `native_rw_display_probe
    anchorName := `NativeTacticModeRewriteSmoke.native_rw_display_probe }
  let some sig ← liftCoreM <| getTheory? target.theoryName
    | throwError "missing native rewrite test theory"
  let flatSig ← liftCoreM <| flattenSignature sig
  let typeStx ← `(ttExpr| Rel aliasA aliasA)
  let typeExpr ← elabObjExpr typeStx
  let rwStep ← `(tactic| rw [eq_aliasA_to_a])
  let resolved ← elabInternalNativeResolvedSteps target flatSig #[] #[] typeExpr #[rwStep.raw]
  let result ← runInternalNativeResolvedTactic target flatSig #[] #[] typeExpr resolved
  unless result.session.fallbacks.isEmpty do
    throwError "native rw display unexpectedly used fallback display goals"
  unless result.finalGoals.length == 1 do
    throwError "native rw display probe did not leave exactly one rewritten goal"

end NativeTacticModeRewriteSmoke
