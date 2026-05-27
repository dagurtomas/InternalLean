/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Intro-exercise UX regression tests

Focused tests for the editor and surface-syntax improvements motivated by the introductory
exercise file.
-/

@[expose] public section

open Lean

namespace InternalLeanTest.IntroUXTest

#guard
  let sig : InternalLean.HLSignature := {
    name := `HoverSmoke,
    rules := #[{ name := `reach_refl, conclusionExpr := .app (.ident `Reach) (.ident `x) }] }
  let target : InternalLean.InternalDefTarget := {
    theoryName := `HoverSmoke, localName := `demo, anchorName := `demo }
  match InternalLean.internalObjectHover? target sig { target := .ident `Goal } `reach_refl with
  | some hover => hover.kind == "rule" && hover.name == `reach_refl
  | none => false

end InternalLeanTest.IntroUXTest

declare_type_theory IntroUXSmoke where
  syntax_sort Node
  judgment Step (src : Node) (tgt : Node)
  judgment Reach (src : Node) (tgt : Node)
  lf_opaque start : Node
  lf_opaque mid : Node
  lf_opaque finish : Node
  rule step_start_mid : Step start mid
  rule step_mid_finish : Step mid finish
  rule reach_refl (x : Node) : Reach x x
  rule reach_of_step (src : Node) (tgt : Node) where
    premise edge : Step src tgt
    conclusion : Reach src tgt
  rule reach_trans (src : Node) (via : Node) (tgt : Node) where
    premise left : Reach src via
    premise right : Reach via tgt
    conclusion : Reach src tgt
  judgment_theorem reach_start_mid : Reach start mid :=
    reach_of_step start mid step_start_mid

generate_lf_model_structure IntroUXSmoke as IntroUXModel

generate_lf_model_derived_theorems IntroUXSmoke for IntroUXModel

namespace IntroUXSmoke

internal def direct_placeholder : Reach mid finish :=
  reach_of_step _ _ step_mid_finish

internal def direct_placeholder_nested : Reach start finish :=
  reach_trans _ mid _ reach_start_mid direct_placeholder

internal def have_term_mode : Reach start finish := by
  have left : Reach start mid := reach_start_mid
  have right : Reach mid finish := reach_of_step mid finish step_mid_finish
  exact reach_trans start mid finish left right

/-- error: object tactic `have h` is missing `end`; write `have h : ... := by ... end` or use
term-mode `have h : ... := proof` -/
#guard_msgs (whitespace := lax) in
internal def bad_have_missing_end : Reach start mid := by
  have h : Reach start mid := by
    exact reach_start_mid
  exact h

internal_defs where
  def batch_node : Node := mid
  def batch_refl : Reach batch_node batch_node := by
    apply reach_refl
  def batch_have : Reach start finish := by
    have left : Reach start mid := reach_start_mid
    exact reach_trans start mid finish left direct_placeholder

#guard_msgs (drop warning) in
internal def admitted_refl (x : Node) : Reach x x := by
  sorry

#guard_msgs (drop warning) in
internal def admitted_compose
    (src : Node) (via : Node) (tgt : Node)
    (left : Reach src via) (right : Reach via tgt) : Reach src tgt := by
  sorry

end IntroUXSmoke

generate_lf_model_transports IntroUXSmoke only
  direct_placeholder_nested
  have_term_mode
  batch_refl
  batch_have
for IntroUXModel

#guard_msgs (drop warning) in
generate_model_transport IntroUXSmoke admitted_refl for IntroUXModel

#guard_msgs (drop warning) in
generate_model_transport IntroUXSmoke admitted_compose for IntroUXModel

#check IntroUXSmoke.IntroUXModel.direct_placeholder
#check IntroUXSmoke.IntroUXModel.direct_placeholder_nested
#check IntroUXSmoke.IntroUXModel.have_term_mode
#check IntroUXSmoke.IntroUXModel.batch_refl
#check IntroUXSmoke.IntroUXModel.batch_have
#check IntroUXSmoke.IntroUXModel.admitted_refl
#check IntroUXSmoke.IntroUXModel.admitted_compose

namespace InternalLeanTest.IntroUXTest

/-- Concrete model used only to check generated admitted transport types. -/
def unitModel : IntroUXSmoke.IntroUXModel where
  Node := Unit
  Step := fun _ _ => Unit
  Reach := fun _ _ => Unit
  start := ()
  mid := ()
  finish := ()
  step_start_mid := ()
  step_mid_finish := ()
  reach_refl := fun _ => ()
  reach_of_step := fun _ _ _ => ()
  reach_trans := fun _ _ _ _ _ => ()

example (x : unitModel.Node) : unitModel.Reach x x :=
  IntroUXSmoke.IntroUXModel.admitted_refl unitModel x

example (x y z : unitModel.Node) (left : unitModel.Reach x y) (right : unitModel.Reach y z) :
    unitModel.Reach x z :=
  IntroUXSmoke.IntroUXModel.admitted_compose unitModel x y z left right

end InternalLeanTest.IntroUXTest
