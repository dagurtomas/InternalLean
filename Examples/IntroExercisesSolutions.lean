/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Examples.IntroExercises

/-!
# Solutions for `Examples/IntroExercises.lean`

This file contains worked solutions and a small model workflow for the introductory exercises.
Try the exercises before reading this file.
-/

@[expose] public section

namespace IntroReach

internal def solution01_start_reaches_start : Reach start start := by
  exact reach_refl start

internal def solution02_mid_reaches_finish : Reach mid finish := by
  exact reach_of_step mid finish step_mid_finish

internal def solution03_start_reaches_finish : Reach start finish := by
  refine reach_trans start mid finish ?_ ?_
  · exact reach_start_mid
  · exact solution02_mid_reaches_finish

internal def solution04_refl_function (x : Node) : Reach x x := by
  exact reach_refl x

internal def solution05_assumption (x : Node) (h : Reach x finish) : Reach x finish := by
  assumption

internal def solution06_direct_term : Reach start finish :=
  reach_trans start mid finish reach_start_mid solution02_mid_reaches_finish

internal def solution07_have_blocks : Reach start finish := by
  have left : Reach start mid := by
    exact reach_start_mid
  end
  have right : Reach mid finish := by
    exact solution02_mid_reaches_finish
  end
  exact reach_trans start mid finish left right

internal def solution08_const_start_function : (x : Node) → Node := by
  intro x
  exact start

internal def solution09_last_node : Node := finish

internal def solution09_change_alias : Reach solution09_last_node solution09_last_node := by
  change Reach finish finish
  exact reach_refl finish

internal def solution10_compose_parameterized
    (src : Node) (via : Node) (tgt : Node)
    (left : Reach src via) (right : Reach via tgt) : Reach src tgt := by
  exact reach_trans src via tgt left right

internal_defs where
  def solution11_batch_node : Node := mid
  def solution11_batch_refl : Reach solution11_batch_node solution11_batch_node :=
    reach_refl solution11_batch_node

end IntroReach

/-!
## Model workflow

A model interprets the checked type theory in Lean. `IntroReachModel` asks a user to provide Lean
data for the node sort, the judgments, and the primitive rules. The transport commands below
replay selected checked internal declarations over any Lean model.
-/

generate_lf_model_transports IntroReach only
  solution02_mid_reaches_finish
  solution03_start_reaches_finish
  solution04_refl_function
  solution06_direct_term
  solution07_have_blocks
  solution08_const_start_function
  solution10_compose_parameterized
for IntroReachModel

namespace IntroReachExercises

/-!
The generated methods replay checked InternalLean declarations over the Lean model from the
exercise file.
-/

#check IntroReach.IntroReachModel.reach_start_mid
#check IntroReach.IntroReachModel.solution02_mid_reaches_finish
#check IntroReach.IntroReachModel.solution03_start_reaches_finish
#check IntroReach.IntroReachModel.solution04_refl_function
#check IntroReach.IntroReachModel.solution08_const_start_function
#check IntroReach.IntroReachModel.solution10_compose_parameterized

example : unitModel.Reach unitModel.start unitModel.finish :=
  IntroReach.IntroReachModel.solution03_start_reaches_finish unitModel

example (x : unitModel.Node) : unitModel.Reach x x :=
  IntroReach.IntroReachModel.solution04_refl_function unitModel x

example : unitModel.Reach unitModel.start unitModel.finish :=
  IntroReach.IntroReachModel.solution06_direct_term unitModel

example : unitModel.Node :=
  IntroReach.IntroReachModel.solution08_const_start_function unitModel unitModel.finish

example (x y z : unitModel.Node) (left : unitModel.Reach x y) (right : unitModel.Reach y z) :
    unitModel.Reach x z :=
  IntroReach.IntroReachModel.solution10_compose_parameterized unitModel x y z left right

end IntroReachExercises
