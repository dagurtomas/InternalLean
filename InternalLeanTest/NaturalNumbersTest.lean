/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLeanTest.TinyNat

/-!
# Registry/LF regression test for `TinyNat`

The quiet declaration of the direct-LF `TinyNat` object theory lives in `TinyNat.lean`.
This file exercises checked LF metadata storage, LF model-obligation generation, checked
LF theorem replay, and the generic object tactic declarations in that signature.
-/

@[expose] public section

#check_type_theory TinyNat
#print_type_theory TinyNat
#print_logical_framework_metadata TinyNat
#print_checked_logical_framework_metadata TinyNat
#print_checked_logical_framework_environment TinyNat
#print_checked_logical_framework_rules TinyNat
#print_logical_framework_rule_schemas TinyNat
#print_checked_logical_framework_head_usage TinyNat

#print_lf_model_obligations TinyNat
#check_lf_model_obligations TinyNat
#print_lf_model_contract TinyNat
#print_lf_model_summary TinyNat
#print_lf_model_skeleton TinyNat
#print_lf_model_artifacts TinyNat

generate_lf_model_structure TinyNat as TinyNatGeneratedLFModel
#print_lf_model_derived_statements TinyNat for TinyNatGeneratedLFModel
#print_lf_model_derived_theorems TinyNat for TinyNatGeneratedLFModel
#check_lf_model_derived_theorems TinyNat for TinyNatGeneratedLFModel
generate_lf_model_derived_theorems TinyNat for TinyNatGeneratedLFModel

#check TinyNat.TinyNatGeneratedLFModel
#check TinyNat.TinyNatGeneratedLFModel.zero_wf
#check TinyNat.TinyNatGeneratedLFModel.local_wfNat_identity
#check TinyNat.TinyNatGeneratedLFModel.add_zero_zero_eq
#check TinyNat.TinyNatGeneratedLFModel.add_zero_zero_by_refine
#check TinyNat.one_ok_by_tactic
#check TinyNat.add_zero_zero_by_refine

extend_type_theory TinyNat where
  rewrite_relation eqNat [lhs, rhs]
  transport_rule eq_trans for eqNat [left_ok, right_ok]
  transport_position eq_trans : eqNat [0]
  rewrite_symmetry eq_symm for eqNat [eq_ok]
  lf_opaque shadowZero : Nat
  rule shadow_zero_eq : eqNat shadowZero zero

namespace TinyNat

internal def shadow_zero_eq_checked : eqNat shadowZero zero := shadow_zero_eq

internal def shadow_zero_rw_transport : eqNat shadowZero zero := by
  rw shadow_zero_eq_checked
  exact eq_refl zero zero_wf

internal def shadow_zero_rw_reverse_transport : eqNat zero zero := by
  rw ← shadow_zero_eq_checked
  exact shadow_zero_eq_checked

end TinyNat

#check TinyNat.shadow_zero_eq_checked
#check TinyNat.shadow_zero_rw_transport
#check TinyNat.shadow_zero_rw_reverse_transport
