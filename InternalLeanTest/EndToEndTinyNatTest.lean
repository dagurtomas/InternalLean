/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLeanTest.TinyNat

/-!
# End-to-end LF interpretation smoke test for `TinyNat`

This is the focused golden-path test for the direct-LF `TinyNat` fixture:

1. import a direct-LF object theory,
2. generate its generic LF model interface,
3. define a concrete Lean model, and
4. replay checked LF theorem/internal-tactic declarations over the model.
-/

@[expose] public section

generate_lf_model_structure TinyNat as TinyNatE2EModel

generate_lf_model_derived_theorems TinyNat for TinyNatE2EModel

generate_model_transport TinyNat add_comm for TinyNatE2EModel

namespace InternalLeanTest.EndToEndTinyNatTest

/-- Left-recursive addition matching the internal LF definition of `TinyNat.add`. -/
def addL : Nat → Nat → Nat
  | Nat.zero, rhs => rhs
  | Nat.succ lhs, rhs => Nat.succ (addL lhs rhs)

/-- A concrete Lean `Nat` model of the generated LF `TinyNat` interface. -/
def natModel : TinyNat.TinyNatE2EModel where
  Nat := Nat
  NatRecursor := Nat → Nat → Nat
  Eq := fun lhs rhs => PLift (lhs = rhs)
  wfNat := fun _ => Unit
  wfRecursor := fun _ => Unit
  eqNat := fun lhs rhs => PLift (lhs = rhs)
  zero := Nat.zero
  succ := Nat.succ
  succStep := fun _ ih => Nat.succ ih
  recStep := fun step n ih => step n ih
  natRec := fun base step n => Nat.rec base (fun n ih => step n ih) n
  reflProof := fun _ => ⟨rfl⟩
  symmProof := fun _ _ p => ⟨p.down.symm⟩
  transProof := fun _ _ _ p q => ⟨p.down.trans q.down⟩
  apSuccProof := fun _ _ p => ⟨congrArg Nat.succ p.down⟩
  natIndProof := fun _ base step n => Nat.rec base (fun n ih => step n ih) n
  betaNatZeroProof := fun _ _ => ⟨rfl⟩
  betaNatSuccProof := fun _ _ _ => ⟨rfl⟩
  succStepBetaProof := fun _ _ => ⟨rfl⟩
  zero_intro := ()
  succ_intro := fun _ _ => ()
  succ_step_intro := ()
  rec_step_intro := fun _ _ _ _ _ _ => ()
  nat_rec_elim := fun _ _ _ _ _ _ => ()
  eq_refl := fun _ _ => ⟨rfl⟩
  eq_symm := fun _ _ eq_ok => ⟨eq_ok.down.symm⟩
  eq_trans := fun _ _ _ left_ok right_ok => ⟨left_ok.down.trans right_ok.down⟩
  succ_step_beta := fun _ _ _ _ => ⟨rfl⟩
  beta_nat_zero := fun _ _ _ _ => ⟨rfl⟩
  beta_nat_succ := fun _ _ _ _ _ _ => ⟨rfl⟩

#check TinyNat.TinyNatE2EModel
#check TinyNat.TinyNatE2EModel.zero_wf
#check TinyNat.TinyNatE2EModel.add_zero_zero_eq
#check TinyNat.TinyNatE2EModel.add_zero_zero_by_refine
#check TinyNat.TinyNatE2EModel.double_two_wf

example :
  natModel.eqNat (natModel.natRec natModel.zero natModel.succStep natModel.zero) natModel.zero :=
  TinyNat.TinyNatE2EModel.add_zero_zero_eq natModel

example : addL Nat.zero Nat.zero = Nat.zero :=
  (TinyNat.TinyNatE2EModel.add_zero_zero_eq natModel).down

example : addL Nat.zero Nat.zero = Nat.zero :=
  (TinyNat.TinyNatE2EModel.add_zero_zero_by_refine natModel).down

example : natModel.wfNat ((fun n => (fun lhs rhs =>
  natModel.natRec rhs natModel.succStep lhs) n n) (natModel.succ (natModel.succ natModel.zero))) :=
  TinyNat.TinyNatE2EModel.double_two_wf natModel

example (n m : Nat) :
    (fun lhs rhs => natModel.natRec rhs natModel.succStep lhs) n m =
      (fun lhs rhs => natModel.natRec rhs natModel.succStep lhs) m n :=
  (TinyNat.TinyNatE2EModel.add_comm natModel n m).down

end InternalLeanTest.EndToEndTinyNatTest
