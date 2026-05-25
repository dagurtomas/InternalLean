/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLeanTest.TinyNat

/-!
# Concrete LF model smoke test for `TinyNat`

This file instantiates the generated LF model interface for the direct-LF `TinyNat`
signature with Lean natural numbers. Model coverage goes through the generic LF model backend and
checked LF theorem replay.
-/

@[expose] public section

generate_lf_model_structure TinyNat as TinyNatModelInterface

generate_lf_model_derived_theorems TinyNat for TinyNatModelInterface

generate_model_transport TinyNat add_comm for TinyNatModelInterface

namespace TinyNat

/-- Left-recursive addition matching the internal LF definition of `TinyNat.add`. -/
def addL : Nat → Nat → Nat
  | Nat.zero, rhs => rhs
  | Nat.succ lhs, rhs => Nat.succ (addL lhs rhs)

/-- A concrete Lean `Nat` model of the direct-LF `TinyNat` signature. -/
def leanNatModel : TinyNatModelInterface where
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

/-- Checked LF theorem replay specializes to ordinary Lean equality in the concrete model. -/
theorem leanNat_add_zero_zero : addL Nat.zero Nat.zero = Nat.zero :=
  (TinyNatModelInterface.add_zero_zero_eq leanNatModel).down

/-- Checked LF theorem replay also covers tactic-authored internal LF declarations. -/
theorem leanNat_add_zero_zero_by_refine : addL Nat.zero Nat.zero = Nat.zero :=
  (TinyNatModelInterface.add_zero_zero_by_refine leanNatModel).down

/-- The internal `add_comm` proof interprets to Lean commutativity for the concrete model. -/
theorem leanNat_add_comm_internal (n m : Nat) :
    (fun lhs rhs => leanNatModel.natRec rhs leanNatModel.succStep lhs) n m =
      (fun lhs rhs => leanNatModel.natRec rhs leanNatModel.succStep lhs) m n :=
  (TinyNatModelInterface.add_comm leanNatModel n m).down

end TinyNat
