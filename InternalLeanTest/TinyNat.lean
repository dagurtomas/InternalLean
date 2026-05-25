/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# The `TinyNat` LF object theory

`TinyNat` is a deliberately small direct-LF arithmetic fixture. It presents every primitive
object-theory ingredient as LF metadata. Derived arithmetic such as addition is defined later with
`internal def`, so models only have to interpret the primitive natural-number language and its
rules.

## Primitive syntax and judgments

The signature has three object sorts.

* `Nat` is the sort of object-theory natural-number terms.
* `NatRecursor` packages the step operation used by the first-order recursor.
* `Eq lhs rhs` is a proof-object family for internal propositional equality proofs between
  natural-number terms.  It is separate from the judgment `eqNat lhs rhs`: `eqNat` is the
  conversion judgment used by the checker/model interface, while `Eq` lets internal
  arithmetic proofs such as `add_comm` be ordinary LF objects.

The primitive judgments are:

* `wfNat n`, asserting that an object natural number is wellformed;
* `wfRecursor r`, asserting that a recursor step is wellformed;
* `eqNat lhs rhs`, the object-theory equality/conversion judgment on naturals.

## Natural-number formation and computation

The natural-number constructors are `zero` and `succ`.  Their wellformedness rules are
`zero_intro` and `succ_intro`.

Recursion is intentionally first-order.  A value `r : NatRecursor` is applied by
`recStep r n ih`, where `n` is the predecessor and `ih` is the recursive result.  The term
`natRec base step n` computes by recursion on `n`, returning `base` at zero and using
`recStep step n (natRec base step n)` at a successor.  The rules are:

* `succ_step_intro`, making the distinguished `succStep` a valid recursor step;
* `rec_step_intro`, wellformedness for applying a recursor step;
* `nat_rec_elim`, wellformedness for `natRec`;
* `beta_nat_zero`, the zero computation rule;
* `beta_nat_succ`, the successor computation rule;
* `succ_step_beta`, explaining the special step `succStep` by
  `recStep succStep n ih = succ ih`.

With these primitives, addition is the internal definition
`add lhs rhs := natRec rhs succStep lhs`.  Thus addition recurses on the left argument and
uses the right argument as the base case.  The derived lemmas `add_zero_left`,
`add_zero_right`, `add_succ_right`, and `add_comm` are internal LF proof objects built
from the primitive proof constructors and induction principle below.

## Internal proof objects

The proof heads `reflProof`, `symmProof`, `transProof`, and `apSuccProof` provide equality
reasoning for the `Eq` family.  `natIndProof` is an LF-level induction principle:
for a family `P : Nat → Type`, it consumes a zero case, a successor step, and a natural
number `n`, then returns a term of `P n`.  The proof heads `betaNatZeroProof`,
`betaNatSuccProof`, and `succStepBetaProof` mirror the computation rules as objects in
`Eq`, so internal arithmetic proofs can reason about `natRec` without becoming primitive
rules or model fields.
-/

@[expose] public section

declare_type_theory TinyNat where
  /--
  Natural-number terms.

  ```text
  ───────────── Nat-sort
  Nat sort
  ```
  -/
  syntax_sort Nat

  /--
  First-order natural-number recursion steps.

  A value `r : NatRecursor` can be applied as `recStep r n ih`, where `n` is the
  predecessor and `ih` is the already-computed recursive result.

  ```text
  ─────────────────── NatRecursor-sort
  NatRecursor sort
  ```
  -/
  syntax_sort NatRecursor

  /--
  Internal proof objects for equality of natural-number terms.

  ```text
  lhs : Nat    rhs : Nat
  ────────────────────── Eq-sort
  Eq lhs rhs sort
  ```
  -/
  syntax_sort Eq (lhs : Nat) (rhs : Nat)

  syntax_sort_role Nat : term_sort

  /--
  Wellformed natural-number terms.

  ```text
  n : Nat
  ───────── wfNat-judgment
  wfNat n judgment
  ```
  -/
  judgment wfNat (n : Nat)

  /--
  Wellformed first-order recursor steps.

  ```text
  r : NatRecursor
  ─────────────────── wfRecursor-judgment
  wfRecursor r judgment
  ```
  -/
  judgment wfRecursor (r : NatRecursor)

  /--
  Object-theory equality/conversion judgment on natural numbers.

  ```text
  lhs : Nat    rhs : Nat
  ────────────────────── eqNat-judgment
  eqNat lhs rhs judgment
  ```
  -/
  judgment eqNat (lhs : Nat) (rhs : Nat)

  judgment_role wfNat : term_typing
  judgment_role eqNat : term_conversion

  /--
  Zero is a primitive natural-number term.

  ```text
  ───────── zero-constant
  zero : Nat
  ```
  -/
  lf_opaque zero : Nat

  /--
  Successor is a primitive natural-number term former.

  ```text
  n : Nat
  ───────────── succ-constant
  succ n : Nat
  ```
  -/
  lf_opaque succ (n : Nat) : Nat

  /--
  The distinguished recursion step used by addition.

  ```text
  ───────────────────────── succStep-constant
  succStep : NatRecursor
  ```
  -/
  lf_opaque succStep : NatRecursor

  /--
  Apply a first-order recursor step to a predecessor and recursive result.

  ```text
  r : NatRecursor    n : Nat    ih : Nat
  ─────────────────────────────────────── recStep-constant
  recStep r n ih : Nat
  ```
  -/
  lf_opaque recStep (r : NatRecursor) (n : Nat) (ih : Nat) : Nat

  /--
  Primitive first-order natural-number recursion.

  ```text
  base : Nat    step : NatRecursor    n : Nat
  ───────────────────────────────────────────── natRec-constant
  natRec base step n : Nat
  ```
  -/
  lf_opaque natRec (base : Nat) (step : NatRecursor) (n : Nat) : Nat

  /--
  Reflexivity as an internal equality proof object.

  ```text
  n : Nat
  ───────────────── reflProof
  reflProof n : Eq n n
  ```
  -/
  lf_opaque reflProof (n : Nat) : Eq n n

  /--
  Symmetry for internal equality proof objects.

  ```text
  p : Eq lhs rhs
  ───────────────────────────── symmProof
  symmProof lhs rhs p : Eq rhs lhs
  ```
  -/
  lf_opaque symmProof (lhs : Nat) (rhs : Nat) (p : Eq lhs rhs) : Eq rhs lhs

  /--
  Transitivity for internal equality proof objects.

  ```text
  p : Eq lhs mid    q : Eq mid rhs
  ───────────────────────────────────────── transProof
  transProof lhs mid rhs p q : Eq lhs rhs
  ```
  -/
  lf_opaque transProof (lhs : Nat) (mid : Nat) (rhs : Nat) (p : Eq lhs mid) (q : Eq mid rhs) :
    Eq lhs rhs

  /--
  Congruence of successor for internal equality proof objects.

  ```text
  p : Eq lhs rhs
  ─────────────────────────────────── apSuccProof
  apSuccProof lhs rhs p : Eq (succ lhs) (succ rhs)
  ```
  -/
  lf_opaque apSuccProof (lhs : Nat) (rhs : Nat) (p : Eq lhs rhs) : Eq (succ lhs) (succ rhs)

  /--
  Natural-number induction as an internal proof-object former.

  ```text
  P : Nat → Type
  base : P zero
  step : (n : Nat) → P n → P (succ n)
  n : Nat
  ───────────────────────────────────────── natIndProof
  natIndProof P base step n : P n
  ```
  -/
  lf_opaque natIndProof
    (P : Nat → Type)
    (base : P zero)
    (step : (n : Nat) → P n → P (succ n))
    (n : Nat) : P n

  /--
  Internal proof-object version of the zero computation rule for `natRec`.

  ```text
  base : Nat    step : NatRecursor
  ───────────────────────────────────────────────── betaNatZeroProof
  betaNatZeroProof base step : Eq (natRec base step zero) base
  ```
  -/
  lf_opaque betaNatZeroProof (base : Nat) (step : NatRecursor) : Eq (natRec base step zero) base

  /--
  Internal proof-object version of the successor computation rule for `natRec`.

  ```text
  base : Nat    step : NatRecursor    n : Nat
  ───────────────────────────────────────────────────────────────── betaNatSuccProof
  betaNatSuccProof base step n : Eq (natRec base step (succ n))
                                  (recStep step n (natRec base step n))
  ```
  -/
  lf_opaque betaNatSuccProof (base : Nat) (step : NatRecursor) (n : Nat) :
    Eq (natRec base step (succ n)) (recStep step n (natRec base step n))

  /--
  Internal proof-object version of the defining equation for `succStep`.

  ```text
  n : Nat    ih : Nat
  ───────────────────────────────────────────── succStepBetaProof
  succStepBetaProof n ih : Eq (recStep succStep n ih) (succ ih)
  ```
  -/
  lf_opaque succStepBetaProof (n : Nat) (ih : Nat) : Eq (recStep succStep n ih) (succ ih)

  /--
  Zero is wellformed.

  ```text
  ───────────── zero-intro
  wfNat zero
  ```
  -/
  rule zero_intro : wfNat zero
  rule_role zero_intro : introduction

  /--
  Successor preserves wellformedness.

  ```text
  wfNat n
  ───────────────── succ-intro
  wfNat (succ n)
  ```
  -/
  rule succ_intro (n : Nat) where
    premise pred_ok : wfNat n
    conclusion : wfNat (succ n)
  rule_role succ_intro : introduction

  /--
  The distinguished successor step is a wellformed recursor step.

  ```text
  ─────────────────────── succ-step-intro
  wfRecursor succStep
  ```
  -/
  rule succ_step_intro : wfRecursor succStep
  rule_role succ_step_intro : introduction

  /--
  Applying a wellformed recursor step to a predecessor and recursive result is wellformed.

  ```text
  wfRecursor r    wfNat n    wfNat ih
  ───────────────────────────────────── rec-step-intro
  wfNat (recStep r n ih)
  ```
  -/
  rule rec_step_intro (r : NatRecursor) (n : Nat) (ih : Nat) where
    premise step_ok : wfRecursor r
    premise pred_ok : wfNat n
    premise ih_ok : wfNat ih
    conclusion : wfNat (recStep r n ih)
  rule_role rec_step_intro : elimination

  /--
  Natural-number recursion preserves wellformedness.

  ```text
  wfNat base    wfRecursor step    wfNat n
  ───────────────────────────────────────── nat-rec-elim
  wfNat (natRec base step n)
  ```
  -/
  rule nat_rec_elim (base : Nat) (step : NatRecursor) (n : Nat) where
    premise base_ok : wfNat base
    premise step_ok : wfRecursor step
    premise arg_ok : wfNat n
    conclusion : wfNat (natRec base step n)
  rule_role nat_rec_elim : elimination

  /--
  Equality is reflexive on wellformed naturals.

  ```text
  wfNat n
  ───────── eq-refl
  eqNat n n
  ```
  -/
  rule eq_refl (n : Nat) where
    premise n_ok : wfNat n
    conclusion : eqNat n n
  rule_role eq_refl : structural

  /--
  Equality is symmetric.

  ```text
  eqNat lhs rhs
  ───────────── eq-symm
  eqNat rhs lhs
  ```
  -/
  rule eq_symm (lhs : Nat) (rhs : Nat) where
    premise eq_ok : eqNat lhs rhs
    conclusion : eqNat rhs lhs
  rule_role eq_symm : structural

  /--
  Equality is transitive.

  ```text
  eqNat lhs mid    eqNat mid rhs
  ─────────────────────────────── eq-trans
  eqNat lhs rhs
  ```
  -/
  rule eq_trans (lhs : Nat) (mid : Nat) (rhs : Nat) where
    premise left_ok : eqNat lhs mid
    premise right_ok : eqNat mid rhs
    conclusion : eqNat lhs rhs
  rule_role eq_trans : structural

  /--
  The successor recursor step computes by applying `succ` to the recursive result.

  ```text
  wfNat n    wfNat ih
  ───────────────────────────────────────── succ-step-beta
  eqNat (recStep succStep n ih) (succ ih)
  ```
  -/
  rule succ_step_beta (n : Nat) (ih : Nat) where
    premise pred_ok : wfNat n
    premise ih_ok : wfNat ih
    conclusion : eqNat (recStep succStep n ih) (succ ih)
  rule_role succ_step_beta : computation

  /--
  Recursion at zero returns the base case.

  ```text
  wfNat base    wfRecursor step
  ───────────────────────────────────── beta-nat-zero
  eqNat (natRec base step zero) base
  ```
  -/
  rule beta_nat_zero (base : Nat) (step : NatRecursor) where
    premise base_ok : wfNat base
    premise step_ok : wfRecursor step
    conclusion : eqNat (natRec base step zero) base
  rule_role beta_nat_zero : computation

  /--
  Recursion at a successor applies the step to the predecessor and recursive result.

  ```text
  wfNat base    wfRecursor step    wfNat n
  ───────────────────────────────────────────────────────────────── beta-nat-succ
  eqNat (natRec base step (succ n)) (recStep step n (natRec base step n))
  ```
  -/
  rule beta_nat_succ (base : Nat) (step : NatRecursor) (n : Nat) where
    premise base_ok : wfNat base
    premise step_ok : wfRecursor step
    premise pred_ok : wfNat n
    conclusion : eqNat (natRec base step (succ n)) (recStep step n (natRec base step n))
  rule_role beta_nat_succ : computation

namespace TinyNat

/-- Addition is an internal definition from primitive natural recursion. -/
internal def add (lhs : Nat) (rhs : Nat) : Nat := natRec rhs succStep lhs

/-- Doubling is an internal abbreviation. -/
internal def double (n : Nat) : Nat := add n n

/-- Quadrupling is an internal abbreviation. -/
internal def quadruple (n : Nat) : Nat := double (double n)

internal def one : Nat := succ zero
internal def two : Nat := succ one
internal def addZeroZero : Nat := add zero zero
internal def doubleTwo : Nat := double two
internal def zero_wf : wfNat zero := zero_intro

/-- Local-assumption smoke theorem: any locally wellformed TinyNat term remains wellformed. -/
internal def local_wfNat_identity (n : Nat) (h : wfNat n) : wfNat n := h

internal def one_wf : wfNat one := succ_intro zero zero_wf
internal def two_wf : wfNat (succ (succ zero)) :=
  succ_intro (succ zero) (succ_intro zero zero_wf)
internal def add_zero_zero_wf : wfNat (add zero zero) :=
  nat_rec_elim zero succStep zero zero_wf succ_step_intro zero_wf
internal def add_zero_zero_eq : eqNat (add zero zero) zero :=
  beta_nat_zero zero succStep zero_wf succ_step_intro
internal def double_two_wf : wfNat (double (succ (succ zero))) :=
  nat_rec_elim (succ (succ zero)) succStep (succ (succ zero)) two_wf succ_step_intro two_wf

internal def add_zero_left (n : Nat) : Eq (add zero n) n :=
  betaNatZeroProof n succStep

internal def add_zero_right (n : Nat) : Eq (add n zero) n :=
  natIndProof
    (fun n => Eq (add n zero) n)
    (add_zero_left zero)
    (fun n ih =>
      transProof
        (add (succ n) zero)
        (recStep succStep n (add n zero))
        (succ n)
        (betaNatSuccProof zero succStep n)
        (transProof
          (recStep succStep n (add n zero))
          (succ (add n zero))
          (succ n)
          (succStepBetaProof n (add n zero))
          (apSuccProof (add n zero) n ih)))
    n

internal def add_succ_right (m : Nat) (n : Nat) : Eq (add m (succ n)) (succ (add m n)) :=
  natIndProof
    (fun m => Eq (add m (succ n)) (succ (add m n)))
    (transProof
      (add zero (succ n))
      (succ n)
      (succ (add zero n))
      (add_zero_left (succ n))
      (apSuccProof n (add zero n) (symmProof (add zero n) n (add_zero_left n))))
    (fun m ih =>
      transProof
        (add (succ m) (succ n))
        (succ (add m (succ n)))
        (succ (add (succ m) n))
        (transProof
          (add (succ m) (succ n))
          (recStep succStep m (add m (succ n)))
          (succ (add m (succ n)))
          (betaNatSuccProof (succ n) succStep m)
          (succStepBetaProof m (add m (succ n))))
        (transProof
          (succ (add m (succ n)))
          (succ (succ (add m n)))
          (succ (add (succ m) n))
          (apSuccProof (add m (succ n)) (succ (add m n)) ih)
          (symmProof
            (succ (add (succ m) n))
            (succ (succ (add m n)))
            (apSuccProof
              (add (succ m) n)
              (succ (add m n))
              (transProof
                (add (succ m) n)
                (recStep succStep m (add m n))
                (succ (add m n))
                (betaNatSuccProof n succStep m)
                (succStepBetaProof m (add m n)))))))
    m

internal def add_comm (n : Nat) (m : Nat) : Eq (add n m) (add m n) :=
  natIndProof
    (fun n => Eq (add n m) (add m n))
    (transProof
      (add zero m)
      m
      (add m zero)
      (add_zero_left m)
      (symmProof (add m zero) m (add_zero_right m)))
    (fun n ih =>
      transProof
        (add (succ n) m)
        (succ (add n m))
        (add m (succ n))
        (transProof
          (add (succ n) m)
          (recStep succStep n (add n m))
          (succ (add n m))
          (betaNatSuccProof m succStep n)
          (succStepBetaProof n (add n m)))
        (transProof
          (succ (add n m))
          (succ (add m n))
          (add m (succ n))
          (apSuccProof (add n m) (add m n) ih)
          (symmProof (add m (succ n)) (succ (add m n)) (add_succ_right m n))))
    n

internal def one_ok_by_tactic : wfNat (succ zero) := by
  apply succ_intro
  exact zero_wf

internal def add_zero_zero_by_refine : eqNat (add zero zero) zero := by
  exact add_zero_zero_eq

end TinyNat
