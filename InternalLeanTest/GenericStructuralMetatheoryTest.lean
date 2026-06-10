/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Generic structural-metatheory smoke tests

These tests cover the first generic structural-metatheory milestone: checked rule metadata can be
organized into source-name-preserving induction cases without hard-coding any downstream theory.
-/

@[expose] public section

open InternalLean

declare_type_theory GenericInductionSimpleSmoke where
  syntax_sort Obj
  judgment Ok (x : Obj)

  lf_opaque base : Obj
  lf_opaque step (x : Obj) : Obj

  rule base_ok where
    conclusion : Ok base

  rule step_ok (x : Obj) where
    premise prev : Ok x
    conclusion : Ok (step x)

/--
info: rule induction for GenericInductionSimpleSmoke over Ok
cases: 2
recursive premises: 1

case base_ok
  parameters: none
  conclusion: Ok base

case step_ok
  parameters: (x : Obj)
  recursive premise prev : Ok x
  conclusion: Ok (step x)
-/
#guard_msgs (whitespace := lax) in
#print_judgment_induction GenericInductionSimpleSmoke Ok

/--
info: judgment induction metadata for GenericInductionSimpleSmoke.Ok: 2 case(s), 1 recursive
  premise(s)
-/
#guard_msgs (whitespace := lax) in
#check_judgment_induction GenericInductionSimpleSmoke Ok

declare_type_theory GenericInductionMutualSmoke where
  syntax_sort Obj
  judgment Even (x : Obj)
  judgment Odd (x : Obj)

  lf_opaque zero : Obj
  lf_opaque succ (x : Obj) : Obj

  rule even_zero where
    conclusion : Even zero

  rule odd_succ (x : Obj) where
    premise prev : Even x
    conclusion : Odd (succ x)

  rule even_succ (x : Obj) where
    premise prev : Odd x
    conclusion : Even (succ x)

/--
info: rule induction for GenericInductionMutualSmoke over Even, Odd
cases: 3
recursive premises: 2

case even_zero
  parameters: none
  conclusion: Even zero

case odd_succ
  parameters: (x : Obj)
  recursive premise prev : Even x
  conclusion: Odd (succ x)

case even_succ
  parameters: (x : Obj)
  recursive premise prev : Odd x
  conclusion: Even (succ x)
-/
#guard_msgs (whitespace := lax) in
#print_rule_induction GenericInductionMutualSmoke for Even, Odd

/--
info: rule induction metadata for GenericInductionMutualSmoke over Even, Odd: 3 case(s), 2
  recursive premise(s)
-/
#guard_msgs (whitespace := lax) in
#check_rule_induction GenericInductionMutualSmoke for Even, Odd

/--
error: rule-induction metadata for type theory 'GenericInductionSimpleSmoke' is not usable:
unknown judgment 'Missing' in checked type theory 'GenericInductionSimpleSmoke'
-/
#guard_msgs in
#check_judgment_induction GenericInductionSimpleSmoke Missing
