/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Encoding object-language universe hierarchies

This example keeps object-language levels as ordinary LF syntax.  The generated Lean universes
still come only from the explicit framework-level annotations such as `Type u` and `Type (u+1)`.

The pattern is extrinsic: `lift` is an unguarded type former, while well-formedness and
cumulativity evidence live in the `IsTy` and `Le` judgments.
-/

@[expose] public section

open InternalLean

/-- A reusable object-language universe hierarchy prelude. -/
declare_type_theory UniverseHierarchy{u} where
  /-- Object-language universe levels. -/
  syntax_sort Level : Type u
  /-- Object-language type codes at a level. -/
  syntax_sort Ty (i : Level) : Type (u+1)
  /-- Elements of a type code. -/
  syntax_sort Tm {i : Level} (A : Ty i) : Type u

  lf_opaque zero : Level
  lf_opaque succ (i : Level) : Level
  lf_opaque lmax (i : Level) (j : Level) : Level

  judgment Le (i : Level) (j : Level)
  rule le_refl (i : Level) : Le i i
  rule le_succ (i : Level) : Le i (succ i)

  /-- Unguarded lift; well-formedness is judgmental (extrinsic style). -/
  lf_opaque lift {i : Level} {j : Level} (A : Ty i) : Ty j
  judgment IsTy {i : Level} (A : Ty i)
  rule lift_wf {i : Level} {j : Level} (A : Ty i) where
    premise le : Le i j
    premise wf : IsTy (i := i) A
    conclusion : IsTy (i := j) (lift (i := i) (j := j) A)

  lf_opaque Univ (i : Level) : Ty (succ i)
  rule univ_wf (i : Level) : IsTy (i := succ i) (Univ i)

  judgment_theorem univ_zero_wf : IsTy (i := succ zero) (Univ zero) := univ_wf zero

-- Type-code notation for the hierarchy's object-level universes.
object_notation UniverseHierarchy "𝒰[" i "]" => Ty i

-- Element notation for a hierarchy type code.
object_notation UniverseHierarchy "El[" A "]" => Tm A

-- Object-level maximum notation; this expands to the `lmax` constant.
object_notation UniverseHierarchy "Level.max[" i "," j "]" => lmax i j

namespace UniverseHierarchy

/-- Native tactic mode proves an object-level cumulativity fact through LF replay. -/
internal theorem zero_le_succ_zero : Le zero (succ zero) := by
  apply le_succ

/-- Quoted hierarchy-shaped body using an implicit-level `lift`/`Univ` application. -/
internal def liftedZeroUniv : Ty (succ (succ zero)) :=
  lift (i := succ zero) (j := succ (succ zero)) (Univ zero)

/-- Native tactics can use the extrinsic well-formedness rule for `lift`. -/
internal theorem liftedZeroUniv_wf : IsTy (i := succ (succ zero)) liftedZeroUniv := by
  apply lift_wf
  · apply le_succ
  · apply univ_wf

end UniverseHierarchy

#check_theory UniverseHierarchy

generate_model_interface UniverseHierarchy as Model
generate_syntactic_model_instance UniverseHierarchy as syntacticModel for Model

namespace UniverseHierarchy

/--
A tiny filled model template.  It interprets object levels as `Nat`, type codes as Lean types,
and all well-formedness evidence as `PUnit`.  This does not make object levels control Lean
universes; this model lives at the framework universe parameter `0`.
-/
def natModel : Model.{0} where
  Level := Nat
  Ty := fun _ => Type
  Tm := fun {_} A => A
  zero := 0
  succ := Nat.succ
  lmax := Nat.max
  lift := fun {_} {_} A => A
  Univ := fun _ => PUnit
  Le := fun i j => PLift (i ≤ j)
  IsTy := fun {_} _ => PUnit
  le_refl := fun i => ⟨Nat.le_refl i⟩
  le_succ := fun i => ⟨Nat.le_succ i⟩
  lift_wf := fun _ _ _ => PUnit.unit
  univ_wf := fun _ => PUnit.unit

#check syntacticModel
#check natModel
#check (natModel.Ty : Nat → Type 1)
#check (natModel.Tm (i := natModel.zero) PUnit : Type)
#check zero_le_succ_zero
#check liftedZeroUniv_wf

end UniverseHierarchy

/-- Ordinary type formers can be layered on top of the prelude vocabulary. -/
extend_type_theory UniverseHierarchy where
  lf_opaque Pi {i : Level} {j : Level} (A : Ty i) (B : Tm (i := i) A → Ty j) :
    Ty (lmax i j)
  lf_opaque Sigma {i : Level} {j : Level} (A : Ty i) (B : Tm (i := i) A → Ty j) :
    Ty (lmax i j)
  lf_opaque UnitTy {i : Level} : Ty i

  rule pi_wf {i : Level} {j : Level} (A : Ty i) (B : Tm (i := i) A → Ty j) where
    premise wfA : IsTy (i := i) A
    premise wfB : (x : Tm (i := i) A) → IsTy (i := j) (B x)
    conclusion : IsTy (i := lmax i j) (Pi (i := i) (j := j) A B)

  rule sigma_wf {i : Level} {j : Level} (A : Ty i) (B : Tm (i := i) A → Ty j) where
    premise wfA : IsTy (i := i) A
    premise wfB : (x : Tm (i := i) A) → IsTy (i := j) (B x)
    conclusion : IsTy (i := lmax i j) (Sigma (i := i) (j := j) A B)

  rule unit_wf {i : Level} : IsTy (i := i) (UnitTy (i := i))

namespace UniverseHierarchy

/-- A quoted higher-order former body over the extension. -/
internal def unitToUnitPi : Ty (lmax zero zero) :=
  Pi (i := zero) (j := zero) (UnitTy (i := zero)) fun _ => UnitTy (i := zero)

#check unitToUnitPi
#check LFQuote.Pi
#check LFQuote.Sigma
#check LFQuote.UnitTy

end UniverseHierarchy
