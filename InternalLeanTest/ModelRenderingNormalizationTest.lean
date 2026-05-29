/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Model-rendering normalization tests

These regressions cover LF-level projection reduction before generated Lean model code is emitted.
-/

@[expose] public section

open InternalLean

declare_type_theory ProjectionFromPackageTest where
  syntax_sort A : Type
  syntax_sort Fam (a : A) : Type
  syntax_sort Marker (a : A) (x : Fam a) : Type
  lf_opaque base : A
  lf_opaque fiber (a : A) : Fam a
  syntax_abbrev Pack := Σ a : A, Fam a
  syntax_abbrev NestedPack := Σ a : A, Σ x : Fam a, Fam a
  lf_def package : Pack := ⟨base, fiber base⟩
  lf_def packageBase : A := fst package
  lf_def packageFiber : Fam packageBase := snd package
  lf_def nested : NestedPack := ⟨base, ⟨fiber base, fiber base⟩⟩
  lf_def nestedFirst : A := fst nested
  lf_def nestedSecond : Fam nestedFirst := fst (snd nested)
  lf_def mkPack : (x : A) ⇒ Pack := fun x => ⟨x, fiber x⟩
  lf_def projected : Fam base := snd (mkPack base)
  lf_def projectedLocalLambda : Fam base := snd ((fun x => ⟨x, fiber x⟩) base)
  lf_opaque usesProjection : Fam packageBase
  lf_opaque usesNestedSecond : Marker nestedFirst nestedSecond
  lf_opaque usesProjected : Marker base projected
  lf_opaque usesLocalLambda : Marker base projectedLocalLambda
  lf_opaque shadow : (package : Pack) → Fam (fst package)

generate_model_interface ProjectionFromPackageTest as ProjectionFromPackageModel
generate_model_transports ProjectionFromPackageTest for ProjectionFromPackageModel

#check ProjectionFromPackageTest.ProjectionFromPackageModel.package
#check ProjectionFromPackageTest.ProjectionFromPackageModel.packageBase
#check ProjectionFromPackageTest.ProjectionFromPackageModel.packageFiber
#check ProjectionFromPackageTest.ProjectionFromPackageModel.nestedSecond
#check ProjectionFromPackageTest.ProjectionFromPackageModel.projected
#check ProjectionFromPackageTest.ProjectionFromPackageModel.projectedLocalLambda
#check ProjectionFromPackageTest.ProjectionFromPackageModel.shadow

def projectionFromPackageModel : ProjectionFromPackageTest.ProjectionFromPackageModel where
  A := Nat
  Fam := fun n => Fin (n + 1)
  Marker := fun _ _ => Unit
  base := 0
  fiber := fun n => ⟨0, Nat.zero_lt_succ n⟩
  usesProjection := ⟨0, Nat.zero_lt_succ 0⟩
  usesNestedSecond := ()
  usesProjected := ()
  usesLocalLambda := ()
  shadow := fun package => package.2
