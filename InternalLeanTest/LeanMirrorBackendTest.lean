/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Experimental Lean mirror checker backend tests

The mirror backend is a prototype checker path: it translates LF expressions to hidden Lean mirror
constants and asks Lean's kernel to check the translated expression.  Registered declarations still
run through the ordinary LF checker after the mirror accepts them.
-/

@[expose] public section

open InternalLean

declare_type_theory LeanMirrorSigmaSmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  lf_opaque id (x : Obj) : Obj

#check_lf_mirror LeanMirrorSigmaSmoke : Obj := o
#check_lf_mirror LeanMirrorSigmaSmoke : Obj := id o
#check_lf_mirror LeanMirrorSigmaSmoke : Obj → Obj := fun x => x
#check_lf_mirror LeanMirrorSigmaSmoke : Σ x : Obj, Obj := ⟨o, o⟩
#check_lf_mirror LeanMirrorSigmaSmoke : Obj := fst ⟨o, o⟩
#check_lf_mirror LeanMirrorSigmaSmoke : Obj := snd ⟨o, o⟩

namespace LeanMirrorSigmaSmoke

internal_mirror def package : Σ x : Obj, Obj := ⟨o, o⟩
internal_mirror def packageFst : Obj := fst package
internal_mirror def packageSnd : Obj := snd package

#check package
#check packageFst
#check packageSnd

end LeanMirrorSigmaSmoke

/--
error: Lean mirror backend rejected term in type theory 'LeanMirrorSigmaSmoke'.

Internal type:
  Σ x : Obj, Obj

Internal value:
  o

Reason:
Lean mirror translated LF term with type
  LeanMirrorSigmaSmoke.LFMirror.Obj
expected
  (_ : LeanMirrorSigmaSmoke.LFMirror.Obj) × LeanMirrorSigmaSmoke.LFMirror.Obj
-/
#guard_msgs (whitespace := lax) in
#check_lf_mirror LeanMirrorSigmaSmoke : Σ x : Obj, Obj := o

/-- Dependent rule and opaque types should mirror telescope locals, not global constants. -/
declare_type_theory LeanMirrorDependentSmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  syntax_sort Fiber (x : Obj) : Type
  judgment Good (x : Obj)
  rule o_good : Good o
  rule keep_good (x : Obj) where
    premise h : Good x
    conclusion : Good x
  lf_opaque witness (x : Obj) : Fiber x
  lf_opaque usePack (p : Σ x : Obj, Fiber x) : Obj

#check_lf_mirror LeanMirrorDependentSmoke : Good o := o_good
#compare_lf_mirror LeanMirrorDependentSmoke : Good o := keep_good o o_good
#check_lf_mirror LeanMirrorDependentSmoke : Fiber o := witness o
#compare_lf_mirror LeanMirrorDependentSmoke : Obj := usePack ⟨o, witness o⟩
#check (LeanMirrorDependentSmoke.LFMirror.Good :
  LeanMirrorDependentSmoke.LFMirror.Obj → Type)

/--
error: Lean mirror backend rejected term in type theory 'LeanMirrorDependentSmoke'.

Internal type:
  Σ x : Obj, Fiber x

Internal value:
  ⟨o, o⟩

Reason:
Lean mirror translated LF term with type
  LeanMirrorDependentSmoke.LFMirror.Obj
expected
  LeanMirrorDependentSmoke.LFMirror.Fiber LeanMirrorDependentSmoke.LFMirror.o
-/
#guard_msgs (whitespace := lax) in
#check_lf_mirror LeanMirrorDependentSmoke : Σ x : Obj, Fiber x := ⟨o, o⟩

/--
error: Lean mirror backend rejected term in type theory 'LeanMirrorDependentSmoke'.

Internal type:
  Obj

Internal value:
  usePack (⟨o, o⟩)

Reason:
Lean mirror translated LF term with type
  LeanMirrorDependentSmoke.LFMirror.Obj
expected
  LeanMirrorDependentSmoke.LFMirror.Fiber LeanMirrorDependentSmoke.LFMirror.o
-/
#guard_msgs (whitespace := lax) in
#check_lf_mirror LeanMirrorDependentSmoke : Obj := usePack ⟨o, o⟩

/-- Syntax and judgment abbreviations mirror as transparent definitions. -/
declare_type_theory LeanMirrorAbbrevSmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  syntax_sort Fiber (x : Obj) : Type
  lf_opaque witness (x : Obj) : Fiber x
  syntax_abbrev ObjAlias := Obj
  syntax_abbrev FiberAlias (x : Obj) := Fiber x
  judgment Good (x : Obj)
  judgment_abbrev GoodAlias (x : Obj) := Good x
  rule good_o : Good o

#check_lf_mirror LeanMirrorAbbrevSmoke : ObjAlias := o
#check_lf_mirror LeanMirrorAbbrevSmoke : FiberAlias o := witness o
#compare_lf_mirror LeanMirrorAbbrevSmoke : GoodAlias o := good_o
#check (LeanMirrorAbbrevSmoke.LFMirror.ObjAlias : Type)
#check (LeanMirrorAbbrevSmoke.LFMirror.FiberAlias :
  LeanMirrorAbbrevSmoke.LFMirror.Obj → Type)
#check (LeanMirrorAbbrevSmoke.LFMirror.GoodAlias :
  LeanMirrorAbbrevSmoke.LFMirror.Obj → Type)
#compare_lf_mirror_theory LeanMirrorAbbrevSmoke

/-- Mirror declaration construction respects dependencies across declaration classes. -/
declare_type_theory LeanMirrorCrossClassDependencySmoke where
  syntax_sort Obj : Type
  syntax_sort Family (x : Obj) : Type
  lf_opaque o : Obj
  lf_opaque f (x : Obj) : Obj
  syntax_abbrev FamilyAtFO := Family (f o)
  syntax_def FamilyAtFOChecked : Type := Family (f o)
  lf_opaque witness : FamilyAtFO
  lf_def witnessAlias : FamilyAtFOChecked := witness

#compare_lf_mirror_theory LeanMirrorCrossClassDependencySmoke

/- Theory-body declarations can be checked through the opt-in mirror fast path. -/
set_option internalLean.mirrorBackend.checkTheoryBodies true

declare_type_theory LeanMirrorTheoryBodyFastSmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  syntax_def ObjAlias : Type := Obj
  lf_def objectAlias : ObjAlias := o

set_option internalLean.mirrorBackend.checkTheoryBodies false

#compare_lf_mirror_theory LeanMirrorTheoryBodyFastSmoke

/- The theory-body mirror path can also run the ordinary LF checker in compare mode. -/
set_option internalLean.mirrorBackend.checkTheoryBodies true
set_option internalLean.mirrorBackend.compareTheoryBodiesWithLF true

declare_type_theory LeanMirrorTheoryBodyCompareSmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  lf_def objectAlias : Obj := o

set_option internalLean.mirrorBackend.checkTheoryBodies false
set_option internalLean.mirrorBackend.compareTheoryBodiesWithLF false

#compare_lf_mirror_theory LeanMirrorTheoryBodyCompareSmoke

/-- Universe-polymorphic syntax sorts mirror with Lean universe parameters. -/
declare_type_theory LeanMirrorUniverseSmoke{u, v} where
  syntax_sort Obj : Type u
  lf_opaque o : Obj
  syntax_sort Code (A : Type u) : Type v
  lf_opaque codeObj : Code Obj
  syntax_sort Fiber (x : Obj) : Type v
  lf_opaque witness : Fiber o

#check_lf_mirror LeanMirrorUniverseSmoke : Type u := Obj
#check_lf_mirror LeanMirrorUniverseSmoke : Code Obj := codeObj
#check_lf_mirror LeanMirrorUniverseSmoke : Σ x : Obj, Fiber x := ⟨o, witness⟩
#check_lf_mirror LeanMirrorUniverseSmoke : Obj := fst ⟨o, witness⟩
#check_lf_mirror LeanMirrorUniverseSmoke : Fiber o := snd ⟨o, witness⟩

universe u v
#check (LeanMirrorUniverseSmoke.LFMirror.Obj.{u, v} : Type u)
#check (LeanMirrorUniverseSmoke.LFMirror.Code.{u, v} : Type u → Type v)

/--
error: Lean mirror backend rejected term in type theory 'LeanMirrorUniverseSmoke'.

Internal type:
  Type

Internal value:
  Obj

Reason:
Lean mirror translated LF term with type
  Type u
expected
  Type
-/
#guard_msgs (whitespace := lax) in
#check_lf_mirror LeanMirrorUniverseSmoke : Type := Obj

/-- Checked definitions are transparent to the mirror; admissions remain opaque. -/
declare_type_theory LeanMirrorTransparencySmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  syntax_def ObjAlias : Type := Obj
  syntax_def AdmittedAlias : Type := sorry
  lf_def objectAlias : Obj := o
  judgment Good (x : Obj)
  rule good_o : Good o

#check_lf_mirror LeanMirrorTransparencySmoke : ObjAlias := o
#check_lf_mirror LeanMirrorTransparencySmoke : Good objectAlias := good_o
#compare_lf_mirror_theory LeanMirrorTransparencySmoke

/--
error: Lean mirror backend rejected term in type theory 'LeanMirrorTransparencySmoke'.

Internal type:
  AdmittedAlias

Internal value:
  o

Reason:
Lean mirror translated LF term with type
  LeanMirrorTransparencySmoke.LFMirror.Obj
expected
  LeanMirrorTransparencySmoke.LFMirror.AdmittedAlias
-/
#guard_msgs (whitespace := lax) in
#check_lf_mirror LeanMirrorTransparencySmoke : AdmittedAlias := o

/-- Structural Sigma eta is part of LF conversion, matching the Lean mirror. -/
declare_type_theory LeanMirrorSigmaEtaPitfall where
  syntax_sort Obj : Type
  lf_opaque p : Σ x : Obj, Obj
  judgment GoodPack (q : Σ x : Obj, Obj)
  rule good_p : GoodPack p

#check_lf_mirror LeanMirrorSigmaEtaPitfall : GoodPack ⟨fst p, snd p⟩ := good_p
#compare_lf_mirror LeanMirrorSigmaEtaPitfall : GoodPack ⟨fst p, snd p⟩ := good_p

/-- Structural function eta is part of LF conversion, matching the Lean mirror. -/
declare_type_theory LeanMirrorFunctionEtaPitfall where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  lf_opaque f : Obj → Obj
  judgment GoodFun (g : Obj → Obj)
  rule good_f : GoodFun f
  rule good (g : Obj → Obj) : GoodFun g

#compare_lf_mirror LeanMirrorFunctionEtaPitfall : Obj := f o
#compare_lf_mirror LeanMirrorFunctionEtaPitfall : GoodFun (fun x => f x) := good_f
#compare_lf_mirror LeanMirrorFunctionEtaPitfall :
    (g : Obj → Obj) → GoodFun (fun x => g x) :=
  fun g => good g

namespace LeanMirrorFunctionEtaPitfall

internal_mirror def etaTheorem (g : Obj → Obj) : GoodFun (fun x => g x) := good g

#check etaTheorem

end LeanMirrorFunctionEtaPitfall

/-- Binder-style declarations mirror-check under local LF parameters, then use ordinary LF
registration. -/
declare_type_theory LeanMirrorBinderSmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  judgment Good (x : Obj)
  rule good_o : Good o

namespace LeanMirrorBinderSmoke

internal_mirror def idObj (x : Obj) : Obj := x
internal_mirror def theoremStyle (x : Obj) (h : Good x) : Good x := h

#check idObj
#check theoremStyle

end LeanMirrorBinderSmoke
