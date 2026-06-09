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
error: Lean mirror translated LF term with type
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
error: Lean mirror translated LF term with type
  LeanMirrorDependentSmoke.LFMirror.Obj
expected
  LeanMirrorDependentSmoke.LFMirror.Fiber LeanMirrorDependentSmoke.LFMirror.o
-/
#guard_msgs (whitespace := lax) in
#check_lf_mirror LeanMirrorDependentSmoke : Σ x : Obj, Fiber x := ⟨o, o⟩

/--
error: Lean mirror translated LF term with type
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

/--
error: Lean mirror translated LF term with type
  LeanMirrorTransparencySmoke.LFMirror.Obj
expected
  LeanMirrorTransparencySmoke.LFMirror.AdmittedAlias
-/
#guard_msgs (whitespace := lax) in
#check_lf_mirror LeanMirrorTransparencySmoke : AdmittedAlias := o

/-- Lean's Sigma eta is accepted by the mirror, so compare mode must report the LF rejection. -/
declare_type_theory LeanMirrorSigmaEtaPitfall where
  syntax_sort Obj : Type
  lf_opaque p : Σ x : Obj, Obj
  judgment GoodPack (q : Σ x : Obj, Obj)
  rule good_p : GoodPack p

#check_lf_mirror LeanMirrorSigmaEtaPitfall : GoodPack ⟨fst p, snd p⟩ := good_p

/--
error: Lean mirror accepted a term in type theory 'LeanMirrorSigmaEtaPitfall',
but the ordinary LF checker rejected it.

Recognized mirror/LF conversion gap: the translated Lean term uses Sigma eta.
The current LF conversion policy does not identify `⟨fst p, snd p⟩` with `p`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.mirrorBackend.compareWithLF true in
#check_lf_mirror LeanMirrorSigmaEtaPitfall : GoodPack ⟨fst p, snd p⟩ := good_p

/-- Function-to-judgment shapes are mirror-checkable Lean types but not LF theorem
statements. -/
declare_type_theory LeanMirrorFunctionEtaPitfall where
  syntax_sort Obj : Type
  judgment GoodFun (g : Obj → Obj)
  rule good (g : Obj → Obj) : GoodFun g

#check_lf_mirror LeanMirrorFunctionEtaPitfall :
    (g : Obj → Obj) → GoodFun (fun x => g x) :=
  fun g => good g

/--
error: Lean mirror accepted a term in type theory 'LeanMirrorFunctionEtaPitfall',
but the ordinary LF checker rejected it.

Recognized mirror/LF conversion gap: the translated Lean term uses function eta.
The current LF conversion policy does not identify `fun x => f x` with `f`.
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.mirrorBackend.compareWithLF true in
#check_lf_mirror LeanMirrorFunctionEtaPitfall :
    (g : Obj → Obj) → GoodFun (fun x => g x) :=
  fun g => good g

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
