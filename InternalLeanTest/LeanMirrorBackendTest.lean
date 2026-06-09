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
error: Lean mirror checker inferred
  LeanMirrorSigmaSmoke.LFMirror.Obj
for translated value, expected
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

#check_lf_mirror LeanMirrorDependentSmoke : Good o := o_good
#check_lf_mirror LeanMirrorDependentSmoke : Good o := keep_good o o_good
#check_lf_mirror LeanMirrorDependentSmoke : Fiber o := witness o
