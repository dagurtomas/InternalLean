/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLeanTest.TinyNat

/-!
# Syntactic model instance tests

These checks exercise the mirror-backed syntactic model instance generator.  The generated
instances elaborate only if the model-interface obligations are coherent with the Lean mirror
translation.
-/

@[expose] public section

open InternalLean

generate_model_interface TinyNat as TinyNatSyntacticModel
generate_syntactic_model_instance TinyNat as tinyNatSyntactic for TinyNatSyntacticModel

#check TinyNat.tinyNatSyntactic
#check TinyNat.tinyNatSyntactic.Nat
#check TinyNat.tinyNatSyntactic.zero_intro

example : TinyNat.tinyNatSyntactic.zero = TinyNat.LFMirror.zero := rfl

declare_type_theory SyntacticModelRichSmoke{u} where
  side_condition_solver trivial_side_condition
  syntax_sort Obj : Type u
  syntax_sort Fam (x : Obj) : Type u
  judgment Good {x : Obj} (y : Fam x)
  lf_opaque o : Obj
  lf_opaque witness : Fam o
  lf_opaque check / 1
  rule good_witness where
    side_condition ok by trivial_side_condition : check witness
    conclusion : Good (x := o) witness

namespace SyntacticModelRichSmoke

#guard_msgs (drop warning) in
internal def admittedFam : Fam o := sorry

end SyntacticModelRichSmoke

extend_type_theory SyntacticModelRichSmoke where
  rule good_admitted where
    conclusion : Good (x := o) admittedFam

#guard_msgs (drop warning) in
generate_model_interface SyntacticModelRichSmoke as SyntacticModelRichModel
generate_syntactic_model_instance SyntacticModelRichSmoke as syntacticRich for
  SyntacticModelRichModel

universe u
#check SyntacticModelRichSmoke.syntacticRich.{u}
#check (SyntacticModelRichSmoke.syntacticRich.{u}.Obj : Type u)
#check (SyntacticModelRichSmoke.syntacticRich.{u}.admittedFam :
  SyntacticModelRichSmoke.LFMirror.Fam SyntacticModelRichSmoke.LFMirror.o)
#check SyntacticModelRichSmoke.LFMirror.admittedFam

/--
info: axiom SyntacticModelRichSmoke.LFMirror.admittedFam.{u} : Fam o
-/
#guard_msgs in
#print SyntacticModelRichSmoke.LFMirror.admittedFam

example : SyntacticModelRichSmoke.syntacticRich.{u}.admittedFam =
    SyntacticModelRichSmoke.LFMirror.admittedFam := rfl

declare_type_theory SyntacticModelParamEvidenceSmoke where
  syntax_sort Obj
  judgment Good (x : Obj)
  lf_opaque o : Obj
  rule intro (x : Obj) where
    evidence hx for x : Good x
    conclusion : Good x

generate_model_interface SyntacticModelParamEvidenceSmoke as SyntacticModelParamEvidenceModel
generate_syntactic_model_instance SyntacticModelParamEvidenceSmoke as syntacticParamEvidence for
  SyntacticModelParamEvidenceModel

#check SyntacticModelParamEvidenceSmoke.syntacticParamEvidence.intro

namespace SyntacticModelRichSmoke

structure IncompleteModel where
  Obj : Type u

end SyntacticModelRichSmoke

/--
error: `Fam` is not a field of structure `IncompleteModel`
---
error: `o` is not a field of structure `IncompleteModel`
---
error: `witness` is not a field of structure `IncompleteModel`
---
error: `admittedFam` is not a field of structure `IncompleteModel`
---
error: `Good` is not a field of structure `IncompleteModel`
---
error: `good_witness` is not a field of structure `IncompleteModel`
---
error: `good_admitted` is not a field of structure `IncompleteModel`
-/
#guard_msgs in
generate_syntactic_model_instance SyntacticModelRichSmoke as incompleteSyntactic for
  IncompleteModel
