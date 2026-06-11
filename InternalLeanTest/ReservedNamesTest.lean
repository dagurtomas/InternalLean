/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Surface-reserved LF names

After the structural-kernel cutover, former raw-kernel constructor names such as `lam`, `_app`,
`pair`, `fst`, `snd`, `arrow`, `sigma`, and `jeq` are ordinary LF heads. Only `Type` remains
reserved by the shared LF declaration validator.
-/

@[expose] public section

open InternalLean

namespace PlainLeanFstSndTokenSmoke

def fst : Nat := 0

def snd : Nat := 1

#check fst
#check snd

end PlainLeanFstSndTokenSmoke

/--
error: LF opaque constant declaration 'Type' uses reserved name 'Type', which is reserved by
InternalLean syntax. Reserved LF names: Type
-/
#guard_msgs (whitespace := lax) in
declare_type_theory ReservedTypeSmoke where
  syntax_sort Obj
  lf_opaque o : Obj
  lf_opaque «Type» (x : Obj) : Obj

/-- Former raw-kernel and projection names are now ordinary LF heads. -/
declare_type_theory FormerReservedPositiveSmoke where
  syntax_sort Obj
  lf_opaque o : Obj
  lf_opaque lam (x : Obj) (y : Obj) : Obj
  lf_opaque _app (x : Obj) (y : Obj) : Obj
  lf_opaque pair (x : Obj) (y : Obj) : Obj
  lf_opaque fst (x : Obj) (y : Obj) : Obj
  lf_opaque snd (x : Obj) (y : Obj) : Obj
  lf_opaque arrow (x : Obj) (y : Obj) : Obj
  lf_opaque sigma (x : Obj) (y : Obj) : Obj
  lf_opaque jeq (x : Obj) (y : Obj) : Obj
  judgment Good (x : Obj)
  rule good_lam (x : Obj) (y : Obj) : Good (lam x y)
  rule good_app (x : Obj) (y : Obj) : Good (_app x y)
  rule good_pair (x : Obj) (y : Obj) : Good (pair x y)
  rule good_fst (x : Obj) (y : Obj) : Good (fst x y)
  rule good_snd (x : Obj) (y : Obj) : Good (snd x y)
  rule good_arrow (x : Obj) (y : Obj) : Good (arrow x y)
  rule good_sigma (x : Obj) (y : Obj) : Good (sigma x y)
  rule good_jeq (x : Obj) (y : Obj) : Good (jeq x y)
  judgment_theorem lam_good : Good (lam o o) := good_lam o o
  judgment_theorem app_good : Good (_app o o) := good_app o o
  judgment_theorem pair_good : Good (pair o o) := good_pair o o
  judgment_theorem fst_good : Good (fst o o) := good_fst o o
  judgment_theorem snd_good : Good (snd o o) := good_snd o o
  judgment_theorem arrow_good : Good (arrow o o) := good_arrow o o
  judgment_theorem sigma_good : Good (sigma o o) := good_sigma o o
  judgment_theorem jeq_good : Good (jeq o o) := good_jeq o o

namespace FormerReservedPositiveSmoke

internal def use_lam : Obj := lam o o
internal def use_app : Obj := _app o o
internal def use_pair : Obj := pair (arrow o o) (sigma o o)
internal def use_fst : Obj := fst o o
internal def use_snd : Obj := snd o o
internal theorem lam_good_again : Good (lam o o) := good_lam o o
internal theorem pair_good_again : Good (pair o o) := good_pair o o
internal theorem fst_good_again : Good (fst o o) := good_fst o o
internal theorem snd_good_again : Good (snd o o) := good_snd o o

end FormerReservedPositiveSmoke

generate_model_interface FormerReservedPositiveSmoke as FormerReservedPositiveModel

#check FormerReservedPositiveSmoke.FormerReservedPositiveModel.lam
#check FormerReservedPositiveSmoke.FormerReservedPositiveModel.fst
#check FormerReservedPositiveSmoke.FormerReservedPositiveModel.snd
#check FormerReservedPositiveSmoke.FormerReservedPositiveModel.good_pair
#check FormerReservedPositiveSmoke.FormerReservedPositiveModel.good_fst
#check FormerReservedPositiveSmoke.FormerReservedPositiveModel.good_snd

declare_type_theory ReservedExtensionBase where
  syntax_sort Obj
  lf_opaque o : Obj
  judgment Good (x : Obj)

extend_type_theory ReservedExtensionBase where
  rule snd : Good o

namespace ReservedExtensionBase

internal def fst : Obj := o

end ReservedExtensionBase

declare_type_theory ReservedPositiveSmoke where
  syntax_sort Fun
  lf_opaque app : Fun
  lf_opaque compose (f : Fun) (g : Fun) : Fun
  judgment Good (f : Fun)
  rule good_app : Good app

namespace ReservedPositiveSmoke

internal def compose_app : Fun := compose app app
internal theorem app_good : Good app := good_app

end ReservedPositiveSmoke

run_cmd do
  let stmt : Judgment := .custom `Good []
  let ctx := ({} : KernelLFCheckContext).addAssumption `h stmt
  let badConstantSig : Signature := {
    name := `KernelReservedConstantSmoke
    constants := [{
      name := `Type
      resultType := .tyConst `Obj }] }
  match CheckedKernelLFDerivation.ofReplay badConstantSig ctx stmt (.assumption `h stmt) with
  | .ok _ => throwError "reserved kernel constant was accepted by replay wrapper"
  | .error err =>
      unless err.contains "kernel LF constant declaration 'Type' uses reserved name 'Type'" do
        throwError "unexpected reserved-constant error: {err}"
  let badRuleSig : Signature := {
    name := `KernelReservedRuleSmoke
    rules := [{
      name := `Type
      «conclusion» := stmt }] }
  match CheckedKernelLFDerivation.ofReplay badRuleSig ctx stmt (.assumption `h stmt) with
  | .ok _ => throwError "reserved kernel rule was accepted by replay wrapper"
  | .error err =>
      unless err.contains "kernel LF rule declaration 'Type' uses reserved name 'Type'" do
        throwError "unexpected reserved-rule error: {err}"
  let conversionStmt : ConversionStatement := {
    plugin := `p
    lhs := .tyConst `A
    rhs := .tyConst `A }
  match CheckedKernelLFConversionCertificate.check badConstantSig {} conversionStmt
      (.refl conversionStmt) with
  | .ok _ => throwError "reserved kernel constant was accepted by conversion wrapper"
  | .error err =>
      unless err.contains "kernel LF constant declaration 'Type' uses reserved name 'Type'" do
        throwError "unexpected reserved-conversion error: {err}"
