/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Reserved LF names

After the structural-kernel cutover, most former raw-kernel constructor names such as `_app`,
`pair`, `arrow`, `sigma`, and `jeq` are ordinary LF heads. `lam` remains reserved while legacy raw
replay still gates acceptance, and `fst`/`snd`/`Type` remain reserved as surface syntax.
-/

@[expose] public section

open InternalLean

/--
error: LF opaque constant declaration 'fst' uses reserved name 'fst', which is reserved by
InternalLean syntax or legacy replay compatibility. Reserved LF names: fst, snd, Type, lam
-/
#guard_msgs (whitespace := lax) in
declare_type_theory ReservedFstSmoke where
  syntax_sort Obj
  lf_opaque o : Obj
  lf_opaque «fst» (x : Obj) : Obj

/--
error: LF opaque constant declaration 'Type' uses reserved name 'Type', which is reserved by
InternalLean syntax or legacy replay compatibility. Reserved LF names: fst, snd, Type, lam
-/
#guard_msgs (whitespace := lax) in
declare_type_theory ReservedTypeSmoke where
  syntax_sort Obj
  lf_opaque o : Obj
  lf_opaque «Type» (x : Obj) : Obj

/- `lam` stays reserved while legacy raw replay still gates acceptance. -/
/--
error: LF opaque constant declaration 'lam' uses reserved name 'lam', which is reserved by
InternalLean syntax or legacy replay compatibility. Reserved LF names: fst, snd, Type, lam
-/
#guard_msgs (whitespace := lax) in
declare_type_theory ReservedLamSmoke where
  syntax_sort Obj
  lf_opaque o : Obj
  lf_opaque lam (x : Obj) (y : Obj) : Obj

/-- Most former raw-kernel constructor names are now ordinary LF heads. -/
declare_type_theory FormerReservedPositiveSmoke where
  syntax_sort Obj
  lf_opaque o : Obj
  lf_opaque _app (x : Obj) (y : Obj) : Obj
  lf_opaque pair (x : Obj) (y : Obj) : Obj
  lf_opaque arrow (x : Obj) (y : Obj) : Obj
  lf_opaque sigma (x : Obj) (y : Obj) : Obj
  lf_opaque jeq (x : Obj) (y : Obj) : Obj
  judgment Good (x : Obj)
  rule good_app (x : Obj) (y : Obj) : Good (_app x y)
  rule good_pair (x : Obj) (y : Obj) : Good (pair x y)
  rule good_arrow (x : Obj) (y : Obj) : Good (arrow x y)
  rule good_sigma (x : Obj) (y : Obj) : Good (sigma x y)
  rule good_jeq (x : Obj) (y : Obj) : Good (jeq x y)
  judgment_theorem app_good : Good (_app o o) := good_app o o
  judgment_theorem pair_good : Good (pair o o) := good_pair o o
  judgment_theorem arrow_good : Good (arrow o o) := good_arrow o o
  judgment_theorem sigma_good : Good (sigma o o) := good_sigma o o
  judgment_theorem jeq_good : Good (jeq o o) := good_jeq o o

namespace FormerReservedPositiveSmoke

internal def use_app : Obj := _app o o
internal def use_pair : Obj := pair (arrow o o) (sigma o o)
internal theorem pair_good_again : Good (pair o o) := good_pair o o

end FormerReservedPositiveSmoke

generate_model_interface FormerReservedPositiveSmoke as FormerReservedPositiveModel

#check FormerReservedPositiveSmoke.FormerReservedPositiveModel.pair
#check FormerReservedPositiveSmoke.FormerReservedPositiveModel.good_pair

declare_type_theory ReservedExtensionBase where
  syntax_sort Obj
  lf_opaque o : Obj
  judgment Good (x : Obj)

/--
error: rule declaration 'snd' uses reserved name 'snd', which is reserved by InternalLean syntax
or legacy replay compatibility. Reserved LF names: fst, snd, Type, lam
-/
#guard_msgs (whitespace := lax) in
extend_type_theory ReservedExtensionBase where
  rule «snd» : Good o

namespace ReservedExtensionBase

/--
error: internal declaration 'fst' uses reserved name 'fst', which is reserved by InternalLean
syntax or legacy replay compatibility. Reserved LF names: fst, snd, Type, lam
-/
#guard_msgs (whitespace := lax) in
internal def «fst» : Obj := o

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
      name := `fst
      «conclusion» := stmt }] }
  match CheckedKernelLFDerivation.ofReplay badRuleSig ctx stmt (.assumption `h stmt) with
  | .ok _ => throwError "reserved kernel rule was accepted by replay wrapper"
  | .error err =>
      unless err.contains "kernel LF rule declaration 'fst' uses reserved name 'fst'" do
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
