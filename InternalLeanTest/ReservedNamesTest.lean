/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Kernel-reserved LF names

These regressions keep the current raw-kernel structural encodings from being shadowed by user
LF head declarations.
-/

@[expose] public section

open InternalLean

/--
error: LF opaque constant declaration 'pair' uses reserved name 'pair', which is reserved by the
kernel encoding. Reserved kernel names: lam, _app, pair, fst, snd, arrow, sigma, Type, jeq,
__implicitArg
-/
#guard_msgs (whitespace := lax) in
declare_type_theory ReservedPairSmoke where
  syntax_sort Obj
  lf_opaque o : Obj
  lf_opaque pair (x : Obj) (y : Obj) : Obj

/--
error: LF opaque constant declaration 'lam' uses reserved name 'lam', which is reserved by the
kernel encoding. Reserved kernel names: lam, _app, pair, fst, snd, arrow, sigma, Type, jeq,
__implicitArg
-/
#guard_msgs (whitespace := lax) in
declare_type_theory ReservedLamSmoke where
  syntax_sort Obj
  lf_opaque o : Obj
  lf_opaque lam (x : Obj) (y : Obj) : Obj
  judgment Good (z : Obj)
  rule mk_good (x : Obj) (y : Obj) : Good (lam x y)

declare_type_theory ReservedExtensionBase where
  syntax_sort Obj
  lf_opaque o : Obj
  judgment Good (x : Obj)

/--
error: rule declaration 'jeq' uses reserved name 'jeq', which is reserved by the kernel encoding.
Reserved kernel names: lam, _app, pair, fst, snd, arrow, sigma, Type, jeq, __implicitArg
-/
#guard_msgs (whitespace := lax) in
extend_type_theory ReservedExtensionBase where
  rule jeq : Good o

namespace ReservedExtensionBase

/--
error: internal declaration 'pair' uses reserved name 'pair', which is reserved by the kernel
encoding. Reserved kernel names: lam, _app, pair, fst, snd, arrow, sigma, Type, jeq, __implicitArg
-/
#guard_msgs (whitespace := lax) in
internal def pair : Obj := o

/--
error: internal declaration 'lam' uses reserved name 'lam', which is reserved by the kernel
encoding. Reserved kernel names: lam, _app, pair, fst, snd, arrow, sigma, Type, jeq, __implicitArg
-/
#guard_msgs (whitespace := lax) in
internal_defs where
  def lam : Obj := o

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
      name := `lam
      resultType := .tyConst `Obj }] }
  match CheckedKernelLFDerivation.ofReplay badConstantSig ctx stmt (.assumption `h stmt) with
  | .ok _ => throwError "reserved kernel constant was accepted by replay wrapper"
  | .error err =>
      unless err.contains "kernel LF constant declaration 'lam' uses reserved name 'lam'" do
        throwError "unexpected reserved-constant error: {err}"
  let badRuleSig : Signature := {
    name := `KernelReservedRuleSmoke
    rules := [{
      name := `jeq
      «conclusion» := stmt }] }
  match CheckedKernelLFDerivation.ofReplay badRuleSig ctx stmt (.assumption `h stmt) with
  | .ok _ => throwError "reserved kernel rule was accepted by replay wrapper"
  | .error err =>
      unless err.contains "kernel LF rule declaration 'jeq' uses reserved name 'jeq'" do
        throwError "unexpected reserved-rule error: {err}"
  let conversionStmt : ConversionStatement := {
    plugin := `p
    lhs := .tyConst `A
    rhs := .tyConst `A }
  match CheckedKernelLFConversionCertificate.check badConstantSig {} conversionStmt
      (.refl conversionStmt) with
  | .ok _ => throwError "reserved kernel constant was accepted by conversion wrapper"
  | .error err =>
      unless err.contains "kernel LF constant declaration 'lam' uses reserved name 'lam'" do
        throwError "unexpected reserved-conversion error: {err}"
