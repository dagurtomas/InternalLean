/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Legacy raw conversion-certificate regression tests

These tests exercise the legacy low-level raw executable conversion checker retained for
compatibility smoke coverage. Registered LF replay and object-tactic conversion plugins use the
structural kernel.

Deep structural conversion coverage lives in `KernelDualReplayTest.lean`.
-/

@[expose] public section

open InternalLean

namespace InternalLeanTest.RawConversion

/- Kernel-facing raw replay payload comparison is alpha-equivalent for LF lambda binders. -/
#guard
  Raw.alphaEq
    (Raw.tmApp `lam [.leanParam `x, .tmApp `id [.leanParam `x]])
    (Raw.tmApp `lam [.leanParam `y, .tmApp `id [.leanParam `y]])

/- The preferred replay API wraps raw derivations only after executable checking. -/
#guard
  let stmt := Judgment.custom `J []
  let ruleSchema : RuleSchema := RuleSchema.mk `intro [] [] [] [] [] stmt
  let sig : Signature := { name := `T, rules := [ruleSchema] }
  let raw := KernelLFDerivation.ruleApp `intro stmt {} [] []
  match CheckedKernelLFDerivation.ofDerivation sig {} raw with
  | .ok checked => checked.check.isOk
  | .error _ => false

/- Checked replay wrappers reject raw derivations that cannot be replayed. -/
#guard
  let stmt := Judgment.custom `J []
  let raw := KernelLFDerivation.ruleApp `missing stmt {} [] []
  match CheckedKernelLFDerivation.ofDerivation { name := `T } {} raw with
  | .ok _ => false
  | .error err => err.contains "unknown rule"

/- A non-identity beta redex should not reduce to its argument. -/
#guard
  let lhs := Raw.tmApp `_app [.tmApp `lam [.leanParam `x, .tmConst `c], .tmConst `a]
  let stmt : ConversionStatement := { plugin := `conv, lhs := lhs, rhs := .tmConst `a }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .executableChecked, supportedSteps := [.beta] }] }
  match KernelLFConversionCertificate.check sig (.pluginStep stmt .beta none [] "") stmt with
  | .ok _ => false
  | .error err => err.contains "beta step reduces lhs"

/- A non-identity beta redex should reduce by substituting into the lambda body. -/
#guard
  let lhs := Raw.tmApp `_app [.tmApp `lam [.leanParam `x, .tmConst `c], .tmConst `a]
  let stmt : ConversionStatement := { plugin := `conv, lhs := lhs, rhs := .tmConst `c }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .executableChecked, supportedSteps := [.beta] }] }
  match KernelLFConversionCertificate.check sig (.pluginStep stmt .beta none [] "") stmt with
  | .ok () => true
  | .error _ => false

/- Function eta contracts the explicit raw `_app` convention. -/
#guard
  let lhs := Raw.tmApp `lam [
    .leanParam `x,
    .tmApp `_app [.leanParam `f, .leanParam `x]]
  let stmt : ConversionStatement := { plugin := `conv, lhs := lhs, rhs := .leanParam `f }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .executableChecked, supportedSteps := [.eta] }] }
  match KernelLFConversionCertificate.check sig (.pluginStep stmt .eta none [] "") stmt with
  | .ok () => true
  | .error _ => false

/- Function eta refuses to capture a binder that also occurs in the function part. -/
#guard
  let lhs := Raw.tmApp `lam [
    .leanParam `x,
    .tmApp `_app [.tmApp `_app [.leanParam `f, .leanParam `x], .leanParam `x]]
  let stmt : ConversionStatement := { plugin := `conv, lhs := lhs, rhs := .leanParam `f }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .executableChecked, supportedSteps := [.eta] }] }
  match KernelLFConversionCertificate.check sig (.pluginStep stmt .eta none [] "") stmt with
  | .ok () => false
  | .error err => err.contains "eta step expected"

/- Sigma eta contracts a pair of projections from alpha-equivalent values. -/
#guard
  let p := Raw.tmConst `p
  let lhs := Raw.tmApp `pair [.tmApp `fst [p], .tmApp `snd [p]]
  let stmt : ConversionStatement := { plugin := `conv, lhs := lhs, rhs := p }
  let sig : Signature := { name := `T, conversionPlugins := [
    { name := `conv, trust := .executableChecked, supportedSteps := [.eta] }] }
  match KernelLFConversionCertificate.check sig (.pluginStep stmt .eta none [] "") stmt with
  | .ok () => true
  | .error _ => false

end InternalLeanTest.RawConversion
