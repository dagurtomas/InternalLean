/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Raw conversion-certificate regression tests

These tests exercise low-level executable conversion checks used by the kernel-facing replay
boundary.
-/

@[expose] public section

open InternalLean

namespace InternalLeanTest.RawConversion

/- Kernel-facing raw replay payload comparison is alpha-equivalent for LF lambda binders. -/
#guard
  Raw.alphaEq
    (Raw.tmApp `lam [.leanParam `x, .tmApp `id [.leanParam `x]])
    (Raw.tmApp `lam [.leanParam `y, .tmApp `id [.leanParam `y]])

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

end InternalLeanTest.RawConversion
