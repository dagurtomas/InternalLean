/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Basic
public import InternalLean.Command

/-!
# Legacy raw conversion capture tests

The legacy executable raw beta checker must not accept a reduct that captures a free raw local.
Structural conversion-certificate coverage lives in `KernelDualReplayTest.lean`.
-/

@[expose] public section

open InternalLean

namespace RawConversionCaptureTest

def sig : Signature := {
  name := `RawConversionCaptureTest
  conversionPlugins := [
    { name := `beta, trust := .executableChecked, supportedSteps := [.beta] }]
}

/-- `((fun x => fun y => x) y)` in the raw LF lambda convention. -/
def lhs : Raw :=
  .tmApp `_app [
    .tmApp `lam [.leanParam `x, .tmApp `lam [.leanParam `y, .leanParam `x]],
    .leanParam `y]

/-- The capture-unsafe reduct `fun y => y`. -/
def captured : Raw := .tmApp `lam [.leanParam `y, .leanParam `y]

/-- A capture-avoiding reduct, up to alpha-equivalence. -/
def correct : Raw := .tmApp `lam [.leanParam `z, .leanParam `y]

def capturedStmt : ConversionStatement := { plugin := `beta, lhs := lhs, rhs := captured }
def correctStmt : ConversionStatement := { plugin := `beta, lhs := lhs, rhs := correct }

def checkCaptured :=
  KernelLFConversionCertificate.check sig (.pluginStep capturedStmt .beta none [] "")
    capturedStmt

def checkCorrect :=
  KernelLFConversionCertificate.check sig (.pluginStep correctStmt .beta none [] "") correctStmt

#guard (match checkCaptured with | .error _ => true | .ok _ => false)
#guard (match checkCorrect with | .ok _ => true | .error _ => false)
#guard !Raw.alphaEq captured correct

end RawConversionCaptureTest
