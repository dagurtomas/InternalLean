/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Basic
public import InternalLean.DSL
public import InternalLean.Registry
public meta import InternalLean.ModelTransport
public meta import InternalLean.LeanFrontend.Elab
public meta import InternalLean.LeanFrontend.Mirror

/-!
# Public command import for user-declared type theories

This module intentionally re-exports the focused command/elaboration modules under the
stable `InternalLean.Command` import path.
-/
