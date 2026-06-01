/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Fixture for incremental checker-cache import tests
-/

@[expose] public section

open InternalLean

declare_type_theory ImportedCacheBase where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x
  judgment_theorem imported : J base := intro base
