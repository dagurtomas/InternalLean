/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLeanTest.TinyNat

/-!
# Mirror oracle smoke tests

This file keeps the experimental Lean mirror backend available as a differential-testing oracle.
The LF checker remains authoritative; these commands only compare already checked declarations.
-/

@[expose] public section

open Lean InternalLean

run_cmd do
  if ← getBoolOption `internalLean.mirrorBackend.checkTheoryBodies then
    throwError "internalLean.mirrorBackend.checkTheoryBodies must default to false"

declare_type_theory MirrorOracleMixedSmoke where
  syntax_sort Obj
  syntax_abbrev ObjAlias := Obj
  syntax_def ObjDef : Type := Obj
  judgment Good (x : Obj)
  judgment_abbrev GoodAlias (x : Obj) := Good x
  lf_opaque o : Obj
  rule good_o : Good o
  lf_def oAlias : ObjAlias := o
  judgment_theorem oGood : GoodAlias oAlias := good_o

namespace MirrorOracleMixedSmoke

set_option internalLean.preferLeanQuotedFrontend true in
set_option internalLean.frontend.compareLegacy true in
internal def compare_mode_body : Obj := oAlias

end MirrorOracleMixedSmoke

namespace TinyNat

set_option internalLean.preferLeanQuotedFrontend true in
set_option internalLean.frontend.compareLegacy true in
internal def phase0_compare_zero : Nat := zero

end TinyNat

#compare_lf_mirror_theory TinyNat
#compare_lf_mirror_theory MirrorOracleMixedSmoke
