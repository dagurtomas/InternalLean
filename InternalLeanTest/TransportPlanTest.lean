/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Direct-LF model transport smoke test

This file keeps a small regression for the supported direct-LF transport commands.
-/

@[expose] public section

declare_type_theory DirectLFTransportSmoke where
  syntax_sort Obj
  judgment Rel (x : Obj) (y : Obj)
  lf_opaque a : Obj
  rule rel_refl (x : Obj) : Rel x x
  lf_def aliasA : Obj := a
  judgment_theorem rel_aliasA : Rel aliasA aliasA := rel_refl aliasA

generate_model_interface DirectLFTransportSmoke as DirectLFTransportSmokeModel
#print_lf_model_transports DirectLFTransportSmoke for DirectLFTransportSmokeModel
generate_lf_model_transports DirectLFTransportSmoke only rel_aliasA for DirectLFTransportSmokeModel
#check DirectLFTransportSmoke.DirectLFTransportSmokeModel.rel_aliasA
