/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Top-level internal declaration tests

These tests exercise `internal def` over the direct-LF declaration path.
-/

@[expose] public section

open Lean

declare_type_theory InternalDefLFSmoke where
  syntax_sort Obj
  judgment Rel (x : Obj) (y : Obj)
  lf_opaque a : Obj
  lf_opaque b : Obj
  rule edge_ab_rule : Rel a b
  rule rel_refl (x : Obj) : Rel x x
  judgment_theorem edge_ab : Rel a b := edge_ab_rule

namespace InternalDefLFSmoke

internal def rel_aa : Rel a a := rel_refl a
internal def edge_ab_again : Rel a b := edge_ab
internal def aliasA : Obj := a

#check rel_aa
#check edge_ab_again
#check aliasA

end InternalDefLFSmoke

internal def InternalDefLFSmoke.aliasB : Obj := b
internal def InternalDefLFSmoke.rel_aliasB : Rel aliasB aliasB := rel_refl aliasB

#check InternalDefLFSmoke.aliasB
#check InternalDefLFSmoke.rel_aliasB

/-- error: cannot infer target type theory for `internal def lonely`

Write the declaration inside a declared theory namespace, for example:
  namespace YourTheory
  internal def lonely : ... := ...
  end YourTheory

or qualify the declaration name:
  internal def YourTheory.lonely : ... := ... -/
#guard_msgs (whitespace := lax) in
internal def lonely : Obj := a

/-- error: unknown type theory 'MissingTheory'

No theory anchor named 'MissingTheory.theory' is available in the current environment. Use
`declare_type_theory MissingTheory where ...` first, import the module that declares it, or qualify
the declaration name with the namespace of an existing theory. -/
#guard_msgs (whitespace := lax) in
internal def MissingTheory.foo : Obj := a

/-- warning: internal declaration 'InternalDefLFSmoke.admittedRel' was admitted by `sorry`; the
annotation was checked in theory 'InternalDefLFSmoke', but the body was not checked. Use
`#lint_type_theory_sorries InternalDefLFSmoke` to list current admissions. -/
#guard_msgs (whitespace := lax) in
internal def InternalDefLFSmoke.admittedRel : Rel a b := sorry

/-- warning: type theory 'InternalDefLFSmoke' has 1 admitted internal declaration(s):
admitted internal theorem InternalDefLFSmoke.admittedRel : Rel a b [missing doc] -/
#guard_msgs (whitespace := lax) in
#lint_type_theory_sorries InternalDefLFSmoke

generate_model_interface InternalDefLFSmoke as InternalDefLFSmokeModel
#print_model_transport_status InternalDefLFSmoke for InternalDefLFSmokeModel
#print_model_transport_signature InternalDefLFSmoke rel_aa for InternalDefLFSmokeModel
generate_model_transport InternalDefLFSmoke rel_aa for InternalDefLFSmokeModel
#check InternalDefLFSmoke.InternalDefLFSmokeModel.rel_aa
#print_model_transport_signature InternalDefLFSmoke admittedRel for InternalDefLFSmokeModel
generate_model_transport InternalDefLFSmoke admittedRel for InternalDefLFSmokeModel
#check InternalDefLFSmoke.InternalDefLFSmokeModel.admittedRel
