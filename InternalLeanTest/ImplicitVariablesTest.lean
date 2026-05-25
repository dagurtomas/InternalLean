/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Implicit variable tests

These tests exercise ordinary implicit object binders and insertion of omitted implicit
arguments before LF replay/checking sees the fully explicit application spine.
-/

@[expose] public section

open Lean

declare_type_theory ImplicitVariablesSmoke where
  syntax_sort Obj
  syntax_sort El (A : Obj)
  judgment Has (A : Obj) (x : El A)
  lf_opaque A : Obj
  lf_opaque B : Obj
  lf_opaque a : El A
  lf_opaque b : El B
  lf_opaque id {A : Obj} (x : El A) : El A
  lf_opaque constObj {A : Obj} : Obj
  rule has_id {A : Obj} (x : El A) : Has A (id x)
  lf_def id_a : El A := id a
  lf_def id_a_named : El A := id {A := A} a
  lf_def id_a_explicit : El A := id A a
  judgment_theorem has_id_a : Has A (id a) := has_id a

#check_type_theory_anchor ImplicitVariablesSmoke
generate_lf_model_structure ImplicitVariablesSmoke as ImplicitVariablesModel

/-- info: ImplicitVariablesSmoke.ImplicitVariablesModel.id (self :
ImplicitVariablesSmoke.ImplicitVariablesModel) {A : self.Obj}
  (x : self.El A) : self.El A -/
#guard_msgs (whitespace := lax) in
#check ImplicitVariablesSmoke.ImplicitVariablesModel.id

/-- info: ImplicitVariablesSmoke.ImplicitVariablesModel.has_id (self :
ImplicitVariablesSmoke.ImplicitVariablesModel)
  {A : self.Obj} (x : self.El A) : self.Has A (self.id x) -/
#guard_msgs (whitespace := lax) in
#check ImplicitVariablesSmoke.ImplicitVariablesModel.has_id

namespace ImplicitVariablesSmoke

internal def has_id_a_tactic : Has A (id a) := by
  exact has_id a

#check has_id_a_tactic

end ImplicitVariablesSmoke

/-- info: type theory ImplicitVariablesSmoke with 15 logical-framework declarations
---
info: syntax_sort Obj
---
info: syntax_sort El (A : Obj)
---
info: judgment Has (A : Obj) (x : El A)
---
info: rule has_id {A : Obj} (x : El A) : Has A (id A x)
---
info: lf_opaque A  : Obj
---
info: lf_opaque B  : Obj
---
info: lf_opaque a  : El A
---
info: lf_opaque b  : El B
---
info: lf_opaque id {A : Obj} (x : El A) : El A
---
info: lf_opaque constObj {A : Obj} : Obj
---
info: lf_def id_a : El A := id A a
---
info: lf_def id_a_named : El A := id A a
---
info: lf_def id_a_explicit : El A := id A a
---
info: judgment_theorem has_id_a : Has A (id A a) := has_id A a
---
info: judgment_theorem has_id_a_tactic : Has A (id A a) := has_id A a -/
#guard_msgs (whitespace := lax) in
#print_type_theory ImplicitVariablesSmoke

/-- error: lf_def 'bad' could not infer implicit argument 'A : Obj' in application 'constObj' in
value; use a named implicit argument or supply all arguments explicitly -/
#guard_msgs (whitespace := lax) in
declare_type_theory ImplicitVariablesUnsolved where
  syntax_sort Obj
  lf_opaque A : Obj
  lf_opaque constObj {A : Obj} : Obj
  lf_def bad : Obj := constObj

/-- error: lf_def 'bad' could not infer implicit arguments for application 'id' in value from
expected expression
  El A
while matching result
  El B
reason: rigid expressions do not match: expected 'B', got 'A' -/
#guard_msgs (whitespace := lax) in
declare_type_theory ImplicitVariablesConflict where
  syntax_sort Obj
  syntax_sort El (A : Obj)
  lf_opaque A : Obj
  lf_opaque B : Obj
  lf_opaque b : El B
  lf_opaque id {A : Obj} (x : El A) : El A
  lf_def bad : El A := id b
