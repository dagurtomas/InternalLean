/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Generated LF-model local-name hygiene tests

Accepted LF local binder names should not shadow generated model variables or produce non-atomic
Lean binders in generated model interfaces/transports.
-/

@[expose] public section

open InternalLean

declare_type_theory BinderMSmoke where
  syntax_sort Obj
  judgment J (x : Obj)
  rule intro (M : Obj) : J M
  judgment_theorem t (M : Obj) : J M := intro M

generate_model_interface BinderMSmoke as Model
generate_lf_model_transports BinderMSmoke only t for Model
#check BinderMSmoke.Model.t

declare_type_theory QualifiedBinderSmoke where
  syntax_sort Obj
  judgment J (Foo.Bar : Obj)
  rule intro (Foo.Bar : Obj) : J Foo.Bar
  judgment_theorem t (Foo.Bar : Obj) : J Foo.Bar := intro Foo.Bar

generate_model_interface QualifiedBinderSmoke as Model
generate_lf_model_transports QualifiedBinderSmoke only t for Model
#check QualifiedBinderSmoke.Model.J
#check QualifiedBinderSmoke.Model.t
