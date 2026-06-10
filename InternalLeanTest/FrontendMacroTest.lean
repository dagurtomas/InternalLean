/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Theory-local frontend macro smoke tests

These tests exercise user-space object macros and non-semantic role metadata over the
current direct-LF surface.
-/

@[expose] public section

namespace InternalLeanTest.FrontendMacroTest

open InternalLean

declare_type_theory MacroSmoke where
  syntax_sort Obj
  judgment Rel (x : Obj) (y : Obj)
  lf_opaque base : Obj
  rule rel_refl (x : Obj) : Rel x x

object_macro MacroSmoke SelfRel (A) => Rel A A
object_role MacroSmoke SelfRel : derivedJudgment
object_role MacroSmoke rel_refl : intro for SelfRel

#expand_object MacroSmoke SelfRel base
#print_object_macros MacroSmoke
#print_object_roles MacroSmoke

/--
error: failed to check internal LF declaration 'MacroSmoke.bad' in type theory 'MacroSmoke'

Classification was ambiguous: expected type has head 'SelfRel', so it is not visibly headed by a
judgment, judgment abbreviation, syntax sort, syntax abbreviation, syntax definition, or structural
object type.

LF object definition path:
object_macro 'SelfRel' in type theory 'MacroSmoke' is diagnostic-only and cannot appear in checked
LF declarations; expand it before writing type of lf_def 'bad'

LF judgment theorem path:
object_macro 'SelfRel' in type theory 'MacroSmoke' is diagnostic-only and cannot appear in checked
LF declarations; expand it before writing statement of judgment_theorem 'bad'
-/
#guard_msgs (whitespace := lax) in
internal def MacroSmoke.bad : SelfRel base := rel_refl base

internal def MacroSmoke.baseRel : Rel base base :=
  rel_refl base

#check_type_theory MacroSmoke
#print_type_theory MacroSmoke

end InternalLeanTest.FrontendMacroTest
