/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Internal declaration scalability tests

These smoke tests exercise incremental `internal def`/theorem registration, the batch command, and
non-model-facing theorem admissions.
-/

@[expose] public section

open InternalLean

set_option internalLean.profileInternalDef true

declare_type_theory InternalDefScaleSmoke where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

namespace InternalDefScaleSmoke

internal_defs where
  def d01 : Obj := base
  def d02 : Obj := d01
  def d03 : Obj := d02
  def d04 : Obj := d03
  def d05 : Obj := d04
  def d06 : Obj := d05
  def d07 : Obj := d06
  def d08 : Obj := d07
  def d09 : Obj := d08
  def d10 : Obj := d09

internal def d11 : Obj := d10
internal def d12 : Obj := d11
internal def d13 : Obj := d12
internal def d14 : Obj := d13
internal def d15 : Obj := d14

internal theorem t01 : J base := intro base
internal theorem t02 : J base := t01
internal def t03 : J base := t02

#guard_msgs (drop warning) in
/-- Temporary theorem-shaped admission for lint/model-obligation behavior. -/
internal theorem admittedTheorem : J base := sorry

end InternalDefScaleSmoke

#check InternalDefScaleSmoke.d15
#check InternalDefScaleSmoke.t03
#print_internal_registration_profile InternalDefScaleSmoke
#print_model_obligations InternalDefScaleSmoke

/--
warning: type theory 'InternalDefScaleSmoke' has 1 admitted internal declaration(s):
admitted internal def InternalDefScaleSmoke.admittedTheorem : J base [documented]
-/
#guard_msgs (whitespace := lax) in
#lint_type_theory_sorries InternalDefScaleSmoke

/--
info: LF model obligation validation self-tests passed
-/
#guard_msgs in
#check_lf_model_obligation_validation_self_tests

declare_type_theory SectionResumeSmoke where
  model_section Chapter
  syntax_sort A

extend_type_theory SectionResumeSmoke where
  model_section Chapter
  syntax_sort B

#print_model_sections SectionResumeSmoke

