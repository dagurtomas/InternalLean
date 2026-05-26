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

open Lean Elab Command
open InternalLean

set_option internalLean.profileInternalDef true

/-- Test helper asserting stable registration-profile totals without depending on all text. -/
elab "#guard_internal_registration_profile_totals " theory:ident events:num inc:num objs:num
    thms:num : command => do
  let profiles ← liftCoreM <| getInternalRegistrationProfilesFor theory.getId
  let totals := profiles.foldl
    (init := (0, 0, 0))
    (fun (objTotal, thmTotal, incTotal) p =>
      (objTotal + p.recheckedObjectDefs, thmTotal + p.recheckedJudgmentTheorems,
        incTotal + p.incrementallyChecked))
  unless profiles.size == events.getNat do
    throwError "expected {events.getNat} registration profile event(s) for '{theory.getId}', \
      found {profiles.size}"
  unless totals.1 == objs.getNat && totals.2.1 == thms.getNat && totals.2.2 == inc.getNat do
    throwError "unexpected registration profile totals for '{theory.getId}': rechecked \
      {totals.1} object def(s), {totals.2.1} theorem(s); incremental={totals.2.2}"

/-- Test helper asserting that a registration strategy was used. -/
elab "#guard_internal_registration_profile_strategy " theory:ident expected:str : command => do
  let profiles ← liftCoreM <| getInternalRegistrationProfilesFor theory.getId
  let expected := expected.getString
  unless profiles.any (fun p => p.strategy == expected) do
    let strategies := profiles.toList.map (fun p => p.strategy)
    throwError "expected registration strategy '{expected}' for '{theory.getId}', found \
      {String.intercalate ", " strategies}"

/-- Test helper asserting checked model-section metadata counts. -/
elab "#guard_model_section_counts " theory:ident sections:num memberships:num : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  unless checked.modelSections.size == sections.getNat do
    throwError "expected {sections.getNat} model section(s) for '{theory.getId}', found \
      {checked.modelSections.size}"
  unless checked.modelSectionMemberships.size == memberships.getNat do
    throwError "expected {memberships.getNat} model section membership(s) for '{theory.getId}', \
      found {checked.modelSectionMemberships.size}"

/-- Test helper asserting full and public/minimal renderable model-field counts. -/
elab "#guard_model_field_counts " theory:ident full:num pub:num : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let countFields (obs : Array LeanTypeModelGeneration.LFModelObligation) : Nat :=
    obs.foldl (init := 0) fun n o =>
      if o.generatedRole == .field && o.renderable then n + 1 else n
  let fullObs ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  let publicObs ←
    LeanTypeModelGeneration.validateLFModelObligations checked admittedNames .publicMode
  let fullFields := countFields fullObs
  let publicFields := countFields publicObs
  unless fullFields == full.getNat && publicFields == pub.getNat do
    throwError "unexpected model field counts for '{theory.getId}': full={fullFields}, \
      public={publicFields}"

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
#guard_model_field_counts InternalDefScaleSmoke 4 4

/--
warning: type theory 'InternalDefScaleSmoke' has 1 admitted internal declaration(s):
admitted internal theorem InternalDefScaleSmoke.admittedTheorem : J base [documented]
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
#guard_model_section_counts SectionResumeSmoke 1 2

set_option internalLean.profileInternalDef false

declare_type_theory ExtendProfileRecheckSmoke where
  syntax_sort Obj
  lf_opaque base : Obj
  lf_def d : Obj := base

extend_type_theory ExtendProfileRecheckSmoke where
  syntax_sort Extra

/--
info: registration profile for ExtendProfileRecheckSmoke: 2 event(s); total old-artifact
rechecks=0 object def(s), 0 theorem(s); incrementally checked=1
declare_type_theory: full declare_type_theory (streaming artifacts); prior=0 object def(s), 0
theorem(s); rechecked=0 object def(s), 0 theorem(s); incremental=0
extend_type_theory: incremental extend_type_theory (streaming block); prior=1 object def(s), 0
theorem(s); rechecked=0 object def(s), 0 theorem(s); incremental=1
-/
#guard_msgs (whitespace := lax) in
#print_internal_registration_profile ExtendProfileRecheckSmoke

declare_type_theory IncrementalExtendUseInternalSmoke where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj

namespace IncrementalExtendUseInternalSmoke

internal def d : Obj := base

end IncrementalExtendUseInternalSmoke

extend_type_theory IncrementalExtendUseInternalSmoke where
  rule introD : J d

/--
info: registration profile for IncrementalExtendUseInternalSmoke: 3 event(s); total old-artifact
rechecks=0 object def(s), 0 theorem(s); incrementally checked=2
declare_type_theory: full declare_type_theory (streaming artifacts); prior=0 object def(s), 0
theorem(s); rechecked=0 object def(s), 0 theorem(s); incremental=0
d: incremental LF object definition; prior=0 object def(s), 0 theorem(s); rechecked=0 object
def(s), 0 theorem(s); incremental=1
extend_type_theory: incremental extend_type_theory (streaming block); prior=1 object def(s), 0
theorem(s); rechecked=0 object def(s), 0 theorem(s); incremental=1
-/
#guard_msgs (whitespace := lax) in
#print_internal_registration_profile IncrementalExtendUseInternalSmoke

declare_type_theory IncrementalExtendTheoremBlockSmoke where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

extend_type_theory IncrementalExtendTheoremBlockSmoke where
  lf_def d : Obj := base
  judgment_theorem t : J d := intro d

/--
info: registration profile for IncrementalExtendTheoremBlockSmoke: 2 event(s); total old-artifact
rechecks=0 object def(s), 0 theorem(s); incrementally checked=2
declare_type_theory: full declare_type_theory (streaming artifacts); prior=0 object def(s), 0
theorem(s); rechecked=0 object def(s), 0 theorem(s); incremental=0
extend_type_theory: incremental extend_type_theory (streaming block); prior=0 object def(s), 0
theorem(s); rechecked=0 object def(s), 0 theorem(s); incremental=2
-/
#guard_msgs (whitespace := lax) in
#print_internal_registration_profile IncrementalExtendTheoremBlockSmoke

declare_type_theory IncrementalExtendUseTheoremSmoke where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

namespace IncrementalExtendUseTheoremSmoke

internal theorem t1 : J base := intro base

end IncrementalExtendUseTheoremSmoke

extend_type_theory IncrementalExtendUseTheoremSmoke where
  judgment_theorem t2 : J base := t1

#guard_internal_registration_profile_totals IncrementalExtendUseTheoremSmoke 3 2 0 0

declare_type_theory IncrementalExtendAfterExtensionInternalSmoke where
  syntax_sort Obj

extend_type_theory IncrementalExtendAfterExtensionInternalSmoke where
  lf_opaque extBase : Obj

namespace IncrementalExtendAfterExtensionInternalSmoke

internal def afterExt : Obj := extBase

end IncrementalExtendAfterExtensionInternalSmoke

#check IncrementalExtendAfterExtensionInternalSmoke.afterExt
#guard_internal_registration_profile_totals IncrementalExtendAfterExtensionInternalSmoke 3 2 0 0

declare_type_theory IncrementalExtendManyInternalsSmoke where
  syntax_sort Obj
  lf_opaque base : Obj

namespace IncrementalExtendManyInternalsSmoke

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
  def d11 : Obj := d10
  def d12 : Obj := d11

end IncrementalExtendManyInternalsSmoke

extend_type_theory IncrementalExtendManyInternalsSmoke where
  syntax_sort Extra01

extend_type_theory IncrementalExtendManyInternalsSmoke where
  syntax_sort Extra02

extend_type_theory IncrementalExtendManyInternalsSmoke where
  syntax_sort Extra03

extend_type_theory IncrementalExtendManyInternalsSmoke where
  syntax_sort Extra04

extend_type_theory IncrementalExtendManyInternalsSmoke where
  syntax_sort Extra05

#guard_internal_registration_profile_totals IncrementalExtendManyInternalsSmoke 18 17 0 0

declare_type_theory IncrementalModelMetadataSmoke where
  model_section Core
  syntax_sort Pub
  syntax_sort Hidden
  lf_opaque pub : Pub
  lf_opaque hidden : Hidden

extend_type_theory IncrementalModelMetadataSmoke where
  model_internal Hidden
  model_internal hidden
  model_section Extra
  syntax_sort ExtraSort
  model_section Core
  lf_opaque pub2 : Pub

#guard_internal_registration_profile_totals IncrementalModelMetadataSmoke 2 6 0 0
#guard_model_section_counts IncrementalModelMetadataSmoke 2 6
#guard_model_field_counts IncrementalModelMetadataSmoke 6 4

declare_type_theory IntraBlockLargeDefSmoke where
  syntax_sort Obj
  lf_opaque base : Obj

extend_type_theory IntraBlockLargeDefSmoke where
  lf_def d01 : Obj := base
  lf_def d02 : Obj := d01
  lf_def d03 : Obj := d02
  lf_def d04 : Obj := d03
  lf_def d05 : Obj := d04
  lf_def d06 : Obj := d05
  lf_def d07 : Obj := d06
  lf_def d08 : Obj := d07
  lf_def d09 : Obj := d08
  lf_def d10 : Obj := d09
  lf_def d11 : Obj := d10
  lf_def d12 : Obj := d11
  lf_def d13 : Obj := d12
  lf_def d14 : Obj := d13
  lf_def d15 : Obj := d14
  lf_def d16 : Obj := d15
  lf_def d17 : Obj := d16
  lf_def d18 : Obj := d17
  lf_def d19 : Obj := d18
  lf_def d20 : Obj := d19

#guard_internal_registration_profile_totals IntraBlockLargeDefSmoke 2 20 0 0
#guard_internal_registration_profile_strategy IntraBlockLargeDefSmoke
  "incremental extend_type_theory (streaming block)"

declare_type_theory IntraBlockLargeTheoremSmoke where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

extend_type_theory IntraBlockLargeTheoremSmoke where
  judgment_theorem t01 : J base := intro base
  judgment_theorem t02 : J base := t01
  judgment_theorem t03 : J base := t02
  judgment_theorem t04 : J base := t03
  judgment_theorem t05 : J base := t04
  judgment_theorem t06 : J base := t05
  judgment_theorem t07 : J base := t06
  judgment_theorem t08 : J base := t07
  judgment_theorem t09 : J base := t08
  judgment_theorem t10 : J base := t09
  judgment_theorem t11 : J base := t10
  judgment_theorem t12 : J base := t11
  judgment_theorem t13 : J base := t12
  judgment_theorem t14 : J base := t13
  judgment_theorem t15 : J base := t14
  judgment_theorem t16 : J base := t15
  judgment_theorem t17 : J base := t16
  judgment_theorem t18 : J base := t17
  judgment_theorem t19 : J base := t18
  judgment_theorem t20 : J base := t19

#guard_internal_registration_profile_totals IntraBlockLargeTheoremSmoke 2 20 0 0
#guard_internal_registration_profile_strategy IntraBlockLargeTheoremSmoke
  "incremental extend_type_theory (streaming block)"

declare_type_theory IntraBlockLargeDeclareSmoke where
  syntax_sort Obj
  lf_opaque base : Obj
  lf_def d01 : Obj := base
  lf_def d02 : Obj := d01
  lf_def d03 : Obj := d02
  lf_def d04 : Obj := d03
  lf_def d05 : Obj := d04
  lf_def d06 : Obj := d05
  lf_def d07 : Obj := d06
  lf_def d08 : Obj := d07
  lf_def d09 : Obj := d08
  lf_def d10 : Obj := d09
  lf_def d11 : Obj := d10
  lf_def d12 : Obj := d11

#guard_internal_registration_profile_totals IntraBlockLargeDeclareSmoke 1 0 0 0
#guard_internal_registration_profile_strategy IntraBlockLargeDeclareSmoke
  "full declare_type_theory (streaming artifacts)"

declare_type_theory SorryAdmissionIncrementalSmoke where
  syntax_sort Obj
  lf_opaque base : Obj

namespace SorryAdmissionIncrementalSmoke

internal def d01 : Obj := base
internal def d02 : Obj := d01

#guard_msgs (drop warning) in
internal def admitted01 : Obj := sorry

#guard_msgs (drop warning) in
internal def admitted02 : Obj := sorry

end SorryAdmissionIncrementalSmoke

extend_type_theory SorryAdmissionIncrementalSmoke where
  lf_def after : Obj := admitted02

#check_type_theory SorryAdmissionIncrementalSmoke
#guard_internal_registration_profile_totals SorryAdmissionIncrementalSmoke 6 5 0 0
#guard_internal_registration_profile_strategy SorryAdmissionIncrementalSmoke
  "incremental admitted LF opaque"
#guard_internal_registration_profile_strategy SorryAdmissionIncrementalSmoke
  "incremental extend_type_theory (streaming block)"

declare_type_theory SorryAdmissionBatchSmoke where
  syntax_sort Obj
  lf_opaque base : Obj

namespace SorryAdmissionBatchSmoke

#guard_msgs (drop warning) in
internal_defs where
  def admitted01 : Obj := sorry
  def admitted02 : Obj := sorry
  def admitted03 : Obj := sorry
  def admitted04 : Obj := sorry

end SorryAdmissionBatchSmoke

extend_type_theory SorryAdmissionBatchSmoke where
  lf_def after : Obj := admitted04

#check_type_theory SorryAdmissionBatchSmoke
#guard_internal_registration_profile_totals SorryAdmissionBatchSmoke 3 5 0 0
#guard_internal_registration_profile_strategy SorryAdmissionBatchSmoke
  "incremental admitted LF opaque batch"

declare_type_theory SorryAdmissionTheoremRouteSmoke where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

namespace SorryAdmissionTheoremRouteSmoke

#guard_msgs (drop warning) in
internal def admittedTheorem : J base := sorry

end SorryAdmissionTheoremRouteSmoke

#guard_internal_registration_profile_totals SorryAdmissionTheoremRouteSmoke 2 1 0 0
#guard_internal_registration_profile_strategy SorryAdmissionTheoremRouteSmoke
  "incremental LF judgment admission"

declare_type_theory IncrementalRoleMetadataSmoke where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x
  lf_def d : Obj := base

extend_type_theory IncrementalRoleMetadataSmoke where
  syntax_sort_role Obj : term_sort
  judgment_role J : term_typing
  rule_role intro : introduction

#check_type_theory IncrementalRoleMetadataSmoke
#guard_internal_registration_profile_totals IncrementalRoleMetadataSmoke 2 3 0 0
#guard_internal_registration_profile_strategy IncrementalRoleMetadataSmoke
  "incremental extend_type_theory (streaming block)"

declare_type_theory IncrementalContextBinderMetadataSmoke where
  syntax_sort Ctx
  syntax_sort Tm (Γ : Ctx)

extend_type_theory IncrementalContextBinderMetadataSmoke where
  context_zone ordinary : Ctx
  binder_class ordinary_var : Tm in ordinary

#check_type_theory IncrementalContextBinderMetadataSmoke
#guard_internal_registration_profile_totals IncrementalContextBinderMetadataSmoke 2 2 0 0
#guard_internal_registration_profile_strategy IncrementalContextBinderMetadataSmoke
  "incremental extend_type_theory (streaming block)"

