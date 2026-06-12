/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Theory mixin composition tests

These tests exercise parent-DAG flattening for shared-ancestor diamonds.  M1 intentionally routes
shared-ancestor `declare_type_theory ... extends ...` blocks through the full checker, while
sharing-free parent trees keep the incremental path.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

/-- Assert that a theory has a registration profile entry using the requested strategy. -/
elab "#guard_mixin_registration_strategy " theory:ident expected:str : command => do
  let profiles ← liftCoreM <| getInternalRegistrationProfilesFor theory.getId
  let expected := expected.getString
  unless profiles.any (fun p => p.strategy == expected) do
    let strategies := profiles.toList.map (fun p => p.strategy)
    throwError "expected registration strategy '{expected}' for '{theory.getId}', found \
      {String.intercalate ", " strategies}"

/-- Assert syntax-sort and LF-opaque counts in a flattened signature. -/
elab "#guard_mixin_flat_counts " theory:ident sorts:num opaques:num : command => do
  let some sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let flat ← liftCoreM <| flattenSignature sig
  unless flat.syntaxSorts.size == sorts.getNat do
    throwError "expected {sorts.getNat} flattened syntax sort(s) for '{theory.getId}', found \
      {flat.syntaxSorts.size}"
  unless flat.lfOpaqueConsts.size == opaques.getNat do
    throwError "expected {opaques.getNat} flattened LF opaque(s) for '{theory.getId}', found \
      {flat.lfOpaqueConsts.size}"

/-- Assert checked role and model-section metadata counts. -/
elab "#guard_mixin_role_section_counts " theory:ident roles:num sections:num memberships:num :
    command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  unless checked.lfSyntaxSortRoles.size == roles.getNat do
    throwError "expected {roles.getNat} syntax-sort role(s), found \
      {checked.lfSyntaxSortRoles.size}"
  unless checked.modelSections.size == sections.getNat do
    throwError "expected {sections.getNat} model section(s), found {checked.modelSections.size}"
  unless checked.modelSectionMemberships.size == memberships.getNat do
    throwError "expected {memberships.getNat} model-section membership(s), found \
      {checked.modelSectionMemberships.size}"

/-- Assert the number of model fields produced from checked obligations. -/
elab "#guard_mixin_model_field_count " theory:ident expected:num : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let obligations ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  let fields := obligations.foldl (init := 0) fun n o =>
    if o.generatedRole == .field && o.renderable then n + 1 else n
  unless fields == expected.getNat do
    throwError "expected {expected.getNat} model field(s) for '{theory.getId}', found {fields}"

/-- Assert inherited internal admissions are deduplicated. -/
elab "#guard_mixin_admission_count " theory:ident expected:num : command => do
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  unless admissions.size == expected.getNat do
    throwError "expected {expected.getNat} inherited admission(s) for '{theory.getId}', found \
      {admissions.size}"

/-- Assert flattened level-parameter count. -/
elab "#guard_mixin_level_param_count " theory:ident expected:num : command => do
  let some sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let flat ← liftCoreM <| flattenSignature sig
  unless flat.levelParams.size == expected.getNat do
    throwError "expected {expected.getNat} flattened level parameter(s) for '{theory.getId}', \
      found {flat.levelParams.size}"

/-- Assert compiled-cache and checked-HL invariants for a diamond child. -/
elab "#guard_mixin_cache_invariant " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let some cache ← liftCoreM <| getCompiledLFCheckCache? theory.getId
    | throwError "no compiled cache stored for type theory '{theory.getId}'"
  let expectedStamp := CompiledLFCheckCacheStamp.ofCheckedSignature checked
  unless cache.stamp == expectedStamp do
    throwError "compiled-cache stamp for '{theory.getId}' does not match checked artifact"
  unless checkedHLSignatureMatchesChecked cache.checkedHL checked do
    throwError "checked-HL signature for '{theory.getId}' does not match checked artifact"

declare_type_theory MixinBase where
  syntax_sort A

declare_type_theory MixinLeft extends MixinBase where
  lf_opaque x : A

declare_type_theory MixinRight extends MixinBase where
  lf_opaque y : A

declare_type_theory MixinChild extends MixinLeft, MixinRight where
  lf_opaque z : A

extend_type_theory MixinChild where
  lf_opaque w : A

#guard_mixin_registration_strategy MixinChild
  "full fallback declare_type_theory: shared parent ancestor"
#guard_mixin_flat_counts MixinChild 1 4
#guard_mixin_cache_invariant MixinChild

generate_model_interface MixinChild as Model
#check MixinChild.Model.A
#guard_mixin_model_field_count MixinChild 5

/--
info: parent DAG for MixinChild:
MixinChild
  MixinLeft
    MixinBase
  MixinRight
    MixinBase (already included via MixinChild -> MixinLeft -> MixinBase)
deduped shared ancestors: MixinBase
-/
#guard_msgs in
#print_type_theory_parents MixinChild

declare_type_theory MixinBadLeft where
  syntax_sort A

declare_type_theory MixinBadRight where
  syntax_sort A

/--
error: conflicting inherited declaration 'A' in type theory 'MixinBad'
from parent path MixinBad -> MixinBadLeft and parent path MixinBad -> MixinBadRight
existing declaration is syntax-sort from 'MixinBadLeft', new declaration is syntax-sort from
  'MixinBadRight'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory MixinBad extends MixinBadLeft, MixinBadRight where
  lf_opaque z : A

declare_type_theory MixinRoleBase where
  syntax_sort A
  syntax_sort_role A : universe_level
  model_section Core
  lf_opaque base : A

declare_type_theory MixinRoleLeft extends MixinRoleBase where
  lf_opaque x : A

declare_type_theory MixinRoleRight extends MixinRoleBase where
  lf_opaque y : A

declare_type_theory MixinRoleChild extends MixinRoleLeft, MixinRoleRight where
  lf_opaque z : A

#guard_mixin_role_section_counts MixinRoleChild 1 1 1

declare_type_theory MixinAdmissionBase where
  syntax_sort A

namespace MixinAdmissionBase

internal def admitted : A := sorry

end MixinAdmissionBase

declare_type_theory MixinAdmissionLeft extends MixinAdmissionBase where
  lf_opaque x : A

declare_type_theory MixinAdmissionRight extends MixinAdmissionBase where
  lf_opaque y : A

declare_type_theory MixinAdmissionChild extends MixinAdmissionLeft, MixinAdmissionRight where
  lf_opaque z : A

#guard_mixin_admission_count MixinAdmissionChild 1

declare_type_theory MixinTreeLeft where
  syntax_sort L

declare_type_theory MixinTreeRight where
  syntax_sort R

declare_type_theory MixinTreeChild extends MixinTreeLeft, MixinTreeRight where
  lf_opaque x : L

#guard_mixin_registration_strategy MixinTreeChild
  "incremental declare_type_theory extends (streaming block)"

declare_type_theory MixinLinearBase where
  syntax_sort A
  lf_opaque x : A

declare_type_theory MixinLinearMid extends MixinLinearBase where
  lf_opaque y : A

declare_type_theory MixinLinearChild extends MixinLinearMid where
  lf_opaque z : A

run_cmd do
  let some sig ← liftCoreM <| getTheory? `MixinLinearChild
    | throwError "missing MixinLinearChild"
  let flat ← liftCoreM <| flattenSignature sig
  let opaqueNames := flat.lfOpaqueConsts.map (fun d => d.name.eraseMacroScopes)
  unless opaqueNames == #[`x, `y, `z] do
    throwError "unexpected linear-chain LF opaque order: {opaqueNames}"

declare_type_theory MixinLevelBase{u} where
  syntax_sort A : Type u

declare_type_theory MixinLevelLeft extends MixinLevelBase where
  lf_opaque x : A

declare_type_theory MixinLevelRight extends MixinLevelBase where
  lf_opaque y : A

declare_type_theory MixinLevelChild extends MixinLevelLeft, MixinLevelRight where
  lf_opaque z : A

#guard_mixin_level_param_count MixinLevelChild 1

declare_type_theory MixinLevelBadLeft{u} where
  syntax_sort A : Type u

declare_type_theory MixinLevelBadRight{u} where
  syntax_sort B : Type u

/--
error: conflicting inherited declaration 'u' in type theory 'MixinLevelBad'
from parent path MixinLevelBad -> MixinLevelBadLeft and parent path MixinLevelBad ->
  MixinLevelBadRight
existing declaration is universe level parameter from 'MixinLevelBadLeft', new declaration is
  universe level parameter from 'MixinLevelBadRight'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory MixinLevelBad extends MixinLevelBadLeft, MixinLevelBadRight where
  lf_opaque z : A
