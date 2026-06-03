/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Editor navigation metadata tests

These checks verify the source anchors used by Lean's language-server go-to-definition support for
InternalLean declarations and generated model-interface fields.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

/-- Test helper asserting that an InternalLean source declaration has a Lean navigation anchor. -/
elab "#guard_internal_source_anchor " theory:ident source:ident : command => do
  let some anchor ← liftCoreM <| internalSourceDeclAnchorName? theory.getId source.getId
    | throwError "missing source anchor for '{theory.getId}.{source.getId}'"
  unless (← getEnv).contains anchor do
    throwError "source anchor '{anchor}' is not a Lean declaration"
  unless (← liftCoreM <| findDeclarationRanges? anchor).isSome do
    throwError "source anchor '{anchor}' has no declaration ranges"

/-- Test helper asserting that a generated model field projects back to the source declaration
range when the model interface is generated in the same module as the source theory. -/
elab "#guard_model_field_source_range " theory:ident structureName:ident field:ident : command => do
  let some sourceAnchor ← liftCoreM <| internalSourceDeclAnchorName? theory.getId field.getId
    | throwError "missing source anchor for '{theory.getId}.{field.getId}'"
  let projectionName := theory.getId ++ structureName.getId ++ field.getId
  let some sourceRanges ← liftCoreM <| findDeclarationRanges? sourceAnchor
    | throwError "source anchor '{sourceAnchor}' has no declaration ranges"
  let some projectionRanges ← liftCoreM <| findDeclarationRanges? projectionName
    | throwError "projection '{projectionName}' has no declaration ranges"
  unless sourceRanges.selectionRange == projectionRanges.selectionRange do
    throwError "projection '{projectionName}' selection range does not point to source \
      declaration '{sourceAnchor}'"

/-- Navigation smoke theory. -/
declare_type_theory NavigationSmoke where
  /-- Object sort used by navigation tests. -/
  syntax_sort Obj
  /-- Predicate used by navigation tests. -/
  judgment J (x : Obj)
  /-- Base object used by navigation tests. -/
  lf_opaque base : Obj
  /-- Introduction rule used by navigation tests. -/
  rule intro (x : Obj) : J x
  /-- Alias used by navigation tests. -/
  lf_def alias : Obj := base
  /-- Checked theorem used by navigation tests. -/
  judgment_theorem alias_ok : J alias := intro alias

#guard_internal_source_anchor NavigationSmoke Obj
#guard_internal_source_anchor NavigationSmoke J
#guard_internal_source_anchor NavigationSmoke base
#guard_internal_source_anchor NavigationSmoke intro
#guard_internal_source_anchor NavigationSmoke alias
#guard_internal_source_anchor NavigationSmoke alias_ok

/-- Top-level checked definition used by navigation tests. -/
internal def NavigationSmoke.checkedBase : Obj := base
/-- Top-level checked theorem used by navigation tests. -/
internal theorem NavigationSmoke.checkedBase_ok : J checkedBase := intro checkedBase

internal_defs where
  /-- Batched checked definition used by navigation tests. -/
  def NavigationSmoke.batchedBase : Obj := checkedBase

#guard_internal_source_anchor NavigationSmoke checkedBase
#guard_internal_source_anchor NavigationSmoke checkedBase_ok
#guard_internal_source_anchor NavigationSmoke batchedBase

extend_type_theory NavigationSmoke where
  /-- Extension constant used by navigation tests. -/
  lf_opaque extBase : Obj

#guard_internal_source_anchor NavigationSmoke extBase

generate_model_interface NavigationSmoke as NavigationModel

#guard_model_field_source_range NavigationSmoke NavigationModel Obj
#guard_model_field_source_range NavigationSmoke NavigationModel J
#guard_model_field_source_range NavigationSmoke NavigationModel base
#guard_model_field_source_range NavigationSmoke NavigationModel intro
#guard_model_field_source_range NavigationSmoke NavigationModel extBase

#check NavigationSmoke.NavigationModel
