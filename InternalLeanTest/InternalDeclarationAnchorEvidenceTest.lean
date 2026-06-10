/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Evidence-indexed InternalLean anchor tests

These tests check that generated Lean-visible anchors depend on declaration-specific evidence
constants rather than on nullary marker values.
-/

@[expose] public section

open Lean
open InternalLean

declare_type_theory AnchorEvidenceSmoke where
  syntax_sort Obj
  lf_opaque o : Obj
  judgment IsObj (x : Obj)
  rule mkObj (x : Obj) : IsObj x

namespace AnchorEvidenceSmoke

internal def obj : Obj := o
internal theorem obj_ok : IsObj o := mkObj o

/--
warning: internal declaration 'AnchorEvidenceSmoke.admittedObj' was admitted by `sorry`; the
annotation was checked in theory 'AnchorEvidenceSmoke', but the body was not checked. Use
`#lint_type_theory_sorries AnchorEvidenceSmoke` to list current admissions.
-/
#guard_msgs (whitespace := lax) in
internal def admittedObj : Obj := sorry

#check _internalLeanEvidence.obj
#check _internalLeanEvidence.obj_ok
#check _internalLeanEvidence.admittedObj
#check obj
#check obj_ok
#check admittedObj

run_cmd do
  let env ← getEnv
  let checkAnchor (anchorName localName : Name) (kind : InternalDeclarationEvidenceKind) := do
    let evidenceName := internalDeclarationEvidenceName `AnchorEvidenceSmoke localName
    unless env.contains evidenceName do
      throwError "missing evidence declaration {evidenceName}"
    let some record ← Lean.Elab.Command.liftCoreM <|
        findInternalDeclarationEvidenceByAnchor? anchorName
      | throwError "missing evidence registry record for {anchorName}"
    unless record.evidenceName == evidenceName.eraseMacroScopes do
      throwError "evidence record for {anchorName} points at {record.evidenceName}, expected \
        {evidenceName}"
    unless record.kind == kind do
      throwError "evidence record for {anchorName} has kind {record.kind.label}, expected \
        {kind.label}"
    let some info := env.find? anchorName
      | throwError "missing anchor declaration {anchorName}"
    unless info.type.isAppOf ``InternalDeclarationAnchor do
      throwError "anchor {anchorName} has unexpected type {info.type}"
    let args := info.type.getAppArgs
    unless args.size == 4 && args[3]! == mkConst evidenceName do
      throwError "anchor {anchorName} is not indexed by evidence {evidenceName}; type was \
        {info.type}"
  checkAnchor `AnchorEvidenceSmoke.obj `obj .checkedObjectDef
  checkAnchor `AnchorEvidenceSmoke.obj_ok `obj_ok .checkedJudgmentTheorem
  checkAnchor `AnchorEvidenceSmoke.admittedObj `admittedObj .admittedLFOpaque

#print_internal_declaration_anchor AnchorEvidenceSmoke.obj

/--
info: InternalLean.InternalDeclarationAnchor.mk {theoryName localName : Name} {kind :
  InternalDeclarationEvidenceKind}
  (ev : InternalDeclarationEvidence theoryName localName kind) : InternalDeclarationAnchor ev
-/
#guard_msgs (whitespace := lax) in
#check InternalLean.InternalDeclarationAnchor.mk

end AnchorEvidenceSmoke
