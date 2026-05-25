/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Documentation capture and lint tests

These tests exercise UX-3 docstring capture, generated hover docs, and documentation lints.
-/

@[expose] public section

open Lean

/-- Documented theory used by the docs linter smoke test. -/
declare_type_theory DocSmoke where
  /-- Objects in the documented smoke theory. -/
  syntax_sort Obj
  /-- Distinguished documented object. -/
  lf_opaque point : Obj
  /-- Reflexive relation on the distinguished object. -/
  judgment Rel (x : Obj)
  /-- A documented relation witness rule. -/
  rule rel_point : Rel point
  /-- Documented LF object definition inside the declaration block. -/
  lf_def pointAlias : Obj := point
  /-- Documented LF judgment theorem inside the declaration block. -/
  judgment_theorem pointAliasRel : Rel pointAlias := rel_point

namespace DocSmoke

/-- Relation witness for the documented point. -/
internal def pointRel : Rel point := rel_point

end DocSmoke

/-- info: type theory 'DocSmoke' documentation lint passed: 8 documented public item(s) -/
#guard_msgs (whitespace := lax) in
#lint_type_theory_docs DocSmoke

#eval show CoreM Unit from do
  let some theoryDoc ← findDocString? (← getEnv) `DocSmoke.theory
    | throwError "missing theory anchor docstring"
  unless theoryDoc.contains "Documented theory used by the docs linter smoke test." do
    throwError "theory anchor docstring did not include source documentation: {theoryDoc}"
  let some internalDoc ← findDocString? (← getEnv) `DocSmoke.pointRel
    | throwError "missing internal declaration anchor docstring"
  unless internalDoc.contains "Relation witness for the documented point." do
    throwError "internal declaration anchor docstring did not include source documentation: \
      {internalDoc}"

/- An intentionally underdocumented theory for snapshot-style lint output. -/
declare_type_theory DocUnder where
  syntax_sort A
  lf_opaque a : A

/-- warning: type theory 'DocUnder' is missing docs for 3 public item(s):
missing doc: theory DocUnder, generated anchor DocUnder.theory
missing doc: syntax sort A
missing doc: LF opaque constant a -/
#guard_msgs (whitespace := lax) in
#lint_type_theory_docs DocUnder

/-- LF metadata theory with source docs for generated model-field hovers. -/
declare_type_theory DocLF where
  /-- Objects in the documented LF smoke theory. -/
  syntax_sort Obj
  /-- A documented unary relation. -/
  judgment Rel (x : Obj)
  /-- Distinguished documented object. -/
  lf_opaque point : Obj
  /-- A documented relation witness rule. -/
  rule rel_point : Rel point

generate_lf_model_structure DocLF as DocModel

#eval show CoreM Unit from do
  let some fieldDoc ← findDocString? (← getEnv) `DocLF.DocModel.Obj
    | throwError "missing generated LF model field docstring"
  unless fieldDoc.contains "Source declaration: syntax_sort Obj." do
    throwError "generated LF model field docstring missed source role: {fieldDoc}"
  unless fieldDoc.contains "Objects in the documented LF smoke theory." do
    throwError "generated LF model field docstring missed source doc: {fieldDoc}"
