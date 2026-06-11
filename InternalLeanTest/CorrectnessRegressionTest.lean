/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Correctness regression tests

These tests keep recent performance/navigation refactors honest at the LF trust boundary.  They
cover intra-block availability, source-order registration paths, syntax-abbreviation batches, and
chunked model-interface generation.
-/

@[expose] public section

open InternalLean

/-- Object declarations cannot refer to later declarations in the same block. -/
declare_type_theory ObjectForwardRefBatchReject where
  syntax_sort Obj
  lf_opaque base : Obj

namespace ObjectForwardRefBatchReject

/--
error: Unknown identifier `d2`
-/
#guard_msgs (whitespace := lax) in
internal_defs where
  def d1 : Obj := d2
  def d2 : Obj := base

end ObjectForwardRefBatchReject

/-- Object declarations cannot refer to themselves in an internal_defs block. -/
declare_type_theory ObjectSelfRefBatchReject where
  syntax_sort Obj

namespace ObjectSelfRefBatchReject

/--
error: Unknown identifier `d`
-/
#guard_msgs (whitespace := lax) in
internal_defs where
  def d : Obj := d

end ObjectSelfRefBatchReject

/-- The theorem-shaped source-order path still rejects self-referential theorem proofs. -/
declare_type_theory TheoremSelfRefFallbackReject where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

namespace TheoremSelfRefFallbackReject

/--
error: Unknown identifier `t`
-/
#guard_msgs (whitespace := lax) in
internal_defs where
  def t : J base := t

end TheoremSelfRefFallbackReject

-- Bad syntax-sort arguments remain rejected after batch/refactor paths.
/--
error: lf_def 'bad' in type theory 'BadSyntaxSortArgumentRegression' has value whose type cannot
be inferred: 'Type', expected 'Obj'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadSyntaxSortArgumentRegression where
  syntax_sort Obj
  lf_def bad : Obj := Type

/-- Mixed object/theorem blocks still use sequential checking and register successfully. -/
declare_type_theory MixedInternalDefsFallbackSmoke where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

namespace MixedInternalDefsFallbackSmoke

internal_defs where
  def alias : Obj := base
  def alias_ok : J alias := intro alias

end MixedInternalDefsFallbackSmoke

#check MixedInternalDefsFallbackSmoke.alias
#check MixedInternalDefsFallbackSmoke.alias_ok

/-- Direct terms with placeholders still use checked placeholder elaboration. -/
declare_type_theory PlaceholderFallbackSmoke where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

namespace PlaceholderFallbackSmoke

internal_defs where
  def viaPlaceholder : J base := intro _

end PlaceholderFallbackSmoke

#check PlaceholderFallbackSmoke.viaPlaceholder

/-- Syntax-abbreviation uses in legacy raw checked object declarations remain accepted. -/
declare_type_theory SyntaxAbbrevBatchSmoke where
  syntax_sort Obj
  syntax_abbrev Endo := Obj → Obj
  lf_opaque idObj (x : Obj) : Obj

namespace SyntaxAbbrevBatchSmoke

internal_raw def idAlias : Endo := fun x => idObj x
internal_raw def idAliasAgain : Endo := fun x => idAlias x

end SyntaxAbbrevBatchSmoke

#check SyntaxAbbrevBatchSmoke.idAliasAgain

/-- Chunked model-interface generation remains accepted and exports late fields. -/
declare_type_theory ChunkedModelInterfaceSmoke where
  syntax_sort Obj
  lf_opaque c00 : Obj
  lf_opaque c01 : Obj
  lf_opaque c02 : Obj
  lf_opaque c03 : Obj
  lf_opaque c04 : Obj
  lf_opaque c05 : Obj
  lf_opaque c06 : Obj
  lf_opaque c07 : Obj
  lf_opaque c08 : Obj
  lf_opaque c09 : Obj
  lf_opaque c10 : Obj
  lf_opaque c11 : Obj
  lf_opaque c12 : Obj
  lf_opaque c13 : Obj
  lf_opaque c14 : Obj
  lf_opaque c15 : Obj
  lf_opaque c16 : Obj
  lf_opaque c17 : Obj
  lf_opaque c18 : Obj
  lf_opaque c19 : Obj
  lf_opaque c20 : Obj
  lf_opaque c21 : Obj
  lf_opaque c22 : Obj
  lf_opaque c23 : Obj
  lf_opaque c24 : Obj
  lf_opaque c25 : Obj
  lf_opaque c26 : Obj
  lf_opaque c27 : Obj
  lf_opaque c28 : Obj
  lf_opaque c29 : Obj
  lf_opaque c30 : Obj
  lf_opaque c31 : Obj
  lf_opaque c32 : Obj
  lf_opaque c33 : Obj
  lf_opaque c34 : Obj
  lf_opaque c35 : Obj
  lf_opaque c36 : Obj
  lf_opaque c37 : Obj
  lf_opaque c38 : Obj
  lf_opaque c39 : Obj
  lf_opaque c40 : Obj
  lf_opaque c41 : Obj
  lf_opaque c42 : Obj
  lf_opaque c43 : Obj
  lf_opaque c44 : Obj

generate_model_interface ChunkedModelInterfaceSmoke as ChunkedModel

#check ChunkedModelInterfaceSmoke.ChunkedModel
#check ChunkedModelInterfaceSmoke.ChunkedModel.c44
