/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Lean-quoted frontend fallback profile tests
-/

@[expose] public section

open InternalLean

set_option internalLean.preferLeanQuotedTheoryBlocks true in
declare_type_theory FrontendFallbackProfileSmoke where
  syntax_sort Obj
  syntax_sort El (A : Obj)
  lf_opaque A : Obj
  lf_opaque a : El A
  lf_opaque id {A : Obj} (x : El A) : El A
  lf_def legacyNamedImplicit : El A := id {A := A} a

declare_type_theory FrontendFallbackCanonicalSmoke where
  syntax_sort Obj
  syntax_sort El (A : Obj)
  lf_opaque A : Obj
  lf_opaque a : El A
  lf_opaque idf {X : Obj} (x : El X) : El X

namespace FrontendFallbackCanonicalSmoke

internal def viaQuoted : El A := idf (X := A) a

end FrontendFallbackCanonicalSmoke

declare_type_theory FrontendFallbackCompareSmoke where
  syntax_sort Obj
  syntax_sort Hom (x : Obj) (y : Obj)
  lf_opaque o : Obj
  lf_opaque idm (x : Obj) : Hom x x
  lf_opaque comp {x : Obj} {y : Obj} {z : Obj}
    (f : Hom x y) (g : Hom y z) : Hom x z

namespace FrontendFallbackCompareSmoke

set_option internalLean.frontend.compareLegacy true in
internal def quotedOnly (f : Hom o o) : Hom o o := comp f (comp f f)

set_option internalLean.frontend.compareLegacy true in
internal def bothAgree : Hom o o := idm o

end FrontendFallbackCompareSmoke

/--
info: internal frontend fallback profile for current file:
  theoryObjExpr: 1
  compareLegacyInternalDef: 1
-/
#guard_msgs (whitespace := lax) in
#print_internal_frontend_fallback_profile
