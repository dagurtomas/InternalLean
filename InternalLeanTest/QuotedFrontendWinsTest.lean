/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Lean-quoted frontend wins

These regressions lock in Lean-elaborated bodies that the legacy direct parser cannot express well
and trust-boundary checks around Lean `sorry`.
-/

@[expose] public section

open InternalLean

declare_type_theory QuotedFrontendWinsSmoke where
  syntax_sort Obj
  syntax_sort Hom (x : Obj) (y : Obj)
  lf_opaque o : Obj
  lf_opaque idm (x : Obj) : Hom x x
  lf_opaque comp {x : Obj} {y : Obj} {z : Obj}
    (f : Hom x y) (g : Hom y z) : Hom x z

namespace QuotedFrontendWinsSmoke

set_option internalLean.preferLeanQuotedFrontend true

internal def nestedImplicit (f : Hom o o) : Hom o o := comp f (comp f f)
internal def inferableUnderscore : Hom o o := idm _
internal def betaRedex (f : Hom o o) : Hom o o := (fun g => comp g g) f

/--
error: Lean-elaborated LF term uses Lean `sorry`. Lean `sorry` cannot become a checked internal
proof; use `:= sorry` for an explicit InternalLean admission.
-/
#guard_msgs (whitespace := lax) in
internal_lean def smuggledSorry : Obj := (sorry : _)

end QuotedFrontendWinsSmoke

/--
info: internal frontend fallback profile for current file:
  no fallbacks
-/
#guard_msgs (whitespace := lax) in
#print_internal_frontend_fallback_profile
