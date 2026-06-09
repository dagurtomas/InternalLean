/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Lean-elaborated quoted LF frontend tests

These tests cover the experimental `internal_lean def` frontend.  Lean elaborates the term body
against generated `T.LFQuote` stubs; InternalLean reflects the elaborated expression back to LF and
then runs the ordinary LF checker.
-/

@[expose] public section

open InternalLean

declare_type_theory LeanQuotedFrontendSmoke where
  syntax_sort Obj : Type
  lf_opaque o : Obj
  lf_opaque id (x : Obj) : Obj
  judgment IsObj (x : Obj)
  rule mkObj (x : Obj) : IsObj x

#check LeanQuotedFrontendSmoke.LFQuote.Obj
#check LeanQuotedFrontendSmoke.LFQuote.o
#check LeanQuotedFrontendSmoke.LFQuote.id
#check LeanQuotedFrontendSmoke.LFQuote.mkObj

/--
info: quoted LF stubs for LeanQuotedFrontendSmoke:
syntax_sort Obj -> LeanQuotedFrontendSmoke.LFQuote.Obj / 0 parameter(s)
judgment IsObj -> LeanQuotedFrontendSmoke.LFQuote.IsObj / 1 parameter(s)
rule mkObj -> LeanQuotedFrontendSmoke.LFQuote.mkObj / 1 parameter(s)
lf_opaque o -> LeanQuotedFrontendSmoke.LFQuote.o / 0 parameter(s)
lf_opaque id -> LeanQuotedFrontendSmoke.LFQuote.id / 1 parameter(s)
-/
#guard_msgs (whitespace := lax) in
#print_lf_quote_stubs LeanQuotedFrontendSmoke

namespace LeanQuotedFrontendSmoke

internal_lean def d : Obj := o
internal_lean def e : Obj := LFQuote.id o
internal_lean def f (x : Obj) : Obj := LFQuote.id x
internal_lean def dAlias : Obj := LFQuote.d
internal_lean def idObj : Obj → Obj := fun x => x
internal_lean def applyLocal (g : Obj → Obj) (x : Obj) : Obj := g x
internal_lean def o_ok : IsObj o := LFQuote.mkObj o

#check d
#check e
#check f
#check dAlias
#check idObj
#check applyLocal
#check o_ok

end LeanQuotedFrontendSmoke

namespace LeanQuotedFrontendSmoke

/--
error: Lean-elaborated LF term uses non-LF constant 'InternalLean.LFQuoteTerm.mk'. Only generated
stubs in namespace 'LeanQuotedFrontendSmoke.LFQuote' are accepted by this prototype.
-/
#guard_msgs (whitespace := lax) in
internal_lean def bad : Obj := InternalLean.LFQuoteTerm.mk

end LeanQuotedFrontendSmoke
