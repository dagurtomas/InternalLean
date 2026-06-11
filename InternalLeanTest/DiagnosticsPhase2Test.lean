/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Phase 2 diagnostics regressions
-/

@[expose] public section

open Lean Elab Command InternalLean

declare_type_theory Phase2HoleSmoke where
  syntax_sort Obj
  syntax_sort Hom (x : Obj) (y : Obj)
  lf_opaque o : Obj
  lf_opaque idm (x : Obj) : Hom x x

namespace Phase2HoleSmoke

internal def inferredUnderscore : Hom o o := idm _

/--
error: direct internal term `idm ...` supplied 2 argument(s)/hole(s), but rule or declaration
'idm' has only 1 explicit argument slot(s).

Omitted explicit arguments are not inferred as subgoals. `_` is infer-only; provide complete
argument terms when the expected type does not determine them.

Expected internal type:
  Hom o o
-/
#guard_msgs (whitespace := lax) in
internal def tooManyArgs : Hom o o := idm _ _

end Phase2HoleSmoke

/--
error: LF opaque constant declaration 'fst' uses reserved name 'fst', which is reserved by
InternalLean syntax. Reserved LF names: fst, snd, Type
-/
#guard_msgs (whitespace := lax) in
declare_type_theory Phase2FailedTheory where
  syntax_sort Obj
  lf_opaque «fst» : Obj

/--
error: type theory 'Phase2FailedTheory' failed to declare (see the earlier error at line 48,
column 20)
-/
#guard_msgs (whitespace := lax) in
#check_type_theory Phase2FailedTheory

/--
error: type theory 'Phase2FailedTheory' failed to declare (see the earlier error at line 48,
column 20)
-/
#guard_msgs (whitespace := lax) in
#check_theory Phase2FailedTheory

/--
error: type theory 'Phase2FailedTheory' failed to declare (see the earlier error at line 48,
column 20)
-/
#guard_msgs (whitespace := lax) in
internal def Phase2FailedTheory.a : Obj := o

declare_type_theory Phase2BinderPremiseInline where
  syntax_sort Obj
  lf_opaque o : Obj
  lf_opaque comp (f : Obj) (g : Obj) : Obj
  judgment Good (x : Obj)
  rule good_o : Good o
  rule good_comp (f : Obj) (g : Obj) (hf : Good f) (hg : Good g) : Good (comp f g)

declare_type_theory Phase2BinderPremiseWhere where
  syntax_sort Obj
  lf_opaque o : Obj
  lf_opaque comp (f : Obj) (g : Obj) : Obj
  judgment Good (x : Obj)
  rule good_o : Good o
  rule good_comp (f : Obj) (g : Obj) where
    premise hf : Good f
    premise hg : Good g
    conclusion : Good (comp f g)

run_cmd do
  let some inline ← liftCoreM <| getCheckedHLSignature? `Phase2BinderPremiseInline
    | throwError "missing checked signature for inline premise smoke"
  let some whereForm ← liftCoreM <| getCheckedHLSignature? `Phase2BinderPremiseWhere
    | throwError "missing checked signature for where-premise smoke"
  let some inlineRule := inline.rules.find? (fun r => r.name == `good_comp)
    | throwError "missing inline good_comp rule"
  let some whereRule := whereForm.rules.find? (fun r => r.name == `good_comp)
    | throwError "missing where good_comp rule"
  unless inlineRule.params.map (fun b => b.name.eraseMacroScopes) ==
      whereRule.params.map (fun b => b.name.eraseMacroScopes) do
    throwError "inline binder-premise rule kept different parameters"
  unless inlineRule.premises.map (fun p => p.name.eraseMacroScopes) == #[`hf, `hg] do
    throwError "inline binder-premise rule did not preserve premise names"
  unless inlineRule.premises == whereRule.premises do
    throwError "inline binder-premise rule did not match where-premise rule"

namespace Phase2BinderPremiseInline

internal theorem inlineGood : Good (comp o o) := good_comp o o good_o good_o

end Phase2BinderPremiseInline

/--
error: rule 'bad' has judgment-headed binder premise(s) followed by non-premise binder 'x'.
Binder-style premises must be trailing; move interleaved premises to the `where premise` form.
-/
#guard_msgs (whitespace := lax) in
declare_type_theory Phase2BinderPremiseInterleaved where
  syntax_sort Obj
  lf_opaque o : Obj
  judgment Good (x : Obj)
  rule bad (hf : Good o) (x : Obj) : Good x

/--
info: local theorem assumption 'h' has statement 'Good o', expected 'Good p'
-/
#guard_msgs (whitespace := lax) in
run_cmd do
  let stmt : Judgment := .custom `Good [.tmConst `o]
  let expected : Judgment := .custom `Good [.tmConst `p]
  let sig : Signature := { name := `KernelMessageSmoke }
  match KernelLFDerivation.checkWithContext {} sig (.assumption `h stmt) expected with
  | .ok () => throwError "unexpected kernel replay success"
  | .error err => logInfo m!"{err}"

declare_type_theory Phase2SinglePathSmoke where
  syntax_sort Obj
  lf_opaque o : Obj
  judgment Good (x : Obj)
  rule good_o : Good o

namespace Phase2SinglePathSmoke

/--
error: failed to check internal LF declaration 'Phase2SinglePathSmoke.badObj' in type theory
'Phase2SinglePathSmoke' as an LF object definition:
unknown identifier 'missing' in value of lf_def 'badObj' in type theory 'Phase2SinglePathSmoke'
-/
#guard_msgs (whitespace := lax) in
internal def badObj : Obj := missing

/--
error: failed to check internal LF declaration 'Phase2SinglePathSmoke.badThm' in type theory
'Phase2SinglePathSmoke' as an LF judgment theorem:
unknown identifier 'missing' in proof of judgment_theorem 'badThm' in type theory
'Phase2SinglePathSmoke'
-/
#guard_msgs (whitespace := lax) in
internal def badThm : Good o := missing

end Phase2SinglePathSmoke

/--
error: LF opaque constant declaration 'fst' uses reserved name 'fst', which is reserved by
InternalLean syntax. Reserved LF names: fst, snd, Type
-/
#guard_msgs (whitespace := lax) in
set_option internalLean.requireLeanQuotedTheoryBlocks true in
declare_type_theory Phase2StrictQuotedFailedTheory where
  syntax_sort Obj
  lf_opaque «fst» : Obj

/--
error: type theory 'Phase2StrictQuotedFailedTheory' failed to declare (see the earlier error at
line 171, column 20)
-/
#guard_msgs (whitespace := lax) in
#check_theory Phase2StrictQuotedFailedTheory

/--
error: type theory 'Phase2StrictQuotedFailedTheory' failed to declare (see the earlier error at
line 171, column 20)
-/
#guard_msgs (whitespace := lax) in
internal def Phase2StrictQuotedFailedTheory.a : Obj := o
