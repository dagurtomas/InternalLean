/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.Registration
public meta import InternalLean.LeanFrontend.MirrorCore

/-!
# Mirror-backed InternalLean goal display

This module builds editor-only Lean goal snapshots for InternalLean object goals.  The generated
metavariables live in an isolated metavariable context stored in `TacticInfo`; they are
`syntheticOpaque` and the elaborator state is restored before returning them, so they cannot be
assigned by later elaboration or by the object-tactic compiler.
-/

@[expose] public meta section

open Lean Elab Command Term Meta
open Lean.PrettyPrinter.Delaborator

namespace InternalLean

register_option internalLean.goalDisplay.logFallbacks : Bool := {
  defValue := false
  descr := "log warnings when mirror-backed InternalLean goal display falls back to the legacy \
    string-marker goal view"
}

/-- Proposition used as a display-only local when quoted-`by` goal simulation becomes stale. -/
public inductive InternalGoalDisplayStaleNote : Prop where
  /-- Marker constructor; display-only metavariables are never solved through this value. -/
  | marker : InternalGoalDisplayStaleNote

syntax (name := internalGoalDisplayStaleNotePretty) "goal_display_may_be_stale" : term

macro_rules
  | `(goal_display_may_be_stale) => `(InternalLean.InternalGoalDisplayStaleNote)

/-- Delaborate the stale-display note as readable editor text. -/
@[app_delab InternalGoalDisplayStaleNote] def delabInternalGoalDisplayStaleNote : Delab := do
  `(goal_display_may_be_stale)

/-- One recorded fallback from the mirror goal renderer to the legacy string marker. -/
structure InternalGoalDisplayFallbackEntry where
  /-- Source file that recorded this entry. -/
  fileName : String := ""
  /-- Stable fallback class. -/
  kind : Name
  /-- Human-readable source position when available. -/
  position? : Option String := none
  /-- Exception or skip message recorded at the fallback boundary. -/
  message : String := ""
  deriving Inhabited, Repr, BEq

/-- Fallback profile state that survives command-elaborator fallthrough and state restoration. -/
initialize internalGoalDisplayFallbackStore : IO.Ref (Array InternalGoalDisplayFallbackEntry) ←
  IO.mkRef #[]

/-- Render a source position for a goal-display fallback diagnostic. -/
def goalDisplayFallbackPositionString? (stx : Syntax) : CommandElabM (Option String) := do
  match stx.getPos? (canonicalOnly := true) with
  | none => pure none
  | some pos =>
      let p := (← getFileMap).toPosition pos
      pure <| some s!"line {p.line}, column {p.column}"

/-- Whether mirror-goal-display fallback warnings are enabled. -/
def logInternalGoalDisplayFallbacks : CommandElabM Bool :=
  getBoolOption `internalLean.goalDisplay.logFallbacks

/-- A fallback found while constructing one display snapshot. -/
structure InternalGoalDisplayFallback where
  /-- Stable fallback class. -/
  kind : Name
  /-- Human-readable reason. -/
  message : MessageData

/-- Record fallback events emitted while constructing a display snapshot. -/
def recordInternalGoalDisplayFallbacks (stx : Syntax)
    (fallbacks : Array InternalGoalDisplayFallback) : CommandElabM Unit := do
  if fallbacks.isEmpty then
    return
  let fileName ← getFileName
  let position? ← goalDisplayFallbackPositionString? stx
  for fallback in fallbacks do
    let text ← fallback.message.toString
    liftIO <| internalGoalDisplayFallbackStore.modify fun entries => entries.push {
      fileName := fileName
      kind := fallback.kind.eraseMacroScopes
      position?
      message := text }
    if ← logInternalGoalDisplayFallbacks then
      let positionText := position?.getD "at unknown position"
      withRef stx <| logWarning m!"InternalLean goal display fallback \
        [{fallback.kind.eraseMacroScopes}] {positionText}: {fallback.message}"

/-- Remove duplicate fallback entries, useful across editor re-elaborations. -/
def dedupeInternalGoalDisplayFallbackEntries (entries : Array InternalGoalDisplayFallbackEntry) :
    Array InternalGoalDisplayFallbackEntry := Id.run do
  let mut out := #[]
  for entry in entries do
    unless out.contains entry do
      out := out.push entry
  return out

/-- Read goal-display fallback entries recorded for the current source file. -/
def currentFileInternalGoalDisplayFallbackEntries : CommandElabM
    (Array InternalGoalDisplayFallbackEntry) := do
  let fileName ← getFileName
  let entries ← liftIO internalGoalDisplayFallbackStore.get
  pure <| dedupeInternalGoalDisplayFallbackEntries <|
    entries.filter fun entry => entry.fileName == fileName

/-- Summarize current-file goal-display fallback counters. -/
def internalGoalDisplayFallbackProfileString (entries : Array InternalGoalDisplayFallbackEntry) :
    String := Id.run do
  let mut kinds : Array Name := #[]
  let mut counts : NameMap Nat := {}
  for entry in entries do
    let kind := entry.kind.eraseMacroScopes
    if (counts.find? kind).isNone then
      kinds := kinds.push kind
    counts := counts.insert kind ((counts.find? kind).getD 0 + 1)
  let mut lines := #["internal goal-display fallback profile for current file:"]
  if kinds.isEmpty then
    lines := lines.push "  no fallbacks"
  else
    for kind in kinds do
      lines := lines.push s!"  {kind}: {(counts.find? kind).getD 0}"
  String.intercalate "\n" lines.toList

/-- Print the current file's mirror-goal-display fallback counters. -/
elab "#print_internal_goal_display_fallback_profile" : command => do
  let profile := internalGoalDisplayFallbackProfileString
    (← currentFileInternalGoalDisplayFallbackEntries)
  logInfo m!"{profile}"

/-- Render the local object context shown by tactic errors and fallback goal markers. -/
def renderInternalObjectContext (ctx : Array HLBinding) : String :=
  if ctx.isEmpty then
    "  (empty object context)"
  else
    String.intercalate "\n" <| ctx.toList.map fun b =>
      s!"  {b.name.eraseMacroScopes} : {diagnosticObjExprString b.typeExpr}"

/-- Lean proposition type used by the legacy string-marker infoview fallback. -/
def internalObjectGoalViewType (target : InternalDefTarget) (ctx : Array HLBinding)
    (goalTarget : ObjExpr) : Expr :=
  mkApp3 (mkConst ``InternalObjectGoalView)
    (mkStrLit target.theoryName.eraseMacroScopes.toString)
    (mkStrLit (renderInternalObjectContext ctx))
    (mkStrLit (toString goalTarget))

/-- One display goal requested by an infoview producer. -/
structure InternalGoalDisplayGoal where
  /-- Object-theory local context. -/
  ctx : Array HLBinding := #[]
  /-- Object-theory target. -/
  target : ObjExpr
  /-- Whether this goal state is a stale best-effort simulation snapshot. -/
  stale : Bool := false

/-- Prepared mirror-display context.  `mirrorError?` being present means every goal should use the
legacy marker fallback; otherwise the renderer can translate individual goals through the mirror. -/
structure InternalGoalDisplayContext where
  /-- Owning object theory. -/
  theoryName : Name
  /-- Universe arguments for generated mirror constants. -/
  levelArgs : List Level := []
  /-- Error that prevented mirror construction for the whole theory, if any. -/
  mirrorError? : Option MessageData := none

/-- The display metavariables and their isolated context for one `TacticInfo` snapshot. -/
structure InternalGoalDisplaySnapshot where
  /-- Isolated metavariable context containing the display goals created for this snapshot. -/
  mctx : MetavarContext
  /-- Display goal metavariable ids, stored in the accompanying `mctx`. -/
  goals : List MVarId
  /-- Fallbacks used while producing the snapshot. -/
  fallbacks : Array InternalGoalDisplayFallback := #[]

/-- Ensure the mirror exists once for a group of goal snapshots. -/
def prepareInternalGoalDisplayContext (target : InternalDefTarget) : TermElabM
    InternalGoalDisplayContext := do
  let theoryName := target.theoryName
  try
    ensureLFMirrorForTheory theoryName
    let levelArgs ← lfMirrorLevelArgsForTheory theoryName
    pure { theoryName, levelArgs }
  catch ex =>
    pure { theoryName, mirrorError? := some ex.toMessageData }

/-- Add the stale-simulation note to a display goal's local context when requested. -/
def withInternalGoalDisplayStaleNote (stale : Bool) (k : MetaM α) : MetaM α := do
  if stale then
    withLocalDecl `note .default (mkConst ``InternalGoalDisplayStaleNote) fun _ => k
  else
    k

/-- Create one display-only metavariable with a mirror-translated target. -/
def mkMirrorInternalGoalMVar (displayCtx : InternalGoalDisplayContext)
    (goal : InternalGoalDisplayGoal) : TermElabM MVarId := do
  withLFMirrorLocalsWithLevels displayCtx.theoryName displayCtx.levelArgs goal.ctx fun locals => do
    let targetType ← lfMirrorExprWithLevels displayCtx.theoryName displayCtx.levelArgs locals
      goal.target
    withInternalGoalDisplayStaleNote goal.stale do
      let mvar ← Meta.mkFreshExprMVar (some targetType) .syntheticOpaque `object
      pure mvar.mvarId!

/-- Create one display-only metavariable using the legacy string-marker target. -/
def mkFallbackInternalGoalMVar (target : InternalDefTarget) (goal : InternalGoalDisplayGoal) :
    TermElabM MVarId := do
  let ctx :=
    if goal.stale then
      goal.ctx.push {
        name := `note
        typeExpr := .ident (.str .anonymous "goal_display_may_be_stale")
        visibility := .explicit }
    else
      goal.ctx
  let mvar ← Meta.mkFreshExprMVar (some (internalObjectGoalViewType target ctx goal.target))
    .syntheticOpaque `object
  pure mvar.mvarId!

/-- Create one live display metavariable with the same mirror/fallback policy as isolated
snapshots.  This is used by native tactic mode so Lean can attach ordinary `TacticInfo`; the
metavariable is still display-only and must not be trusted as LF evidence. -/
def mkLiveInternalGoalDisplayMVarWithContext (target : InternalDefTarget)
    (displayCtx : InternalGoalDisplayContext) (goal : InternalGoalDisplayGoal) :
    TermElabM (MVarId × Array InternalGoalDisplayFallback) := do
  match displayCtx.mirrorError? with
  | some message =>
      let mvarId ← mkFallbackInternalGoalMVar target goal
      pure (mvarId, #[{ kind := `mirrorUnavailable, message }])
  | none =>
      try
        let mvarId ← mkMirrorInternalGoalMVar displayCtx goal
        pure (mvarId, #[])
      catch ex =>
        let mvarId ← mkFallbackInternalGoalMVar target goal
        pure (mvarId, #[{ kind := `goalTranslation, message := ex.toMessageData }])

/-- Create display goals in an isolated metavariable context.  The returned metavariable ids are
valid only in the returned `mctx`; the surrounding elaboration state is restored before this
function returns. -/
def mkInternalObjectGoalDisplaySnapshotWithContext (target : InternalDefTarget)
    (displayCtx : InternalGoalDisplayContext) (goals : Array InternalGoalDisplayGoal) :
    TermElabM InternalGoalDisplaySnapshot :=
  withoutModifyingState do
    let mut goalIds : Array MVarId := #[]
    let mut fallbacks : Array InternalGoalDisplayFallback := #[]
    for goal in goals do
      match displayCtx.mirrorError? with
      | some message =>
          fallbacks := fallbacks.push { kind := `mirrorUnavailable, message }
          goalIds := goalIds.push (← mkFallbackInternalGoalMVar target goal)
      | none =>
          try
            goalIds := goalIds.push (← mkMirrorInternalGoalMVar displayCtx goal)
          catch ex =>
            fallbacks := fallbacks.push { kind := `goalTranslation, message := ex.toMessageData }
            goalIds := goalIds.push (← mkFallbackInternalGoalMVar target goal)
    let mctx ← getMCtx
    pure { mctx, goals := goalIds.toList, fallbacks }

/-- Prepare the theory mirror and create display goals in one call. -/
def mkInternalObjectGoalDisplaySnapshot (target : InternalDefTarget)
    (goals : Array InternalGoalDisplayGoal) : TermElabM InternalGoalDisplaySnapshot := do
  let displayCtx ← prepareInternalGoalDisplayContext target
  mkInternalObjectGoalDisplaySnapshotWithContext target displayCtx goals

/-- Construct a display-goal input from an object context and target. -/
def mkInternalGoalDisplayGoal (ctx : Array HLBinding) (target : ObjExpr)
    (stale : Bool := false) : InternalGoalDisplayGoal :=
  { ctx, target, stale }

/-- Split a Lean name into string components. -/
partial def nameStringComponents : Name → List String
  | .anonymous => []
  | .str p s => nameStringComponents p ++ [s]
  | .num p n => nameStringComponents p ++ [toString n]

/-- Build a Lean name from string components. -/
def nameOfStringComponents (components : List String) : Name :=
  components.foldl (fun n s => .str n s) .anonymous

/-- If a declaration name is under `T.LFMirror`, return `(T, sourceName)`. -/
def lfMirrorDeclNameView? (declName : Name) : Option (Name × Name) :=
  let rec go (prefixRev : List String) : List String → Option (Name × Name)
    | [] => none
    | "LFMirror" :: rest =>
        if prefixRev.isEmpty || rest.isEmpty then
          none
        else
          some (nameOfStringComponents prefixRev.reverse, nameOfStringComponents rest)
    | part :: rest => go (part :: prefixRev) rest
  go [] (nameStringComponents declName)

/-- Delaborate generated mirror constants without the `T.LFMirror` implementation prefix.

The returned syntax is annotated with the mirror expression.  Mirror declarations receive source
ranges copied from the InternalLean source anchor when generated, so editor navigation from this
compact rendering jumps to the object-theory declaration rather than to a generated stub. -/
@[delab app] def delabLFMirrorApplication : Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  let .const declName _ := e.getAppFn | failure
  let some (theoryName, sourceName) := lfMirrorDeclNameView? declName | failure
  guard <| declName == lfMirrorDeclName theoryName sourceName
  let head ← mkAnnotatedIdent sourceName.eraseMacroScopes e.getAppFn
  let headTerm : Term := ⟨head.raw⟩
  let mut args : TSyntaxArray `term := #[]
  for _h : i in [:e.getAppNumArgs] do
    args := args.push (← Lean.PrettyPrinter.Delaborator.SubExpr.withNaryArg i delab)
  pure <| Lean.Syntax.mkApp headTerm args

end InternalLean
