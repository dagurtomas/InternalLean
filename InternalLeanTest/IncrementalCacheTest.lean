/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command
public import InternalLeanTest.IncrementalCacheFixture

/-!
# Incremental checker-cache tests

These tests cover the derived compiled LF checking cache used by standalone checked internal
LF definitions and judgment theorems.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

/-- Assert that an internal registration profile used the compiled checker cache. -/
elab "#guard_internal_profile_cache " theory:ident decl:ident status:str replay:ident :
    command => do
  let profiles ← liftCoreM <| getInternalRegistrationProfilesFor theory.getId
  let declName := decl.getId.eraseMacroScopes
  let some profile := profiles.find? (fun p => p.declName.eraseMacroScopes == declName)
    | throwError "no registration profile for '{theory.getId}.{declName}'"
  unless profile.cacheStatus? == some status.getString do
    throwError "expected cache status {status.getString} for '{theory.getId}.{declName}', found \
      {profile.cacheStatus?}"
  unless profile.cacheOverlayDecls == 1 do
    throwError "expected one cache overlay declaration for '{theory.getId}.{declName}', found \
      {profile.cacheOverlayDecls}"
  let expectedReplay := replay.getId.eraseMacroScopes == `true
  unless profile.kernelReplayCacheHit == expectedReplay do
    throwError "expected kernel replay cache hit {expectedReplay} for \
      '{theory.getId}.{declName}', found {profile.kernelReplayCacheHit}"

/-- Assert cache status and overlay count for a registration profile. -/
elab "#guard_internal_profile_cache_overlay " theory:ident decl:str status:str replay:ident
    overlay:num : command => do
  let profiles ← liftCoreM <| getInternalRegistrationProfilesFor theory.getId
  let declName := Name.mkSimple decl.getString
  let some profile := profiles.find? (fun p => p.declName.eraseMacroScopes == declName)
    | throwError "no registration profile for '{theory.getId}.{declName}'"
  unless profile.cacheStatus? == some status.getString do
    throwError "expected cache status {status.getString} for '{theory.getId}.{declName}', found \
      {profile.cacheStatus?}"
  unless profile.cacheOverlayDecls == overlay.getNat do
    throwError "expected {overlay.getNat} cache overlay declaration(s) for \
      '{theory.getId}.{declName}', found {profile.cacheOverlayDecls}"
  let expectedReplay := replay.getId.eraseMacroScopes == `true
  unless profile.kernelReplayCacheHit == expectedReplay do
    throwError "expected kernel replay cache hit {expectedReplay} for \
      '{theory.getId}.{declName}', found {profile.kernelReplayCacheHit}"

/-- Assert local cache updates are persisted by small touch markers, not full cache snapshots. -/
elab "#guard_no_local_full_compiled_cache_entries" : command => do
  let entries := compiledLFCheckCacheExt.getEntries (← getEnv)
  let fullCount := entries.foldl (init := 0) fun count entry =>
    match entry with
    | .cache _ _ => count + 1
    | .touch _ => count
  unless fullCount == 0 do
    throwError "expected no local full compiled-cache entries, found {fullCount}"

/-- Poison a cache stamp and assert lookup rebuilds instead of using the stale cache. -/
elab "#guard_compiled_cache_mismatch_rebuild " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let lookup ← liftCoreM <| getOrBuildCompiledLFCheckCache theory.getId checked
  let staleStamp := {
    lookup.cache.stamp with
    objectDefCount := lookup.cache.stamp.objectDefCount + 1 }
  liftCoreM <| setCompiledLFCheckCache theory.getId { lookup.cache with stamp := staleStamp }
  let rebuilt ← liftCoreM <| getOrBuildCompiledLFCheckCache theory.getId checked
  unless rebuilt.rebuilt && rebuilt.status == "stale-rebuilt" do
    throwError "expected stale compiled cache for '{theory.getId}' to be rebuilt, got \
      status={rebuilt.status}, rebuilt={rebuilt.rebuilt}"
  let expected := CompiledLFCheckCacheStamp.ofCheckedSignature checked
  unless rebuilt.cache.stamp == expected do
    throwError "rebuilt compiled cache for '{theory.getId}' has an unexpected stamp"

/-- Assert that an append-updated compiled cache has the same shape as a full rebuild. -/
elab "#guard_compiled_cache_matches_rebuild " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let some cache ← liftCoreM <| getCompiledLFCheckCache? theory.getId
    | throwError "no compiled cache stored for type theory '{theory.getId}'"
  let rebuilt ← liftCoreM <| mkCompiledLFCheckCache theory.getId checked
  unless cache.stamp == rebuilt.stamp do
    throwError "compiled cache stamp for '{theory.getId}' differs from a full rebuild"
  unless checkedHLSignatureMatchesChecked cache.checkedHL checked do
    throwError "compiled cache checked-HL signature for '{theory.getId}' does not match"
  unless cache.structuralKernelSig.constants.length ==
      rebuilt.structuralKernelSig.constants.length do
    throwError "compiled cache constants for '{theory.getId}' differ from a full rebuild"
  unless cache.structuralKernelSig.rules.length == rebuilt.structuralKernelSig.rules.length do
    throwError "compiled cache rules for '{theory.getId}' differ from a full rebuild"
  unless cache.structuralKernelSig.contextZones.length ==
      rebuilt.structuralKernelSig.contextZones.length do
    throwError "compiled cache context zones for '{theory.getId}' differ from a full rebuild"
  unless cache.structuralKernelSig.binderClasses.length ==
      rebuilt.structuralKernelSig.binderClasses.length do
    throwError "compiled cache binder classes for '{theory.getId}' differ from a full rebuild"
  unless cache.structuralKernelSig.conversionPlugins.length ==
      rebuilt.structuralKernelSig.conversionPlugins.length do
    throwError "compiled cache conversion plugins for '{theory.getId}' differ from a full rebuild"
  unless cache.structuralKernelSig == rebuilt.structuralKernelSig do
    throwError "compiled cache kernel signature for '{theory.getId}' differs from a full rebuild"

declare_type_theory IncrementalCacheSmoke where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

namespace IncrementalCacheSmoke

internal def cachedObj : Obj := base
internal theorem cachedThm1 : J base := intro base
internal theorem cachedThm2 : J base := cachedThm1
internal theorem local_id (x : Obj) (h : J x) : J x := h
internal theorem use_local_id : J base := local_id base (intro base)

end IncrementalCacheSmoke

#guard_internal_profile_cache IncrementalCacheSmoke cachedObj "hit" false
#guard_internal_profile_cache IncrementalCacheSmoke cachedThm1 "hit" true
#guard_internal_profile_cache IncrementalCacheSmoke cachedThm2 "hit" true
#guard_internal_profile_cache IncrementalCacheSmoke local_id "hit" true
#guard_internal_profile_cache IncrementalCacheSmoke use_local_id "hit" true
#guard_compiled_cache_mismatch_rebuild IncrementalCacheSmoke
#guard_no_local_full_compiled_cache_entries

namespace ImportedCacheBase

internal theorem imported_again : J base := imported

end ImportedCacheBase

#guard_internal_profile_cache ImportedCacheBase imported_again "hit" true

declare_type_theory IncrementalCacheExtensionDelta where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj

extend_type_theory IncrementalCacheExtensionDelta where
  lf_opaque extra : Obj
  lf_def alias : Obj := extra
  rule introExtra : J extra
  rule introAlias : J alias
  judgment_theorem ext_id (x : Obj) (h : J x) : J x := h
  judgment_theorem ext_alias : J alias := introAlias

#guard_compiled_cache_matches_rebuild IncrementalCacheExtensionDelta

namespace IncrementalCacheExtensionDelta

internal def alias_copy : Obj := alias
internal theorem use_ext_rule : J alias := introAlias
internal theorem use_ext_theorem_schema : J alias := ext_id alias ext_alias

end IncrementalCacheExtensionDelta

#guard_internal_profile_cache IncrementalCacheExtensionDelta alias_copy "hit" false
#guard_internal_profile_cache IncrementalCacheExtensionDelta use_ext_rule "hit" true
#guard_internal_profile_cache IncrementalCacheExtensionDelta use_ext_theorem_schema "hit" true
#guard_compiled_cache_matches_rebuild IncrementalCacheExtensionDelta

declare_type_theory IncrementalCacheExtensionOrder where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  lf_opaque extra : Obj
  rule introBase : J base
  judgment_theorem base_ok : J base := introBase

extend_type_theory IncrementalCacheExtensionOrder where
  rule introExtra : J extra

#guard_compiled_cache_matches_rebuild IncrementalCacheExtensionOrder

namespace IncrementalCacheExtensionOrder

internal theorem use_later_rule : J extra := introExtra

end IncrementalCacheExtensionOrder

#guard_internal_profile_cache IncrementalCacheExtensionOrder use_later_rule "hit" true
#guard_compiled_cache_matches_rebuild IncrementalCacheExtensionOrder

declare_type_theory IncrementalCacheAdmittedOpaqueBatch where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

namespace IncrementalCacheAdmittedOpaqueBatch

#guard_msgs (drop warning) in
internal def admittedSingle : Obj := sorry

#guard_msgs (drop warning) in
internal_defs where
  def admittedBatch1 : Obj := sorry
  def admittedBatch2 : Obj := sorry

internal theorem use_admitted_single : J admittedSingle := intro admittedSingle
internal theorem use_admitted_batch : J admittedBatch2 := intro admittedBatch2

end IncrementalCacheAdmittedOpaqueBatch

#guard_internal_profile_cache IncrementalCacheAdmittedOpaqueBatch admittedSingle "hit" false
#guard_internal_profile_cache_overlay IncrementalCacheAdmittedOpaqueBatch "internal_defs" "hit"
  false 2
#guard_internal_profile_cache IncrementalCacheAdmittedOpaqueBatch use_admitted_single "hit" true
#guard_internal_profile_cache IncrementalCacheAdmittedOpaqueBatch use_admitted_batch "hit" true
#guard_compiled_cache_matches_rebuild IncrementalCacheAdmittedOpaqueBatch

declare_type_theory IncrementalCacheSelfReferenceReject where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

namespace IncrementalCacheSelfReferenceReject

/--
error: Unknown identifier `self_ref`
-/
#guard_msgs (whitespace := lax) in
internal theorem self_ref : J base := self_ref

end IncrementalCacheSelfReferenceReject
