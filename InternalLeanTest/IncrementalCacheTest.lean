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

namespace ImportedCacheBase

internal theorem imported_again : J base := imported

end ImportedCacheBase

#guard_internal_profile_cache ImportedCacheBase imported_again "hit" true

declare_type_theory IncrementalCacheSelfReferenceReject where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x

namespace IncrementalCacheSelfReferenceReject

/--
error: judgment_theorem 'self_ref' in type theory 'IncrementalCacheSelfReferenceReject' uses
premise theorem 'self_ref' before it is available
-/
#guard_msgs (whitespace := lax) in
internal theorem self_ref : J base := self_ref

end IncrementalCacheSelfReferenceReject
