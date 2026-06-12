# InternalLean theory mixin composition spec

Status: proposed, motivated by InternalMath MLTT modularization, 2026-06-11. Split into
reviewable phases M1–M3 on 2026-06-12 after a scoping review; the review's implementation
findings are recorded under "Current composition paths" below.

## Workflow

This spec runs under the same implement/review regime as
`Plans/InternalUniverseHierarchyEncodingSpec.md` and the archived refactor spec it imports by
reference:

- One agent implements, a second reviews. **Each phase below is a reviewable phase**: implement
  one phase, request review, do not start the next phase until the verdict is ACCEPTED. Findings
  are blocking (fix and re-review) or non-blocking (carry forward, recorded in the verdict).
- Before requesting review, run the per-phase handoff checklist: the full build
  (`lake build InternalLean.Command InternalLeanTest InternalLean Examples`), the compare-legacy
  variant while `internalLean.frontend.compareLegacy` exists,
  `scripts/check_lean_line_lengths.py --max 100`, `scripts/check_text_style.py`, and
  `git diff --check` — and write a work-log entry in `Plans/InternalLeanWorkLog.md` with an
  honest **Deviations** section. The review starts from that entry.
- Commits are prefixed `M<phase>:` (e.g. `M1: add parent DAG flattening`), mirroring the
  refactor's `P<N>:` and universe spec's `U<N>:` conventions.
- Review verdicts are appended to **this** file (verdict sections with findings, checks run, and
  carried items).
- **M2 is measure-gated**: it starts with a registration-time profile of a representative
  diamond-shaped child through the M1 full path; implementation proceeds only if the profile
  shows a real regression relative to the linearized baseline. If M2 is skipped, record the
  decision and the numbers here.
- **M3 is downstream-only**: it validates against InternalMath the same way as the Lean 4.31
  downstream patch workflow (`Plans/InternalMathLean431DownstreamPatch.diff`). Do not edit
  `../InternalMath` source unless explicitly requested; use temporary worktrees or `.pi`/`/tmp`
  diagnostics.

## Purpose

Allow a theory author to build a final object theory from several independently reusable extension
layers over a common base.  The motivating shape is MLTT:

```lean
declare_type_theory MLTT.Basic where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  syntax_sort Tm (Γ : Ctx)
  judgment IsCtx (Γ : Ctx)
  judgment IsTy {Γ : Ctx} (A : Ty Γ)
  judgment IsTm {Γ : Ctx} (a : Tm Γ) (A : Ty Γ)
  judgment EqTm {Γ : Ctx} (a : Tm Γ) (b : Tm Γ) (A : Ty Γ)

declare_type_theory MLTT.Substitution extends MLTT.Basic where
  ...

declare_type_theory MLTT.Pi extends MLTT.Substitution where
  ...

declare_type_theory MLTT.Sigma extends MLTT.Substitution where
  ...

declare_type_theory MLTT extends MLTT.Pi, MLTT.Sigma where
  ...
```

The point is that features should share only their real prerequisites.  For example, `MLTT.Pi` and
`MLTT.Sigma` can both depend on `MLTT.Substitution`, while unit, empty, natural numbers, identity
types, universes, and HoTT primitives should be reusable without forcing an arbitrary linear chain
between otherwise independent features.

## Current behavior

InternalLean already parses multiple parents:

```lean
declare_type_theory Child extends Parent₁, Parent₂ where
  ...
```

But parent flattening concatenates each flattened parent.  A diamond with shared ancestry currently
fails because the common base declarations are duplicated:

```lean
declare_type_theory MPBase where
  syntax_sort A

declare_type_theory MPLeft extends MPBase where
  lf_opaque x : A

declare_type_theory MPRight extends MPBase where
  lf_opaque y : A

declare_type_theory MPChild extends MPLeft, MPRight where
  lf_opaque z : A
```

Current diagnostic:

```text
error: duplicate syntax-sort declaration 'A' in flattened type theory 'MPChild'
```

This means downstream developments that want reusable feature layers must temporarily linearize the
layers.

## Current composition paths (implementation facts)

The 2026-06-12 scoping review found that theory composition runs through **two parallel paths**,
and any diamond support must account for both:

1. **Full path.** `registerTheoryFull` (`InternalLean/Registration.lean`) flattens the high-level
   signature with `flattenSignature` (`InternalLean/LFElab/Core.lean:177`) and re-checks the
   whole flattened source. `flattenSignature`'s `seen` set is currently **per-path cycle
   detection only**: it is passed down but not shared across sibling parents, so a shared
   ancestor is flattened once per path — this is the diamond failure. Duplicate detection is
   centralized in `checkNoDuplicateNamesInSignature` (`InternalLean/LFElab/Core.lean:332`),
   which produces the current diagnostic.
2. **Incremental fast path.** `registerTheory` routes `declare_type_theory Child extends ...` to
   `registerTheoryIncrementalFromParents` when the child block qualifies
   (`unsupportedIncrementalTheoryBlockReason?` returns none and the signature has no
   macros/roles). That path does **not** re-check flattened source: it builds the child's
   checked baseline by concatenating already-checked parent artifacts
   (`checkedParentBaseForSignature` → `appendCheckedTheoryDelta`,
   `InternalLean/LFElab/Incremental.lean`). Checked artifacts are stored as a flat
   per-theory soup with **no per-declaration provenance and no dedupe**, so a diamond through
   this path would duplicate checked artifacts and fail later with kernel-level errors such as
   "duplicate rule schema".

Related facts that constrain or help the implementation:

- Admissions are already DAG-aware: `getInternalAdmissionsForIncludingParents`
  (`InternalLean/Registry.lean`) walks parents with a visited set and dedupes, so the
  admission-provenance acceptance test below should mostly follow from fixed flattening.
- `checkedHLSignatureMatchesChecked` compares per-category array sizes between the checked HL
  signature and the checked artifact, and `CompiledLFCheckCacheStamp` records per-category
  counts. Dedupe must keep these invariants consistent; they are good cheap regression probes.
- Stored signatures keep `parents` un-flattened (both registration paths store the original
  parent list), so descendants re-flatten through the registry; a flattening fix applies
  transitively without migrating stored state.
- `flattenSignature` concatenates **all** parallel metadata arrays (roles, model sections and
  memberships, macros, level params, rewrite/transport metadata, level-normalizer profiles).
  Visited-set traversal dedupes all of them uniformly because each ancestor theory contributes
  its arrays at most once.

## Design goal

Make multi-parent extension work for ordinary shared-ancestor diamonds by treating inherited
identical declarations as one declaration in the flattened child.

The feature must remain generic:

- no hard-coded MLTT, HoTT, SCT, or declaration names;
- no special treatment for syntax sorts, judgments, rules, or type formers beyond generic
  declaration identity;
- no automatic merging of two unrelated declarations with the same local name;
- clear diagnostics when two parents provide genuinely conflicting declarations.

## Scope decisions

These decisions bound each phase; deviating from them requires re-opening this spec, not silent
scope growth.

1. **M1 supports diamonds in the full path only.** `registerTheory` gains a shared-ancestor
   detection helper over the parent DAG; children whose parent DAG shares an ancestor are routed
   to `registerTheoryFull` even when the block would otherwise qualify for the incremental fast
   path. This reuses the existing graceful-fallback routing (the same pattern as unsupported
   incremental blocks). Tree-shaped parent lists keep the incremental fast path unchanged.
2. **Incremental diamond support is M2 and measure-gated.** Concatenating checked parent
   artifacts cannot dedupe without either per-theory checked deltas or a name-plus-structural
   identity argument; that is its own reviewable design, and it is only worth doing if the M1
   full-path fallback is measurably too slow for MLTT-sized children.
3. **Downstream validation is M3.** The InternalMath de-linearization (acceptance test 5 of the
   original draft) lives in a downstream worktree/patch phase and cannot be part of an
   InternalLean commit.
4. **Level parameters follow declaration identity.** A theory-level universe parameter such as
   `{u}` inherited from a shared ancestor through two parents dedupes like any declaration
   (one contribution from one source theory). Two **independent** parents each declaring a level
   parameter with the same name remain an error, with the same conflict diagnostic shape as
   declarations.
5. **Ordering is backward compatible by construction.** The deterministic left-to-right
   post-order traversal with a shared visited set produces byte-identical flattened order for
   sharing-free parent trees (every existing theory), so linear chains must show no ordering or
   model-field-order change. This is an explicit M1 acceptance check, not an accident.
6. **`extend_type_theory` keeps working on diamond children.** Block extension appends to the
   flattened base; it needs no new semantics, only a regression test.

## Proposed semantics

Flatten the parent DAG, not the list of parent trees.  Each ancestor theory should contribute its
own direct declarations at most once.

The algorithm:

1. Traverse the parent DAG in a deterministic left-to-right post-order (ancestors before
   descendants), keeping one **shared** visited set of theory names across the whole traversal,
   so a shared ancestor is flattened once. Cycle detection stays.
2. Append each theory's direct declaration block (all parallel metadata arrays) after its
   ancestors.
3. While traversing, record a provenance side map from declared local name to the contributing
   source theory and one witness parent path. This map exists only for diagnostics; the
   declaration record types themselves do **not** grow provenance fields.
4. When two different theories contribute declarations with the same local name, reject with
   both source paths. Note this case is simpler than the original draft suggested: with
   identity-by-source-theory there is nothing to compare structurally — the visited set already
   guarantees a single contribution per ancestor, so any same-name collision is from two
   genuinely different declarations. "Byte-for-byte identical but declared independently" is
   just a conflict; an alias/import-equivalence mechanism stays future work.
5. Preserve source docs, model-section memberships, roles, admissions, and transport metadata for
   the kept declaration (automatic: the metadata arrays travel with the single contribution).

The flattened child should behave as if each inherited declaration appears exactly once, in the
same relative order as the topological traversal.

## Declaration identity

Inherited declarations are identified by their source theory and local name, not only by local
name.  For example, if `MLTT.Basic.Ctx` is inherited through both `MLTT.Substitution` and
`MLTT.Pi`, those are the same source declaration and are deduped by the visited set.

Conflicting independent declarations remain errors:

```lean
declare_type_theory Left where
  syntax_sort A

declare_type_theory Right where
  syntax_sort A

declare_type_theory Bad extends Left, Right where
  ...
```

This fails because `Left.A` and `Right.A` are different declarations sharing the same local name
in the child namespace.

## Diagnostics

Add diagnostics for inherited DAG composition:

- `#print_type_theory_parents T` or an extension of `#print_type_theory T` showing the parent DAG;
- conflict diagnostics that mention both contributing theories and declaration categories, driven
  by the provenance side map;
- optional model-obligation provenance showing the original source theory for inherited fields
  (may be carried to a later phase if it grows).

A useful conflict message:

```text
conflicting inherited declaration 'A' in type theory 'Bad'
from parent path Bad -> Left and parent path Bad -> Right
both declarations are syntax_sort declarations but have different source theories
```

For successful diamond deduplication, debug output should make it visible that a shared ancestor was
included once.

## Phase M1: parent-DAG flattening in the full path

Scope:

1. Convert `flattenSignature` to the shared-visited-set DAG traversal above, covering all
   parallel metadata arrays, with the provenance side map for diagnostics.
2. Upgrade the duplicate-name conflict diagnostic (in or beside
   `checkNoDuplicateNamesInSignature`) to name both contributing theories and parent paths.
3. Add the shared-ancestor detection helper and gate such children out of
   `registerTheoryIncrementalFromParents` into `registerTheoryFull` (scope decision 1).
4. Apply the level-parameter policy (scope decision 4).
5. Add `#print_type_theory_parents` (or extend `#print_type_theory`) with the parent DAG and
   an indication of dedupe.

Acceptance tests for M1:

1. Diamond deduplication smoke:

   ```lean
   declare_type_theory Base where
     syntax_sort A

   declare_type_theory Left extends Base where
     lf_opaque x : A

   declare_type_theory Right extends Base where
     lf_opaque y : A

   declare_type_theory Child extends Left, Right where
     lf_opaque z : A
   ```

   Expected: checks, and the generated model interface for `Child` has one `A` field.

2. Independent conflict smoke: the `Bad extends Left, Right` example above is rejected with a
   conflict diagnostic naming both parent paths.

3. Role and model-section dedupe smoke: a shared base declaration with roles and model-section
   membership is inherited through two parents and appears once with metadata intact.

4. Admission/provenance smoke: a shared admitted internal declaration inherited through two
   parents appears once in `#lint_type_theory_sorries` for the child.

5. Fallback-gating smoke: a diamond child whose block **would** qualify for the incremental fast
   path registers through the full path (visible in the recorded registration profile/strategy)
   and checks; a tree-shaped multi-parent child still uses the incremental path.

6. Linear-chain ordering regression: an existing linear `extends` chain produces an unchanged
   flattened declaration order and model-field order (scope decision 5).

7. `extend_type_theory` on a diamond child appends a block and checks (scope decision 6).

8. Level-parameter smokes: `{u}` shared through a diamond dedupes; two independent parents both
   declaring `{u}` are rejected (scope decision 4).

9. Cache/invariant probe: `checkedHLSignatureMatchesChecked` and the compiled-cache stamp counts
   agree for a diamond child (deduped counts on both sides).

Reviewer focus for M1: that dedupe is by visited source theory, never by content comparison; that
the incremental gating cannot route a shared-ancestor DAG into `appendCheckedTheoryDelta`; the
ordering regression for existing linear chains; and that conflict diagnostics name both paths.

## Phase M2 (measure-gated): diamonds in the incremental fast path

Gate: profile registration time for a representative MLTT-shaped diamond child through the M1
full path against the linearized baseline. Implement only on a measured regression that matters
for downstream workflows; otherwise record the numbers and skip.

Design directions to evaluate (this phase starts with a short design note appended here, same
discipline as other measure/design-gated phases):

- **Per-theory checked deltas (preferred).** Store each theory's own checked contribution at
  registration time so a child can compose ancestor deltas in topological order with the same
  visited-set discipline as M1. This gives the checked-artifact path real provenance instead of
  inferring it.
- **Name-plus-structural dedupe in `appendCheckedTheoryDelta`.** Justifiable only because the
  M1 HL-level conflict check runs first and guarantees that same-name checked artifacts can only
  be same-ancestor copies; requires a determinism argument (checked artifacts for one source
  theory must be byte-stable across paths, including derived schemas, certificates, and
  diagnostic strings) and a regression that proves it.

Acceptance for M2: for diamond children, the incremental path produces checked artifacts, checked
HL signatures, and compiled caches identical to the full path (direct comparison test); the
registration profile shows the intended strategy; the M1 gating helper is relaxed only for the
supported shapes.

## Phase M3 (downstream): InternalMath de-linearization validation

Replace the temporary linear MLTT chain in a downstream InternalMath worktree by independent
mixins over `MLTT.Basic` and declare:

```lean
declare_type_theory MLTT extends
  MLTT.Pi, MLTT.Sigma, MLTT.Coproduct,
  MLTT.Empty, MLTT.Unit, MLTT.Nat, MLTT.Identity
where
  ...
```

Acceptance for M3: the MLTT library build and `#lint_type_theory_sorries MLTT` baseline are
unchanged except for intentional model-obligation/provenance ordering; results are recorded here
and in the work log as a patch/report, following the Lean 4.31 downstream workflow. No
InternalLean source changes are expected in this phase; if the validation surfaces one, it goes
through a reviewed M1/M2 follow-up commit, not a downstream-only hack.

## Non-goals

- Selective imports or hiding declarations.
- Renaming inherited declarations.
- Merging two independently declared but structurally identical theories.
- Typeclass-like search for feature dependencies.
- Any MLTT-specific implementation path.
- Alias/import-equivalence between independently declared identical theories (future work noted
  in "Proposed semantics" step 4).

## M1 review — 2026-06-12 (ACCEPTED)

M1 (`7a8b443 M1: add parent DAG flattening`) is accepted. Parent flattening now traverses the
source-theory DAG with a shared visited set and deterministic left-to-right post-order, so shared
ancestors contribute once while independently declared same-name items remain conflicts. Shared-
ancestor `declare_type_theory extends` blocks are gated out of the incremental parent-concatenation
path and use the full checker.

Verified:

- Diamond inheritance dedupes by visited source theory, not by content comparison, and the model
  interface for the diamond child has one shared base field.
- Independent same-name parents are rejected before checked-artifact concatenation, with diagnostics
  naming both parent paths; independent duplicate level parameters are rejected similarly.
- Role metadata, model-section metadata, inherited admissions, level parameters, and checked/cache
  counts remain deduped and coherent for a shared ancestor.
- Registration profiles show the full fallback for a shared-ancestor diamond and the incremental
  strategy for a sharing-free multi-parent tree.
- Linear-chain declaration order is unchanged; a scratch probe also checked the linear model-field
  order `A, x, y, z`.
- `extend_type_theory` on a diamond child appends and checks, preserving the compiled-cache and
  checked-HL invariants.
- `#print_type_theory_parents` reports the parent DAG and marks already-included shared ancestors.

Checks run:

- `lake build InternalLean.LFElab.Core InternalLean.Registration InternalLean.Diagnostics \
  InternalLeanTest.TheoryMixinCompositionTest`
- `lake build InternalLeanTest.TheoryMixinCompositionTest`
- `lake build InternalLeanTest`
- `lake build InternalLean.Command InternalLeanTest InternalLean Examples`
- `lake build -KinternalLean.frontend.compareLegacy=true InternalLean.Command InternalLeanTest \
  InternalLean Examples`
- `python3 scripts/check_lean_line_lengths.py --max 100 --root .`
- `python3 scripts/check_text_style.py --root .`
- `git diff --check`
- `lake env lean .pi/tmp_m1_linear_order_probe.lean`

No blocking or non-blocking findings. M2 may start with its required measurement gate.

## M2 design/measurement gate — 2026-06-12 (SKIPPED)

M2 started with the required registration-time profile instead of an implementation. The benchmark
used generated scratch sources under `.lake/build/internallean-bench/mixin-m2/` and measured only
the final `registerTheory` call inside `run_cmd`, after parent theories were already registered.
Both variants had the same checked final shape: 115 checked LF metadata declarations, 47 LF opaque
constants, and 52 rules.

Representative shape:

- shared base: `Basic` plus `Substitution` with MLTT-like `Ctx`, `Ty`, `Tm`, substitution
  constants, judgments, roles, and rules;
- seven feature layers (`Pi`, `Sigma`, `Coproduct`, `Empty`, `Unit`, `Nat`, `Identity`) over the
  shared substitution layer;
- diamond child: final theory extends all seven feature layers and therefore uses the M1 full
  fallback strategy;
- linearized baseline: the same feature layers are arranged as a chain and the final theory extends
  the last layer, using the incremental streaming strategy.

Eight warm-cache Lean-process runs gave:

| variant | strategy | final registration mean | median | min-max |
| --- | --- | ---: | ---: | ---: |
| diamond | `full fallback declare_type_theory: shared parent ancestor` | 36.125ms | 36ms | 36–37ms |
| linearized | `incremental declare_type_theory extends (streaming block)` | 5.375ms | 5ms | 5–6ms |

The measured final-registration delta is about 30.75ms. Whole scratch-file wall time was dominated
by Lean startup/import and parent registration noise (diamond mean 909.65ms, linear mean
941.97ms), so the user-visible command-level benchmark did not show an end-to-end regression.

Design evaluation:

- Per-theory checked deltas remain the right design if the fallback becomes a real bottleneck,
  because they would give the checked-artifact path source-theory provenance matching M1.
- Name-plus-structural dedupe in `appendCheckedTheoryDelta` was not pursued. It would add a
  determinism/trust-boundary argument for duplicate checked artifacts without a measured need.

Decision: skip M2 implementation. The profile shows a relative slowdown in the final registration
call, but the absolute cost on an MLTT-shaped signature is tens of milliseconds and does not yet
matter for downstream workflows. The M1 gate remains in place: shared-ancestor diamonds continue to
use the full checker, while tree/linear parent shapes keep the incremental fast path.

## M2 review — 2026-06-12 (ACCEPTED)

M2 (`1046bd3 M2: record diamond measurement gate`) is accepted as a measured skip. The phase made
no `InternalLean/` or `InternalLeanTest/` implementation change; it records the required
registration-time profile and keeps the M1 full-fallback gate for shared-ancestor diamonds.

Verified:

- The scratch benchmark shape is representative of the intended MLTT mixin pressure: a shared
  `Basic`/`Substitution` layer, seven independent feature layers, and matching diamond vs.
  linearized final theories.
- The benchmark measures the final `registerTheory` call after parent registration, which is the
  M2 gate target, and both variants report the same final checked shape: 115 metadata
  declarations, 47 LF opaque constants, and 52 rules.
- Re-running the scratch benchmark during review confirmed the strategies and order of magnitude:
  three diamond runs were 36ms each with `full fallback declare_type_theory: shared parent
  ancestor`; three linear runs were 5ms each with `incremental declare_type_theory extends
  (streaming block)`.
- The recorded decision to skip incremental-diamond implementation is consistent with the spec's
  measure gate: the absolute final-registration delta is about 31ms and the whole-file benchmark
  is dominated by Lean startup/import and parent registration noise.
- No name-plus-structural checked-artifact dedupe or other trust-boundary change was introduced.

Checks run:

- Three `lake env lean .lake/build/internallean-bench/mixin-m2/m2_profile_diamond.lean` runs
- Three `lake env lean .lake/build/internallean-bench/mixin-m2/m2_profile_linear.lean` runs
- `lake build InternalLean.Command InternalLeanTest InternalLean Examples`
- `lake build -KinternalLean.frontend.compareLegacy=true InternalLean.Command InternalLeanTest \
  InternalLean Examples`
- `python3 scripts/check_lean_line_lengths.py --max 100 --root .`
- `python3 scripts/check_text_style.py --root .`
- `git diff --check`

No blocking or non-blocking findings. M3 may start as the downstream/report-only validation phase.

## M3 downstream validation — 2026-06-12 (REPORT)

M3 was completed as a downstream-only validation in `../InternalMath-m3-validation`. The worktree
was created from `../InternalMath` `HEAD` (`e5ea08b`) and populated with the current untracked HoTT
MLTT sources from `../InternalMath`; `lakefile.toml` in the temporary worktree used path
dependencies to `../InternalLean` and `../InternalMath/.lake/packages/mathlib`. No source file under
`../InternalMath` was edited.

Patch snapshot: `Plans/InternalMathMLTTMixinCompositionPatch.diff`.

The downstream patch changes only the MLTT assembly/import shape:

- `MLTT.Sigma`, `MLTT.Coproduct`, `MLTT.Empty`, `MLTT.Unit`, `MLTT.Nat`, and `MLTT.Identity` import
  `MLTT.Substitution` and extend `MLTT.Substitution` directly instead of forming a temporary
  linear chain through each other.
- `InternalMath.HoTT.MLTT` imports all selected mixins and declares final `MLTT` as
  `MLTT.Pi, MLTT.Sigma, MLTT.Coproduct, MLTT.Empty, MLTT.Unit, MLTT.Nat, MLTT.Identity`.
- The final `MLTT` registration profile reports
  `full fallback declare_type_theory: shared parent ancestor`, and `#print_type_theory_parents MLTT`
  shows `MLTT.Substitution` deduped through the seven parent paths.

Baseline and patched validation:

- Linear baseline in the temporary worktree: `lake build InternalMath.HoTT.MLTT.Library` passed.
- Linear baseline `#lint_type_theory_sorries MLTT` reported three admitted declarations:
  `MLTT.idFiberContr`, `MLTT.universePathTy`, and `MLTT.idtoeqv`, with downstream dependency
  `idIsEquiv depends on admitted idFiberContr`.
- Patched diamond worktree: `lake build InternalMath.HoTT.MLTT.Library` passed.
- Patched diamond `#lint_type_theory_sorries MLTT` reported the same three admitted declarations
  and the same downstream dependency; the normalized lint output was byte-identical after replacing
  the scratch lint filename.
- `git diff --check` passed in the temporary downstream worktree after marking the HoTT files as
  intent-to-add for diff checking.

Decision: M1's full-path diamond support is sufficient for the downstream MLTT de-linearization
patch. No InternalLean follow-up was needed for M3, and the downstream patch is left as a report
snapshot rather than applied to `../InternalMath`.
