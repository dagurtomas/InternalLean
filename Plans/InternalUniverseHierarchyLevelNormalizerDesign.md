# Internal Universe Hierarchy Level-Normalizer Design

Status: U5-design gate for `Plans/InternalUniverseHierarchyEncodingSpec.md`.
Implementation of U5 must wait for an `ACCEPTED` review verdict for this design.

## Purpose

Layer 5 adds optional automation for object-language level expressions in theories that use the
universe hierarchy pattern from U1--U4. The automation should help with facts such as:

- `lmax i i` normalizes to `i`;
- `lmax` is associative and commutative;
- `zero` is the bottom level;
- `Le i (lmax i j)` and `Le j (lmax i j)` are decidable side conditions;
- `succ` is monotone when both sides are normalized.

The design preserves the existing boundary: object levels are ordinary LF data, and every use of
level automation must appear as a replay certificate or a conversion-certificate leaf. The LF
checker's ordinary definitional equality must not learn a global theory of levels.

## Non-goals

- No Lean universe inference from object-level terms.
- No global cumulativity relation between generated Lean model fields.
- No unconditional rewrite of every `lmax` expression during checking.
- No theorem proving over arbitrary level constants or user-defined functions.
- No silently trusted solver. Opaque or external certificates, if supported later, must remain
  audit-visible leaves.

## Opt-in profile

U5 should be per-theory opt-in. The U1--U4 declarations and role metadata are not enough to run a
normalizer because the constructors `zero`, `succ`, and `lmax` are still ordinary LF constants. The
implementation should introduce one explicit profile declaration, either as a theory-block item or
as a post-declaration command. A concrete surface can be chosen during implementation, but it should
carry this information:

```lean
level_normalizer UniverseHierarchy where
  level Level
  zero zero
  succ succ
  max lmax
  le Le
  trust executable_checked
```

If this is implemented inside a theory block, the `UniverseHierarchy` argument can be omitted. The
profile should be validated after parent flattening:

- `Level` must be a syntax sort tagged or otherwise accepted as the universe-level family.
- `zero : Level` must be an LF opaque constant or checked LF definition with result `Level`.
- `succ : Level -> Level` must have one explicit `Level` argument and result `Level`.
- `lmax : Level -> Level -> Level` must have two explicit `Level` arguments and result `Level`.
- `Le : Level -> Level -> judgment` must be a judgment family.
- Duplicate profiles or ambiguous inherited profiles are errors.

The U2 shorthand should not automatically enable the normalizer in the first implementation. Users
can add the opt-in explicitly after seeing the trust and diagnostic behavior.

## Normalizer fragment

The executable fragment is first-order and structural. It recognizes only the profile's level sort
and constructors. Terms are normalized after lowering to scope-erased LF/object expressions or
structural `KTerm`s.

Level terms:

```text
level ::= zero
        | neutral
        | succ level
        | lmax level level
```

A neutral is a locally bound level variable or a closed level constant that is explicitly allowed as
an atom by the checker. Applications headed by unmarked LF constants are unsupported in the first
implementation; they should fail with a diagnostic naming the head and the source path. This keeps
partial support visible instead of treating arbitrary functions as algebraic atoms.

Canonical form:

```text
NF := max(floor, atom_1 + offset_1, ..., atom_n + offset_n)
```

- `floor : Nat` represents finite levels generated from `zero` and `succ`.
- Each `atom` is a stable scope-erased neutral level term.
- Offsets are natural numbers.
- At most one entry exists for each atom; merging takes the larger offset.
- `succ` increments the floor and every atom offset.
- `lmax` takes componentwise maxima.

Equality succeeds when two normal forms are identical. Order succeeds when every literal and atom
component of the left normal form is bounded by the right normal form:

- `floor_left <= floor_right`, and
- for each atom `a + k` on the left, the right contains `a + m` with `k <= m`.

This proves the intended max/idempotence/associativity/commutativity consequences and simple
`Le` goals such as `Le i (lmax i j)`. It does not invent facts such as `Le i j` for unrelated
atoms, and it does not use arbitrary hypotheses unless a later reviewed extension adds an explicit
assumption context to the query.

## Certificate surfaces

### Side-condition certificates

Rules should request level facts through existing side-condition slots. The recommended shape is a
side condition whose input is a `Le`-headed query or a small dedicated query object rendered from
`Le lhs rhs`:

```lean
rule lift_lmax_wf {i : Level} {j : Level} (A : Ty i) where
  side_condition le_left by level_normalizer : Le i (lmax i j)
  premise wf : IsTy (i := i) A
  conclusion : IsTy (i := lmax i j) (lift (i := i) (j := lmax i j) A)
```

The checker should elaborate the side-condition input normally, then the executable level hook
should:

1. verify that the input is a supported `Le lhs rhs` query for the profiled `Le` judgment;
2. normalize `lhs` and `rhs` with the profile;
3. decide the normal-form order;
4. emit a checked side-condition certificate containing the profile name, query, normal forms, and
   decision trace.

The current `SideConditionCertificateKind` only records `builtinTrivial`. U5 should extend the
provenance vocabulary with a level-normalizer kind or a generic executable-hook kind carrying the
hook name. Diagnostics must print this provenance instead of making level facts look like trivial
side conditions.

### Conversion certificates

Conversion automation should be a conversion plugin, not ordinary LF definitional equality. A
profile may declare or generate an executable conversion plugin for level normalization, for
example:

```lean
conversion_plugin level_norm executable [reindexing]
```

Implementation may add a more specific `level_normalization` conversion step kind if the generic
`reindexing` label is too imprecise. Either way, a conversion leaf is accepted only when:

- the plugin is declared `executable_checked` for this theory/profile;
- both endpoints are supported level expressions, or supported expressions whose relevant index
  subterms are level expressions;
- the computed normal forms justify the requested equality or reindexing step;
- the certificate payload agrees with the recomputed normal forms, if a payload is present.

The normalizer must not run as a fallback for ordinary conversion. Tactic `simp`, tactic `rw`, and
quoted/frontend checks may use it only by constructing an explicit conversion-certificate leaf that
is then validated by the structural conversion checker.

External-certificate or opaque plugin modes are not needed for the first U5 implementation. If they
are added later, the existing trust-kind labels must remain visible in replay output and lints.

## Trust accounting and audit output

Every successful level-normalizer use must be visible in one of the existing audit surfaces:

- `#print_checked_type_theory` should show the level-normalizer profile and generated or declared
  plugin/solver names.
- `#print_logical_framework_side_condition_hooks` should list produced level certificates with the
  query and normalized forms.
- `#print_lf_replay_certificate` should include level side-condition certificate obligations in the
  replay dependency summary.
- Conversion-certificate diagnostics should show the level-normalizer plugin step, trust kind, and
  endpoint normal forms.
- Model-obligation output should not treat level-normalizer facts as primitive model fields unless
  the user explicitly declared a corresponding rule or opaque constant.

No code path may silently downgrade a failed executable level certificate to an opaque assumption.
If a profile is missing, malformed, or unsupported, automation must fail with an actionable error.
Existing `sorry`/admission lints are unchanged.

## Native tactic diagnostics

Native tactics should surface level automation as certificate production, not as Lean goals.
Diagnostics should name the tactic, candidate rule or plugin, side-condition slot, and profile.

Recommended messages:

- Missing profile: `object tactic apply lift_lmax_wf needs level-normalizer profile for Le`.
- Unsupported term: include the unsupported head, the rendered subterm, and the supported grammar.
- Failed order: show `lhs`, `rhs`, `nf(lhs)`, and `nf(rhs)`.
- Missing trust: say whether the plugin is undeclared, declared opaque, or missing the supported
  step kind.
- Success tracing for debug/fuel output: include the generated certificate name and compact normal
  forms.

Initial integration should target existing `apply`/`refine` side-condition synthesis and existing
`rw`/`simp` conversion-plugin diagnostics. A new user tactic such as `level` is optional and should
be a separate reviewed extension if the basic certificate-producing paths are not enough.

## Performance discipline

The normalizer should run only for explicit level-normalizer side conditions or explicit
level-normalizer conversion-plugin leaves. It should not scan unrelated LF expressions during
ordinary checking.

Implementation requirements:

- cheap head/profile checks before recursive normalization;
- a size or depth budget with a clear diagnostic on exhaustion;
- memoization keyed by profile plus scope-erased term for repeated subterms;
- no eager unfolding of unrelated checked LF definitions;
- tests following the Phase 11 lazy-unfolding discipline, including a doubling/max tree that checks
  without exponential normalization.

## Implementation slices after gate acceptance

1. Add the profile metadata and diagnostics, without any automation.
2. Implement and unit-test the normalizer on scope-erased object expressions or structural terms.
3. Add the executable side-condition hook and certificate provenance.
4. Add conversion-plugin validation for level-normalization leaves.
5. Wire native tactic diagnostics to the new failure modes.
6. Add positive, negative, audit-output, and performance regressions.

Each slice should keep LF checking and replay as the acceptance gate. If any slice requires a
broader trust-boundary change, stop and re-open design review before implementation continues.

## Required U5 implementation tests

- Positive side-condition certificate for `Le i (lmax i j)`.
- Negative side-condition certificate for unrelated atoms, with normalized-form diagnostics.
- Unsupported-head diagnostic for a level expression outside the fragment.
- Checked replay certificate output showing level side-condition dependencies.
- Conversion-certificate success for an `lmax` associativity/commutativity normalization step.
- Deliberate divergent/wrong conversion certificate rejected by structural replay.
- Native tactic `apply` or `refine` failure that points at the missing or failed level certificate.
- No acceptance change for the same theory when the profile is absent.
- Performance regression for a shared or doubled `lmax` tree.
