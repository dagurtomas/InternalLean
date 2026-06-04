---
name: internallean-docs
description: >-
  Use when editing README.md, Docs/*.md, .agents documentation, release notes, or public examples
  in this repository.
---

# InternalLean documentation workflow

Use this skill for documentation work in the `InternalLean` repository.

## Documentation split

- `README.md` and `Docs/` are public, human-facing docs.
- `.agents/` is for detailed agent and maintainer guidance.
- Public docs should explain what users can do and where to start.
- Agent docs may include checklists, failure modes, trust-boundary warnings, and implementation
  conventions.

Keep `.agents/` tool-neutral:

- no local absolute paths;
- no private machine details;
- no instructions for one specific agent harness;
- no replacement for public docs that belong in `Docs/`.

## Public-doc style

- Keep beginner docs direct and concise.
- Prefer the terms “type theory”, “internal proof term”, and “internal tactic script”.
- Explain that internal reasoning happens in the declared object theory, not Lean's kernel.
- Mention current limitations when they affect users, but move long operational cautions to
  `.agents/docs/InternalLeanDevelopmentNotes.md`.
- Keep dependency examples pinned to the current compatibility tag unless documenting development
  against `main`.
- Preserve the README warning that most code in the repository was written by AI coding agents.

## Things to keep accurate

- Current Lean toolchain and release tag.
- Public command names in `InternalLean.Command`.
- Model generation namespace behavior: `generate_model_interface T as M` creates `T.M`.
- `internal theorem` support and its limitations.
- `internal_defs where` batching behavior.
- Object notation limitations and the reserved `⇒` token.
- Public/minimal model commands and provenance diagnostics.
- Deprecated compatibility shims: `object_def` and `object_theorem`.

## Checks

For docs-only edits:

```bash
python3 scripts/check_text_style.py --root .
git diff --check
```

If Lean examples or snippets in tracked Lean files changed, also run an appropriate Lean check:

```bash
lake build InternalLean.Command
lake build InternalLeanTest
```
