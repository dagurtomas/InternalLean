# Shared agent context

This directory contains repository-specific guidance for AI coding agents. It is tracked so that
contributors can use the same project context across different agent tools.

Keep this directory tool-neutral:

- do not include local absolute paths;
- do not include personal names or private machine details;
- do not include instructions for one specific agent harness;
- keep public, human-facing documentation in `Docs/`.

## Contents

- `docs/InternalLeanDevelopmentNotes.md` — detailed InternalLean design, workflow, and release notes
  that are too verbose for public tutorials.
- `skills/internallean-framework/SKILL.md` — shared workflow notes for implementation work in this
  repository.
- `skills/internallean-docs/SKILL.md` — shared workflow notes for README, `Docs/`, and `.agents/`
  documentation edits.

Public docs should be concise and reader-oriented. Agent notes can be more explicit about checks,
status conventions, trust-boundary warnings, and common failure modes.
