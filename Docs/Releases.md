# Releases and Lean-version bumps

InternalLean is intended to track recent Lean releases closely. For now, releases should be made
manually after a toolchain bump builds successfully.

## Bumping Lean

Use the helper script from the repository root:

```bash
scripts/bump_lean_toolchain.py --to v4.30.0-rc2
```

The `--to` argument accepts either a Lean tag such as `v4.30.0-rc2` or a full toolchain string such
as `leanprover/lean4:v4.30.0-rc2`.

The script updates `lean-toolchain`, runs `lake update`, and then runs the standard checks:

```bash
lake build InternalLean InternalLeanTest
lake env lean InternalLean.lean
lake env lean InternalLeanTest.lean
scripts/check_text_style.py
scripts/check_lean_line_lengths.py --max 100
```

Useful options:

```bash
scripts/bump_lean_toolchain.py --to v4.30.0-rc2 --dry-run
scripts/bump_lean_toolchain.py --to v4.30.0-rc2 --no-checks
```

After a successful run, review the diff. Usually the intended files are `lean-toolchain` and,
if dependencies were updated, `lake-manifest.json`.

## Tagging compatibility releases

For Lean-ecosystem compatibility, prefer tags that match the Lean toolchain tag, following the
pattern used by packages such as Batteries and Aesop:

```text
v4.30.0-rc2
```

This makes downstream `lakefile.toml` files simple:

```toml
[[require]]
name = "InternalLean"
git = "https://github.com/dagurtomas/InternalLean.git"
rev = "v4.30.0-rc2"
```

Release checklist:

1. Start from the branch that should be released, usually `main`.
2. Run the Lean bump script, or confirm `lean-toolchain` already has the desired version.
3. Run the full CI-equivalent checks locally.
4. Commit the release-ready state.
5. Create an annotated tag:

   ```bash
   git tag -a v4.30.0-rc2 -m "InternalLean for Lean v4.30.0-rc2"
   ```

6. Push the commit and tag:

   ```bash
   git push origin main
   git push origin v4.30.0-rc2
   ```

7. Optionally create a GitHub release from the tag:

   ```bash
   gh release create v4.30.0-rc2 \
     --title "InternalLean for Lean v4.30.0-rc2" \
     --notes "Compatibility release for Lean v4.30.0-rc2."
   ```

Do not move or force-push public release tags. If a fix is needed for the same Lean version after a
tag is public, create a new unique tag such as `v4.30.0-rc2-patch` or
`v4.30.0-rc2-internallean.1` and ask downstream projects to use that tag.
