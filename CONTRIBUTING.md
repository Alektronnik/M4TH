# Contributing to M4TH

Thank you for your interest in contributing to this project.  M4TH is a monorepo
of 15 self-contained Lean 4 packages spanning PDE, analytic number theory, gauge
theory, lattice field theory, and arithmetic geometry.  All packages depend only
on Mathlib.

Before contributing, read `M4THDocs/M4THProtocol.md` — it defines the full
package standard: directory layout, lake configuration, bit-exact live layer,
web-layer convention for v4.33.0-rc1 compatibility, and the `M4TH.sh`
validation script.

## Project structure

```
M4TH/
  M4TH.sh                  Unified build / live / web validation script
  M4THDocs/
    M4THProtocol.md        Complete package standard (read this first)
    ...                    Companion papers (CC-BY 4.0)
  <PackageName>/
    README.md
    lakefile.toml
    <PackageName>.lean     Root aggregator + native SVG generator
    <PackageName>.svg
    <PackageName>/         Library source modules
    <PackageName>Live/     Live layer + optional web layer
      <PackageName>.live.lean
      <PackageName>.live.MANUAL.md
      <PackageName>.web.lean        (only if v4.33.0-rc1 needs fixes)
      <PackageName>.web.README.md
```

Each package is self-contained (depends only on Mathlib, never on another
M4TH package).

## How to contribute

### Reporting issues

- Use the GitHub issue tracker.
- Include the Lean 4 version, the Mathlib commit pinned in `lakefile.toml`,
  and a minimal reproducing example.
- For a mathematical question about a proof, reference the specific theorem name
  and module.

### Proposing changes

1. **Discuss first.** Open an issue describing what you intend to change and why.

2. **Keep packages self-contained.** Each package depends only on Mathlib.
   If your contribution needs lemmas from another package, coordinate with the
   maintainer: submit those lemmas upstream to Mathlib first.

3. **Follow the M4TH Protocol.** See `M4THDocs/M4THProtocol.md`.  Key rules:
   - Every file must have the standard copyright header (Apache 2.0).
   - Module docstrings are required.
   - Use namespaced imports (`public import PackageName.Module`).
   - No `sorry`, no `axiom`, no `native_decide`.
   - The axiom certificate of every headline theorem must be exactly
     `[propext, Classical.choice, Quot.sound]`.

4. **Live layer is bit-exact.** If you change a source module, regenerate the
   corresponding `*Live/*.live.lean` file.  Do not patch the live file manually
   to diverge from the source.

5. **Web layer.** If your change introduces or removes an API name that differs
   between Lean v4.31.0 and v4.33.0-rc1, update `*Live/*.web.lean` and its
   `*Live/*.web.README.md` accordingly.  See the protocol for the name-change
   table.

6. **Pull requests.**
   - Target the `main` branch.
   - One logical change per PR.
   - Run `./M4TH.sh live` before submitting.  All 15 `.live.lean` files must
     compile.  `.web.lean` files target v4.33.0-rc1 and are verified on the
     web environment (live.lean-lang.org).

### Code style

- Line length: 100 characters preferred.
- Minimise imports before opening a Mathlib PR (use `#min_imports` or the import
  linter).

### Licence

By contributing, you agree that your contributions will be licensed under the
Apache License 2.0 (software) and CC-BY 4.0 (documentation), matching the
project licences.

## Development setup

```bash
# From the M4TH monorepo root
./M4TH.sh live                # compile all .live.lean (v4.31.0 local environment)
./M4TH.sh build               # build all packages via lake build
./M4TH.sh build <Package>     # build a single package
./M4TH.sh live  <Package>     # compile .live.lean for one package
./M4TH.sh clean               # remove M4TH.log

# .web.lean files target v4.33.0-rc1 (live.lean-lang.org); they are expected
# to fail on a local v4.31.0 toolchain.  Run './M4TH.sh web' only when you
# have a v4.33.0-rc1 environment available.
./M4TH.sh web   <Package>     # compile .web.lean for one package

# Or directly (from monorepo root, no lake artifacts inside packages)
lake build <PackageName>
```

## Contact

- Author: Bezalel Izquierdo Perez
- ORCID: [0009-0001-5993-4057](https://orcid.org/0009-0001-5993-4057)
- Repository: <https://github.com/Alektronnik/M4TH>
