# Contributing to M4TH

Thank you for your interest in contributing to this project. This repository
contains formalisations of hyperbolic and dispersive partial differential
equations in Lean 4 over Mathlib.

## Project structure

The repository is organised as three independent Lean 4 packages, each with
its own `lakefile.toml`:

| Package | Topic |
|---|---|
| `ConservationLaws` | Weak solutions, travelling shocks, Rankine-Hugoniot, Lax entropy condition |
| `BurgersBlowUp` | Finite-time gradient blow-up for the inviscid Burgers equation |
| `KdV` | Exact one-soliton profile and conservation laws for KdV |

Each package is self-contained (depends only on Mathlib) and its modules form a
linear dependency chain designed for incremental contribution to Mathlib.

The paper `M4THDocs/Hyperbolic_Dispersive_PDE_in_Lean4.md` is the companion
mathematical exposition (CC-BY 4.0).

## How to contribute

### Reporting issues

- Use the GitHub issue tracker.
- For a bug, include the Lean 4 version, the Mathlib commit pinned in
  `lakefile.toml`, and a minimal reproducing example.
- For a mathematical question about a proof, reference the specific theorem name
  and module.

### Proposing changes

1. **Discuss first.** Open an issue describing what you intend to change and why.
   For mathematical additions, explain the PDE result you want to formalise and
   how it fits the existing dependency graph.

2. **Keep packages self-contained.** Each package must depend
   only on Mathlib, not on the other packages. If your contribution needs lemmas
   from another package, coordinate with the maintainer: those lemmas should be
   submitted upstream to Mathlib first, then both packages can import them from
   there.

3. **Follow Mathlib conventions.**
   - Use `ContDiff`, `deriv`, `fderiv`, `MeasureTheory` from Mathlib.
   - Name theorems with the namespace prefix (e.g. `ConservationLaw.hasShockIntegralReduction`).
   - Every file must have a copyright header referencing the Apache 2.0 license
     and the `LICENSE` file.
   - Module docstrings are required.

4. **No `sorry`, no `axiom`.** Every theorem must be fully proved. The axiom
   certificate of every headline theorem must be exactly
   `[propext, Classical.choice, Quot.sound]`. Run the certificate check
   documented in each package's README before submitting.

5. **Pull requests.**
   - Target the `main` branch.
   - One logical change per PR.
   - Ensure `lake build` passes for the affected package.
   - If the change touches the Live single-file variant, update the
     corresponding `*Live/*.live.lean` file to match.

### Code style

- Line length: 100 characters preferred.
- Use `set_option linter.unusedVariables false` only when justified; document why.
- Minimise imports before opening a Mathlib PR (use `#min_imports` or the import linter).

### Licence

By contributing, you agree that your contributions will be licensed under the
Apache License 2.0 (software) and CC-BY 4.0 (documentation text), matching the
project licences.

## Development setup

```bash
# Choose a package, e.g. ConservationLaws
cd ConservationLaws

lake update
lake exe cache get
lake build ConservationLaws
```

## Contact

- Author: Bezalel Izquierdo Perez
- ORCID: [0009-0001-5993-4057](https://orcid.org/0009-0001-5993-4057)
- Repository: <https://github.com/Alektronnik/M4TH>
