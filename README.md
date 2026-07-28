# M4TH

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21635317.svg)](https://doi.org/10.5281/zenodo.21635317)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Lean 4](https://img.shields.io/badge/Lean-4-green.svg)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-latest-orange.svg)](https://github.com/leanprover-community/mathlib4)

**Hyperbolic and dispersive 1D PDE in Lean 4 -- weak solutions, shock waves,
the Lax entropy condition, gradient blow-up, and solitons. Zero `sorry`,
zero `axiom`. Every headline theorem: `[propext, Classical.choice, Quot.sound]`.**

- Author: Bezalel Izquierdo Perez
- ORCID: [0009-0001-5993-4057](https://orcid.org/0009-0001-5993-4057)
- License: Apache 2.0 (software), CC-BY 4.0 (documentation)

---

## One result

Three independent Lean 4 packages, each self-contained on top of Mathlib.
One mathematical idea per package, fully proved.

| Package | Theorem | Status |
|---|---|---|
| `ConservationLaws` | Travelling step is a weak solution iff Rankine-Hugoniot holds (arbitrary flux) | Proved |
| `BurgersBlowUp` | No C^2 solution of Burgers reaches `t = 1` for `u_0(x) = -x` | Proved |
| `KdV` | `3c sech^2(sqrt(c)/2 x)` is an exact soliton for all `c > 0` | Proved |

To our knowledge this is the first formalisation of weak solutions of
conservation laws, of Rankine-Hugoniot and Lax entropy conditions, of gradient
blow-up for a nonlinear PDE, and of the KdV soliton, in any major proof
assistant.

## Quick start

Each package is an independent Lean 4 project. Choose one and build:

```bash
cd ConservationLaws   # or BurgersBlowUp, or KdV

lake update
lake exe cache get
lake build
```

## Axiom certificate

After a successful build, verify zero `sorry` and zero `axiom`:

```bash
echo 'import ConservationLaws
#print axioms ConservationLaw.hasShockIntegralReduction' | lake env lean --stdin

echo 'import BurgersBlowUp
#print axioms Burgers.not_isRegularSolution_initialRamp' | lake env lean --stdin

echo 'import KdV
#print axioms KdV.soliton_satisfies_kdv' | lake env lean --stdin
```

Each must report only `[propext, Classical.choice, Quot.sound]`.

## Theorems

### ConservationLaws -- scalar conservation laws

| Theorem | Statement |
|---|---|
| `hasShockIntegralReduction` | `weakResidual f (shockProfile uL uR s) phi = integral of R-H deficit along interface` |
| `isWeakSolution_shockProfile_of_rankineHugoniot` | Step is weak solution iff Rankine-Hugoniot holds |
| `expansion_midpoint_is_weak_but_not_entropic` | Expansion step is a weak solution violating the Lax entropy condition |

For the Burgers flux `f(u) = u^2/2`, the Lax entropy pair `(eta, q) = (u^2/2, u^3/6)` and
entropy dissipation sign are fully formalised.

### BurgersBlowUp -- gradient blow-up

| Theorem | Statement |
|---|---|
| `constant_along_characteristic` | `u` constant along `x = x_0(1-t)` (Lyapunov-energy uniqueness) |
| `gradient_riccati_evolution` | `V'(t) = -V(t)^2` with `V(0) = -1` |
| `gradient_eq_neg_one_div` | `V(t) = -1/(1-t)` (exact Riccati solution) |
| `not_isRegularSolution_initialRamp` | No C^2 solution reaches `t = 1` (algebraic contradiction) |

### KdV -- exact soliton and conservation laws

| Theorem | Statement |
|---|---|
| `travellingWave_reduction` | Travelling-wave ansatz reduces KdV to `-c f' + f f' + f''' = 0` |
| `soliton_satisfies_kdv` | `3c sech^2(sqrt(c)/2 x)` satisfies the soliton ODE for all `c > 0` |
| `massRate_conserved` | `d/dt integral u = 0` for compactly supported smooth solutions |
| `energyRate_conserved` | `d/dt integral u^2 = 0` for compactly supported smooth solutions |

## Architecture

```
M4TH/
  README.md                 <-- this file
  LICENSE                   (Apache 2.0)
  CONTRIBUTING.md
  CITATION.cff
  CHANGELOG.md

  M4THDocs/
    Hyperbolic_Dispersive_PDE_in_Lean4.md   (companion paper, CC-BY 4.0)

  BurgersBlowUp/          Gradient blow-up for the inviscid Burgers equation
    README.md
    lakefile.toml
    BurgersBlowUp.lean
    BurgersBlowUp.svg
    BurgersBlowUp/          (Calculus, ODE, Characteristics, BlowUp)
    BurgersBlowUpLive/      (single-file live version + mathematical manual)

  ConservationLaws/       Weak solutions and shock theory
    README.md
    lakefile.toml
    ConservationLaws.lean
    ConservationLaws.svg
    ConservationLaws/       (TestFunction, WeakSolution, Galilean,
                             ShockProfile, ShockReduction, Burgers)
    ConservationLawsLive/   (single-file live version + mathematical manual)

  KdV/                    Exact soliton and conservation laws
    README.md
    lakefile.toml
    KdV.lean
    KdV.svg
    KdV/                    (Basic, Hyperbolic, Soliton, ConservationLaws)
    KdVLive/                (single-file live version + mathematical manual)
```

## Live versions

Each package includes a `*Live/` subfolder with:

- `*.live.lean` -- a single self-contained file fusing all modules, for web
  reading and independent verification.
- `*.live.MANUAL.md` -- a mathematical exposition in theorem-style format.

## Paper

The companion paper `M4THDocs/Hyperbolic_Dispersive_PDE_in_Lean4.md`
provides the full mathematical context, references, and formalisation notes.

## Related work

- S. Armstrong et al., *A formalisation of the De Giorgi-Nash-Moser theorem in
  Lean* (2026). The first non-trivial PDE regularity result in a proof assistant;
  this work is complementary, addressing evolutionary hyperbolic and dispersive
  equations.
- The Mathlib library: <https://github.com/leanprover-community/mathlib4>

## Requirements

- Lean 4 (v4.31.0 or later)
- Mathlib (pinned per package via `lakefile.toml`)
- macOS / Linux / Windows

## License

- Software (`.lean`, `.toml`): Apache License 2.0 -- see [LICENSE](LICENSE).
- Documentation and paper (`.md`): CC-BY 4.0.

## Citation

If you use this work in academic research, please cite the companion paper and
the repository:

```bibtex
@software{M4TH_v1.0.0,
  title     = {Hyperbolic and Dispersive 1D PDE in Lean 4:
               Weak Solutions, Shock Waves, Gradient Blow-up, and Solitons},
  author    = {Izquierdo P{\'{e}}rez, Bezalel},
  orcid     = {0009-0001-5993-4057},  doi       = {10.5281/zenodo.21635317},  year      = {2026},
  version   = {v1.0.0},
  url       = {https://github.com/Alektronnik/M4TH}
}
```

See [CITATION.cff](CITATION.cff) for the full metadata.
