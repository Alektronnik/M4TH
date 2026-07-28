# M4TH

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21635317.svg)](https://doi.org/10.5281/zenodo.21635317)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Lean 4](https://img.shields.io/badge/Lean-4-green.svg)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-latest-orange.svg)](https://github.com/leanprover-community/mathlib4)

**Formalised PDE and analytic number theory in Lean 4 -- weak solutions,
shock waves, Lax entropy, gradient blow-up, KdV solitons, Dirichlet eta,
Riemann zero-counting, logarithmic residues, digamma identities,
argument-principle contour chain, asymptotic von Mangoldt synthesis,
and discrete Abel-Chebyshev bridge.
Zero `sorry`, zero `axiom`. Every headline theorem:
`[propext, Classical.choice, Quot.sound]`.**

- Author: Bezalel Izquierdo Perez
- ORCID: [0009-0001-5993-4057](https://orcid.org/0009-0001-5993-4057)
- License: Apache 2.0 (software), CC-BY 4.0 (documentation)

---

## Packages

Eleven independent Lean 4 packages, each self-contained on top of Mathlib.
One mathematical idea per package, fully proved.

### v1.0.0 -- Hyperbolic and dispersive PDE

| Package | Theorem | Status |
|---|---|---|
| `ConservationLaws` | Travelling step is a weak solution iff Rankine-Hugoniot holds (arbitrary flux) | Proved |
| `BurgersBlowUp` | No C^2 solution of Burgers reaches `t = 1` for `u_0(x) = -x` | Proved |
| `KdV` | `3c sech^2(sqrt(c)/2 x)` is an exact soliton for all `c > 0` | Proved |

### v2.0.0 -- Riemann-von Mangoldt: zero counting and logarithmic residues

| Package | Theorem | Status |
|---|---|---|
| `DirichletEta` | `η(s) = (1-2^{1-s})ζ(s)` and non-vanishing of ζ on `(0,1)` | Proved |
| `ZetaZeroCounting` | `N(T)` with multiplicities, safe heights, von Mangoldt main term | Proved |
| `XiLogResidue` | Logarithmic residue = multiplicity; dictionary with `MeromorphicOn.divisor` | Proved |
| `XiLogDeriv` | Expansion of `Ξ'/Ξ`; digamma identity for `Γ_ℝ` | Proved |

### v3.0.0 -- Meissel-Mertens constant and compensated convergence

| Package | Theorem | Status |
|---|---|---|
| `MertensPNT` | Meissel-Mertens constant, compensated prime harmonic convergence, conditional PNT+ closure | Proved |

### v4.0.0 -- Argument principle, asymptotic synthesis, and discrete Abel-Chebyshev

| Package | Theorem | Status |
|---|---|---|
| `XiArgumentPrinciple` | Contour/rectangle integral identity; conditional winding = count via typed `ArgumentPrincipleBridge` | Proved |
| `XiAsymptoticFrontier` | Conditional Riemann-von Mangoldt equivalence via typed `AnalyticFrontier` (7 fields) | Proved |
| `DiscreteAbelChebyshev` | Finite Abel summation; Chebyshev-to-prime error transfer via typed `ChebyshevErrorSumBound` | Proved |

To our knowledge this is the first formalisation of weak solutions of
conservation laws, of Rankine-Hugoniot and Lax entropy conditions, of gradient
blow-up for a nonlinear PDE, of the KdV soliton, of the Riemann-von Mangoldt
zero-counting function, of the logarithmic-residue/multiplicity dictionary,
of the Meissel-Mertens constant with compensated convergence, of the
critical-box argument-principle contour chain for the entire Xi variant,
and of the typed analytic-frontier synthesis for the asymptotic counting formula,
in any major proof assistant.

## Quick start

Each package is an independent Lean 4 project. Choose one and build:

```bash
cd ConservationLaws   # or BurgersBlowUp, KdV, DirichletEta,
                      #    ZetaZeroCounting, XiLogResidue, XiLogDeriv,
                      #    MertensPNT, XiArgumentPrinciple,
                      #    XiAsymptoticFrontier, DiscreteAbelChebyshev

lake update
lake exe cache get
lake build
```

## Axiom certificate

After a successful build, verify zero `sorry` and zero `axiom`:

```bash
# v1.0.0
echo 'import ConservationLaws
#print axioms ConservationLaw.hasShockIntegralReduction' | lake env lean --stdin

echo 'import BurgersBlowUp
#print axioms Burgers.not_isRegularSolution_initialRamp' | lake env lean --stdin

echo 'import KdV
#print axioms KdV.soliton_satisfies_kdv' | lake env lean --stdin

# v2.0.0
echo 'import DirichletEta
#print axioms DirichletEta.zeta_real_open_interval_nonvanishing_from_eta' | lake env lean --stdin

echo 'import ZetaZeroCounting
#print axioms Riemann.zerosUpToIm_finite' | lake env lean --stdin

echo 'import XiLogResidue
#print axioms RiemannLogResidue.entireXi_divisor_finset_eq_zerosUpToImFinset' | lake env lean --stdin

echo 'import XiLogDeriv
#print axioms RiemannLogDeriv.gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma' | lake env lean --stdin

# v3.0.0
echo 'import MertensPNT
#print axioms ErdosReciprocals.mertens_product_convergence' | lake env lean --stdin

# v4.0.0
echo 'import XiArgumentPrinciple
#print axioms RiemannArgumentPrinciple.entireXiContourIntegral_eq_rectangleIntegral' | lake env lean --stdin

echo 'import XiArgumentPrinciple
#print axioms RiemannArgumentPrinciple.contour_winding_equals_count_of_safe' | lake env lean --stdin

echo 'import XiAsymptoticFrontier
#print axioms RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_frontier' | lake env lean --stdin

echo 'import DiscreteAbelChebyshev
#print axioms DiscreteAbelChebyshev.abel_summation' | lake env lean --stdin

echo 'import DiscreteAbelChebyshev
#print axioms DiscreteAbelChebyshev.chebyshev_implies_prime_error' | lake env lean --stdin
```

Each must report only `[propext, Classical.choice, Quot.sound]`.

## Theorems

### ConservationLaws -- scalar conservation laws

| Theorem | Statement |
|---|---|
| `hasShockIntegralReduction` | Residual collapses exactly to R-H deficit along the interface |
| `isWeakSolution_shockProfile_of_rankineHugoniot` | Step is weak solution iff Rankine-Hugoniot holds |
| `expansion_midpoint_is_weak_but_not_entropic` | Expansion step violates the Lax entropy condition |

### BurgersBlowUp -- gradient blow-up

| Theorem | Statement |
|---|---|
| `constant_along_characteristic` | `u` constant along `x = x_0(1-t)` |
| `gradient_riccati_evolution` | `V'(t) = -V(t)^2` with `V(0) = -1` |
| `gradient_eq_neg_one_div` | `V(t) = -1/(1-t)` (exact Riccati solution) |
| `not_isRegularSolution_initialRamp` | No C^2 solution reaches `t = 1` |

### KdV -- exact soliton and conservation laws

| Theorem | Statement |
|---|---|
| `travellingWave_reduction` | Travelling-wave ansatz reduces KdV to `-c f' + f f' + f''' = 0` |
| `soliton_satisfies_kdv` | `3c sech^2(sqrt(c)/2 x)` satisfies the soliton ODE for all `c > 0` |
| `massRate_conserved` | `d/dt integral u = 0` for compactly supported smooth solutions |
| `energyRate_conserved` | `d/dt integral u^2 = 0` for compactly supported smooth solutions |

### DirichletEta -- Dirichlet eta function

| Theorem | Statement |
|---|---|
| `eta_eq_zeta_of_re_gt_one` | `η(s) = (1-2^{1-s})ζ(s)` for `Re(s) > 1` |
| `zeta_real_open_interval_nonvanishing_from_eta` | `ζ(x) ≠ 0` for all `x ∈ (0,1)` |

### ZetaZeroCounting -- Riemann-von Mangoldt N(T)

| Theorem | Statement |
|---|---|
| `zerosUpToIm_finite` | Finite number of nontrivial zeros up to any finite height |
| `exists_safe_height_above` | Density of safe heights: every `(T, T+ε]` contains a height avoided by all zero ordinates |
| `T_isLittleO_vonMangoldtMainTerm` | `T = o` of the von Mangoldt main term `(T/2π)(log(T/2π)-1)` |

### XiLogResidue -- logarithmic residue = multiplicity

| Theorem | Statement |
|---|---|
| `entireXi_logDeriv_residue_eq_multiplicity` | Residue of `Ξ'/Ξ` at a zero equals its multiplicity |
| `entireXi_divisor_finset_eq_zerosUpToImFinset` | Divisor support = counted zeros; bridge to `MeromorphicOn.divisor` |

### XiLogDeriv -- expansion and digamma identity

| Theorem | Statement |
|---|---|
| `logDeriv_entireXiPolynomialFactor_eq` | Polynomial factor of `Ξ'/Ξ` |
| `gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma` | Digamma identity for `Γ_ℝ` |

### MertensPNT -- Meissel-Mertens constant and compensated convergence

| Theorem | Statement |
|---|---|
| `summable_mertensPrimeCorrection` | The correction series `∑_p (log(1-1/p)+1/p)` is summable, defining the Meissel-Mertens constant `M` |
| `tendsto_partialProduct_mul_exp_partialSum_add_gamma` | `∏(1-1/p)·e^{S(n)+γ} → e^M` (compensated convergence, unconditional) |
| `mertens_product_convergence` | The Euler product converges to zero with exact compensated rate |

### XiArgumentPrinciple -- critical-box argument-principle chain

| Theorem | Statement |
|---|---|
| `entireXiContourIntegral_eq_rectangleIntegral` | Contour integral of `Ξ′/Ξ` equals the rectangle integral (unconditional) |
| `contour_winding_equals_count_of_safe` | Under `ArgumentPrincipleBridge`, contour integral = `2πi·N(T)` |
| `contour_winding_index_one_of_safe` | Winding index = +1 for all zeros inside the critical box |

### XiAsymptoticFrontier -- typed analytic frontier

| Theorem | Statement |
|---|---|
| `riemann_von_mangoldt_from_contour_frontier` | Under `AnalyticFrontier`, `N(T) ~ (T/2π)(log(T/2π)−1)` |
| `riemann_von_mangoldt_from_contour_bridge` | Point-free Prop form of the same implication |
| `safe_counting_equiv_main` | Safe-height counting follows the main term under gamma dominance |

### DiscreteAbelChebyshev -- discrete Abel summation and Chebyshev bridge

| Theorem | Statement |
|---|---|
| `abel_summation` | `Σ a_n f_n = A_N f_N − Σ A_{n+1} Δf_n` (finite, exact, no limits) |
| `pi_approx_final` | Exact Abel decomposition of the weighted Mangoldt sum |
| `chebyshev_implies_prime_error` | Chebyshev bound + residual frontier → prime-counting error estimate |

## Architecture

```
M4TH/
  README.md                 <-- this file
  LICENSE                   (Apache 2.0)
  CONTRIBUTING.md
  CITATION.cff
  CHANGELOG.md

  M4THDocs/
    Hyperbolic_Dispersive_PDE_in_Lean4.md              (v1.0.0 paper, CC-BY 4.0)
    Riemann_von_Mangoldt_in_Lean4.md                   (v2.0.0 paper, CC-BY 4.0)
    Mertens_PNT_in_Lean4.md                            (v3.0.0 paper, CC-BY 4.0)
    Argument_Principle_over_Critical_Box_in_Lean4.md   (v4.0.0 paper, CC-BY 4.0)

  BurgersBlowUp/          Gradient blow-up for the inviscid Burgers equation
    README.md, lakefile.toml, BurgersBlowUp.lean, BurgersBlowUp.svg
    BurgersBlowUp/          (Calculus, ODE, Characteristics, BlowUp)
    BurgersBlowUpLive/      (single-file live version + mathematical manual)

  ConservationLaws/       Weak solutions and shock theory
    README.md, lakefile.toml, ConservationLaws.lean, ConservationLaws.svg
    ConservationLaws/       (TestFunction, WeakSolution, Galilean,
                             ShockProfile, ShockReduction, Burgers)
    ConservationLawsLive/   (single-file live version + mathematical manual)

  DirichletEta/           Dirichlet eta function and non-vanishing of ζ on (0,1)
    README.md, lakefile.toml, DirichletEta.lean, DirichletEta.svg
    DirichletEta/           (Basic, Analytic, Nonvanishing)
    DirichletEtaLive/       (single-file live version + mathematical manual)

  KdV/                    Exact soliton and conservation laws
    README.md, lakefile.toml, KdV.lean, KdV.svg
    KdV/                    (Basic, Hyperbolic, Soliton, ConservationLaws)
    KdVLive/                (single-file live version + mathematical manual)

  MertensPNT/             Meissel-Mertens constant and compensated convergence
    README.md, lakefile.toml, MertensPNT.lean, MertensPNT.svg
    MertensPNT/             (Basic, Connections, ErdosBlocks, MertensBridge,
                             MertensConstant, PNTFrontier, TTAOData)
    MertensPNTLive/         (single-file live version + mathematical manual)

  XiLogDeriv/             Log-derivative expansion of Ξ and digamma identity
    README.md, lakefile.toml, XiLogDeriv.lean, XiLogDeriv.svg
    XiLogDeriv/             (Basic, GammaR, DigammaContinuity, Expansion)
    XiLogDerivLive/         (single-file live version + mathematical manual)

  XiLogResidue/           Logarithmic residue = multiplicity; divisor dictionary
    README.md, lakefile.toml, XiLogResidue.lean, XiLogResidue.svg
    XiLogResidue/           (Basic, LocalResidue, Divisor)
    XiLogResidueLive/       (single-file live version + mathematical manual)

  ZetaZeroCounting/       Riemann-von Mangoldt N(T), safe heights, main term
    README.md, lakefile.toml, ZetaZeroCounting.lean, ZetaZeroCounting.svg
    ZetaZeroCounting/       (Xi, ZeroCounting, SafeHeights, MainTerm)
    ZetaZeroCountingLive/   (single-file live version + mathematical manual)

  XiArgumentPrinciple/    Critical-box argument-principle chain
    README.md, lakefile.toml, XiArgumentPrinciple.lean, XiArgumentPrinciple.svg
    XiArgumentPrinciple/    (Basic, Contour, Counting)
    XiArgumentPrincipleLive/ (single-file live version + mathematical manual)

  XiAsymptoticFrontier/   Typed analytic frontier for contour synthesis
    README.md, lakefile.toml, XiAsymptoticFrontier.lean, XiAsymptoticFrontier.svg
    XiAsymptoticFrontier/   (Basic, Frontier, Synthesis)
    XiAsymptoticFrontierLive/ (single-file live version + mathematical manual)

  DiscreteAbelChebyshev/  Discrete Abel summation and Chebyshev bridge
    README.md, lakefile.toml, DiscreteAbelChebyshev.lean, DiscreteAbelChebyshev.svg
    DiscreteAbelChebyshev/  (Basic, ChebyshevBridge)
    DiscreteAbelChebyshevLive/ (single-file live version + mathematical manual)
```

## Live versions

Each package includes a `*Live/` subfolder with:

- `*.live.lean` -- a single self-contained file fusing all modules, for web
  reading and independent verification.
- `*.live.MANUAL.md` -- a mathematical exposition in theorem-style format.

## Papers

- `M4THDocs/Hyperbolic_Dispersive_PDE_in_Lean4.md` (v1.0.0) -- hyperbolic and
  dispersive PDE: conservation laws, gradient blow-up, KdV solitons.
- `M4THDocs/Riemann_von_Mangoldt_in_Lean4.md` (v2.0.0) -- analytic number
  theory: Dirichlet eta, zero counting, logarithmic residues, digamma identity.
- `M4THDocs/Mertens_PNT_in_Lean4.md` (v3.0.0) -- Mertens' theorems,
  Meissel-Mertens constant, compensated convergence, conditional PNT+ closure.
- `M4THDocs/Argument_Principle_over_Critical_Box_in_Lean4.md` (v4.0.0) --
  argument principle over the critical box, asymptotic contour synthesis,
  discrete Abel-Chebyshev bridge.

## Related work

- S. Armstrong et al., *A formalisation of the De Giorgi-Nash-Moser theorem in
  Lean* (2026).
- D. Loeffler, M. Stoll, *Formalizing the Riemann zeta function in Mathlib*,
  arXiv:2503.00959 (2025).
- The Mathlib library: <https://github.com/leanprover-community/mathlib4>

## Requirements

- Lean 4 (v4.31.0 or later)
- Mathlib (pinned per package via `lakefile.toml` to `fabf563a`)
- macOS / Linux / Windows

## License

- Software (`.lean`, `.toml`): Apache License 2.0 -- see [LICENSE](LICENSE).
- Documentation and paper (`.md`): CC-BY 4.0.

## Citation

If you use this work in academic research, please cite:

```bibtex
@software{M4TH,
  title     = {M4TH: Formalised PDE and Analytic Number Theory in {Lean} 4},
  author    = {Izquierdo P{\'{e}}rez, Bezalel},
  orcid     = {0009-0001-5993-4057},
  doi       = {10.5281/zenodo.21635317},
  year      = {2026},
  version   = {v4.0.0},
  url       = {https://github.com/Alektronnik/M4TH}
}
```

See [CITATION.cff](CITATION.cff) for the full metadata.
