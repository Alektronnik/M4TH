# Changelog

All notable changes to the M4TH formalisation packages.

## [2.0.0] -- 2026-07-28

### Added
- `DirichletEta` package: Dirichlet eta function and non-vanishing of ζ on (0,1)
  - `Basic.lean`: alternating series, `η(s) = (1-2^{1-s})ζ(s)` for `Re(s) > 0`
  - `Analytic.lean`: analytic continuation of `η`
  - `Nonvanishing.lean`: `ζ(x) ≠ 0` for all `x ∈ (0,1)`
- `ZetaZeroCounting` package: Riemann-von Mangoldt zero-counting infrastructure
  - `Xi.lean`: completed xi function, nontrivial zeros, symmetry
  - `ZeroCounting.lean`: `N(T)` with multiplicities, finiteness
  - `SafeHeights.lean`: safe height enclosures, density
  - `MainTerm.lean`: von Mangoldt main term and asymptotics
- `XiLogResidue` package: logarithmic residue = multiplicity
  - `Basic.lean`: meromorphy of `Ξ`, log-derivative on the critical box
  - `LocalResidue.lean`: residue equals `analyticOrderNatAt`
  - `Divisor.lean`: dictionary with `MeromorphicOn.divisor` (bridge to ProjectVD)
- `XiLogDeriv` package: expansion of `Ξ'/Ξ` and digamma identity
  - `Basic.lean`: three-component log-derivative expansion
  - `GammaR.lean`: non-vanishing and differentiability of `Γ_ℝ`
  - `DigammaContinuity.lean`: continuity of digamma away from poles
  - `Expansion.lean`: closed identity for `Γ_ℝ` via digamma
- Paper `Riemann_von_Mangoldt_in_Lean4.md` in `M4THDocs/`
- Live single-file variants and mathematical manuals for each new package
- Native Lean-generated SVG cover figures per new package

### Changed
- README header, package table, axiom certificate, and citation updated to reflect 7 packages
- CITATION.cff updated to v2.0.0 with expanded abstract and keywords
- `lakefile.toml` Mathlib revision pinned to `fabf563a` across all 7 packages
- Build instructions simplified (no manual pin step)

### Verification
- Zero `axiom`, zero `sorry` across all 7 packages (20 source modules)
- Every headline theorem: `[propext, Classical.choice, Quot.sound]`

### Known Limitations
- Mathlib revision pinned to `fabf563a` (Lean 4 v4.31.0); update `lakefile.toml` when migrating to newer Mathlib
- Import lists not yet minimised with import linter (flagged for PR review)
- `set_option maxHeartbeats 600000` in `KdV/Soliton.lean` (computationally heavy derivative proofs)

## [1.0.0] -- 2026-07-28

### Added
- `ConservationLaws` package: weak solutions of scalar conservation laws
  - `TestFunction.lean`: test function structure, partial derivatives, improper FTC
  - `WeakSolution.lean`: weak residual, `IsWeakSolution` for arbitrary flux
  - `Galilean.lean`: Galilean change of frame, Fubini cancellations on half-planes
  - `ShockProfile.lean`: travelling step, Rankine-Hugoniot condition, shock classification
  - `ShockReduction.lean`: exact reduction of shock residual to R-H jump (`hasShockIntegralReduction`)
  - `Burgers.lean`: Burgers flux, Lax entropy pair, entropy dissipation, non-uniqueness pathology
- `BurgersBlowUp` package: finite-time gradient blow-up for inviscid Burgers
  - `Calculus.lean`: Frechet derivative decomposition, chain rule along plane curves
  - `ODE.lean`: Lyapunov-energy uniqueness, exact Riccati solution
  - `Characteristics.lean`: `IsRegularSolution`, constancy along characteristics
  - `BlowUp.lean`: Riccati gradient evolution, exact formula, blow-up theorem
- `KdV` package: exact one-soliton profile and conservation laws
  - `Basic.lean`: `IsSolution`, `TravellingWave`, travelling-wave reduction
  - `Hyperbolic.lean`: `sech`, `solitonProfile`, hyperbolic-function calculus
  - `Soliton.lean`: explicit derivatives, `soliton_satisfies_kdv`
  - `ConservationLaws.lean`: mass and energy conservation rates
- Live single-file variants for each package (web/Zulip reading)
- Live mathematical manuals in theorem-style format
- Companion paper: `Hyperbolic_Dispersive_PDE_in_Lean4.md`
- Native Lean-generated SVG cover figures per package
- `README.md`, `LICENSE` (Apache 2.0), `CONTRIBUTING.md`, `CITATION.cff`, `.gitignore`

### Verification
- Zero `axiom`, zero `sorry` across all 13 source modules
- Every headline theorem: `[propext, Classical.choice, Quot.sound]`
- Packages organised as standalone Mathlib-style contributions with linear PR dependency chains

### Known Limitations
- Mathlib revision pinned to `fabf563a` (Lean 4 v4.31.0); update `lakefile.toml` when migrating to newer Mathlib
- Import lists not yet minimised with import linter (flagged for PR review)
- Four calculus helpers duplicated between `ConservationLaws` and `BurgersBlowUp` (intentional; to be submitted once as shared Mathlib PR)
- `set_option maxHeartbeats 600000` in `KdV/Soliton.lean` (computationally heavy derivative proofs)
