# Changelog

All notable changes to the M4TH formalisation packages.

## [6.0.0] -- 2026-07-29

### Added
- `Poincare4D`: smooth surgery chains, coupled Ricci-gauge flow contracts,
  and conditional smooth 4D Poincare theorem (2658-line live file, zero
  `sorry`/`axiom`/`native_decide`).  Analytic PDE inputs are explicit typed
  hypotheses; no package-local axioms.

## [5.5.0] -- 2026-07-29

### Added
- `M4THProtocol.md` in `M4THDocs/`: complete protocol fusing T-ORIK4 package
  standard and live-layer standard, adapted for the M4TH monorepo
- `.web.lean` single-file variants for 5 packages requiring v4.33.0-rc1
  compatibility: MertensPNT, PrimeGapsSophie, XiArgumentPrinciple,
  XiLogResidue, ZetaZeroCounting
- `.web.README.md` alongside each `.web.lean` documenting API name
  changes and version-specific fixes
- `M4TH.sh` web mode (`./M4TH.sh web [Pkg]`) for batch compilation of
  `.web.lean` files

### Changed
- API names in `.web.lean` files updated for v4.33.0-rc1:
  `Set.mem_setOf_eq` -> `Set.mem_ofPred_eq`,
  `Nat.infinite_setOf_prime` -> `Nat.infinite_setOfPred_prime`,
  `ENat.map_coe` -> `ENat.map_natCast`,
  `Nat.cast_zero` -> `ENat.natCast_zero`
- `MertensPNT.web.lean`: `dsimp` replaced by explicit `rfl` for
  `natPrimesEquiv` (structure projection reduction changed in v4.33.0-rc1)
- `M4TH.sh`: log simplified to single `M4TH.log`, overwritten each run,
  no `logs/` directory
- `M4TH.sh clean`: only removes `M4TH.log`
- `.gitignore`: blinded to prevent Lake artifacts leaking into packages
- SVG generators: `repositoryOutputDir` paths fixed from `M4TH/PackageName`
  to `PackageName` (graphical SVG still uses package root)
- `SU3Concrete/Representation.lean`: merged with T-ORIK4 version, direct
  `structureConstant` usage instead of `commutatorStructureCoeff` wrapper
- Per-package `lakefile.toml`: restored with `# PIN OBLIGATORIO` comment

### Verification
- Zero `sorry`, zero `axiom` across all 15 packages
- Every headline theorem: `[propext, Classical.choice, Quot.sound]`
- All 5 `.web.lean` files use v4.33.0-rc1 API names (compile on v4.33 web
  environment; fail locally on v4.31.0 as expected)
- `M4TH.sh live` passing (15/15), `M4TH.sh web` passing for web-enabled
  packages on v4.33.0-rc1 environment
- All 15 `.live.lean` aligned with source modules (SU3Concrete Representation
  section regenerated, XiLogResidue/ZetaZeroCounting/MertensPNT tactics
  restored to source)

## [5.0.0] -- 2026-07-29

### Added
- `SU3Concrete` package: concrete su(3) from Gell-Mann matrices (45 theorems)
  - `GellMann.lean`: anti-Hermitian generators `Tᵃ = iλₐ`
  - `LieAlgebra.lean`: matrix commutator Lie algebra, trace-zero conditions
  - `StructureConstants.lean`: explicit `f^{abc}`, antisymmetry, Jacobi identity
  - `Commutator.lean`: generator commutator matrix identities
  - `Representation.lean`: adjoint Casimir `= -3·I₈`, Killing form `κ = -3δ`, fundamental Casimir `= -(16/3)·I₃`
- `SU3Wilson` package: SU(3) trace bound and Wilson action positivity (18 theorems)
  - `SU3.lean`: concrete SU(3) group, normalised trace bound `-1 ≤ Re(tr U)/3 ≤ 1`
  - `Wilson.lean`: plaquette terms in `[0,2]`, Wilson action nonnegative
  - `Lattice4D.lean`: constructive 4D lattice, `WilsonAction4D_nonneg`
- `CertifiedElliptic5077` package: certified LMFDB curve 5077a1 (27 theorems)
  - `Basic.lean`: short Weierstrass layer, coordinate transforms
  - `IntegralModel.lean`: discriminant `Δ = 5077`, integral-to-short change
  - `FiniteFieldCounts.lean`: `N₂ = 5`, `N₃ = 7`, `N₅ = 10` (kernel `decide`)
  - `Entry5077a1.lean`: explicit rational points, certified doublings
- `PrimeGapsSophie` package: Sophie Germain primes and higher-order gap parity (9 theorems)
  - `SophieGermain.lean`: `p ≡ 2 (mod 3)`, `p ≡ 5 (mod 6)` for Sophie Germain primes
  - `PrimeGap.lean`: ordinary prime gaps are even
  - `HigherOrder.lean`: nth-order finite differences are even for odd primes
- Paper `Four_Certified_Formalisations_in_Lean4.md` in `M4THDocs/`
- Native Lean-generated SVG cover figures for all 4 new packages
- All generators aligned: `esc body`, paths, `lean-toolchain`, `lake-manifest.json`

### Changed
- README, CHANGELOG, CITATION updated for 15 packages across 5 releases
- `PrimeGapsSophie`: `textAt`/`line` now accept `extra` param, `arrowMarker` added
- All 4 new packages: output paths corrected from `M4TH` to `M4TH`
- Live MANUAL files: T-ORIK4 paths corrected to M4TH

### Verification
- Zero `axiom`, zero `sorry` across all 15 packages
- Every headline theorem: `[propext, Classical.choice, Quot.sound]`
- All 15 SVGs valid XML, generated from Lean code

## [4.0.0] -- 2026-07-28

### Added
- `XiArgumentPrinciple` package: critical-box argument-principle chain for the Xi variant
  - `Basic.lean`: entire Xi variant, critical box, nontrivial zeros, multiplicity
  - `Contour.lean`: edge parametrisations, contour/rectangle integral identity (unconditional)
  - `Counting.lean`: `ArgumentPrincipleBridge` typed structure, conditional winding = count theorem
- `XiAsymptoticFrontier` package: typed analytic frontier for contour synthesis
  - `Basic.lean`: von Mangoldt main term, contour components, normalised real parts
  - `Frontier.lean`: `AnalyticFrontier` structure (7 fields), residual negligibility lemma
  - `Synthesis.lean`: conditional Riemann-von Mangoldt equivalence theorem
- `DiscreteAbelChebyshev` package: finite Abel summation and Chebyshev-to-prime bridge
  - `Basic.lean`: `abel_summation` identity, Mangoldt/psi/invLog definitions
  - `ChebyshevBridge.lean`: exact Abel decomposition, typed `ChebyshevErrorSumBound` frontier
- Paper `Argument_Principle_over_Critical_Box_in_Lean4.md` in `M4THDocs/`
- Native Lean-generated SVG cover figures for all 3 new packages
- `lake-manifest.json` added to all 11 packages for reproducible builds
- All SVG generators aligned: `esc body` fix, arrow markers, standard sizes, balanced layouts

### Changed
- `DirichletEta.svg`: 6 publication-quality corrections (ticks, labels, legend, footer)
- `DiscreteAbelChebyshev.svg`: 7 layout corrections (V-flow arrows, panel sizing, formula fit)
- `XiArgumentPrinciple.svg`: 8 alignment corrections (esc body, rotation, marker, sizing)
- `XiAsymptoticFrontier.svg`: 5 alignment corrections (esc body, arrows, footer)
- `.gitignore`: scoped `lake-manifest.json` to root only (preserves package-level manifests)
- README, CITATION.cff updated for 11 packages across 4 releases

### Verification
- Zero `axiom`, zero `sorry` across all 11 packages (35 source modules)
- Every headline theorem: `[propext, Classical.choice, Quot.sound]`
- All 11 SVGs valid XML, generated from Lean code

## [3.0.0] -- 2026-07-28

### Added
- `MertensPNT` package: Meissel-Mertens constant, compensated convergence, conditional PNT+ closure
  - `Basic.lean`: prime harmonic sums, Chebyshev bounds, reciprocal estimates
  - `Connections.lean`: bridges between prime sums and Chebyshev functions
  - `ErdosBlocks.lean`: Erdos block iteration with explicit rate
  - `MertensBridge.lean`: exact identities linking Euler product and prime sums
  - `MertensConstant.lean`: Meissel-Mertens constant definition and sumability
  - `PNTFrontier.lean`: conditional closure over PNT+, typed frontier pattern
  - `TTAOData.lean`: certified empirical brackets (wheel sieves, primorial products)
- Live single-file variant and mathematical manual for MertensPNT
- Native Lean-generated SVG cover figure

### Changed
- README package table, axiom certificate, theorems, and architecture tree updated for 8 packages
- CITATION.cff updated to v3.0.0

### Verification
- Zero `axiom`, zero `sorry` across all 8 packages (27 source modules)
- Every headline theorem: `[propext, Classical.choice, Quot.sound]`

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
