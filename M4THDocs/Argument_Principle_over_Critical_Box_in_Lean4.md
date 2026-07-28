# The Riemann–von Mangoldt Formula in Lean 4

## Argument Principle over the Critical Box, Asymptotic Synthesis, and a Discrete Abel–Chebyshev Bridge

**Author.** Bezalel Izquierdo Pérez — ORCID [0009-0001-5993-4057](https://orcid.org/0009-0001-5993-4057)
**Code.** <https://github.com/Alektronnik/M4TH> — packages `XiArgumentPrinciple`, `XiAsymptoticFrontier`, `DiscreteAbelChebyshev`
**License.** Apache 2.0 (software), CC-BY 4.0 (text)
**Verification.** Lean 4 over Mathlib. Zero `axiom`, zero `sorry`. Every displayed theorem carries a clean axiom certificate (`[propext, Classical.choice, Quot.sound]`).

---

## Abstract

We report a self-contained formalisation, in the Lean 4 proof assistant on top of
Mathlib, of the argument-principle skeleton of the Riemann–von Mangoldt zero-counting
formula. Three packages complete the arc opened by the v2.0.0 release, which built the
counting function `N(T)`, the safe-height apparatus, and the logarithmic-residue/multiplicity
dictionary, and left the counting formula itself as a typed proposition. The first package,
`XiArgumentPrinciple`, defines the contour integral of the logarithmic derivative of the
entire Xi variant over the four edges of the critical box, proves the *unconditional*
algebraic identity that this contour integral equals the corresponding rectangle integral,
and packages the Cauchy-index counting step as a theorem conditional on an explicit typed
bridge. The second, `XiAsymptoticFrontier`, introduces a typed analytic frontier — a
structure recording exactly which contour contributions are negligible and which supplies
the main term — and proves that, under that frontier, the multiplicity counting function is
asymptotically equivalent to the classical von Mangoldt main term `(T/2π)(log(T/2π) − 1)`.
The third, `DiscreteAbelChebyshev`, proves the finite Abel summation identity outright and
applies it to a discrete Chebyshev-to-prime-counting bridge whose residual estimate is kept
as an explicit hypothesis. Crucially, **all three packages depend only on Mathlib**: the
external analytic ingredient that the classical proof would import — the rectangular residue
theorem — is exposed as typed hypotheses rather than as a library dependency, keeping the
entire M4TH series on a single, uniform, publication-safe foundation.

---

## 1. Introduction

The v2.0.0 release of M4TH, "Riemann–von Mangoldt in Lean 4", built the scaffolding of the
zero-counting theory: the counting function `N(T)` with multiplicities, the density of safe
heights, and a bidirectional dictionary between the logarithmic residue of `Ξ′/Ξ` and
Mathlib's `MeromorphicOn.divisor`. That release deliberately recorded the Riemann–von
Mangoldt counting formula itself as a typed proposition and never assumed it, because its
proof belongs to the argument-principle argument over the critical box. The present release
supplies exactly that argument, in the only form that keeps the library uniform: an
argument-principle *skeleton* whose single non-elementary input is named and typed, not
imported.

The design decision that governs this release is worth stating first, because it departs
from the obvious route. The classical proof integrates `Ξ′/Ξ` around the critical box and
invokes the argument principle to equate the winding number with the number of enclosed
zeros; formalising that step directly would require a rectangular residue theorem that is
not yet in Mathlib and lives, in partial form, in external developments such as
`PrimeNumberTheoremAnd`. Importing such a dependency would break the "Mathlib-only"
invariant that all eight previously published M4TH packages satisfy. We therefore do not
import it. Instead, the exact analytic facts the classical proof would use — Cauchy index
`+1` inside the box, index `0` outside, residue sum equal to the multiplicity sum — are
recorded as fields of an explicit `Prop`-valued structure, and every counting theorem is
stated conditionally on it. The skeleton is thus complete and unconditional *as
mathematics about the interface*, while the interface itself is a named target for a future
Mathlib or PNT+ rectangular-residue contribution.

Three theorems organise the development.

1. **The contour equals the rectangle** (Section 3). Over the four parametrised edges of the
   critical box, the contour integral of `entireXiLogDeriv` equals the rectangle integral of
   the same integrand. This is proved unconditionally and is the algebraic backbone of the
   argument principle.

2. **Winding equals count** (Section 3). Under the typed `ArgumentPrincipleBridge`, the
   contour integral equals `2πi` times the multiplicity-counting function, so the winding
   number counts the zeros in the box.

3. **Counting is asymptotic to the main term** (Section 4). Under the typed
   `AnalyticFrontier`, the multiplicity counting function is equivalent at infinity to the
   von Mangoldt main term `(T/2π)(log(T/2π) − 1)`.

A fourth, elementary strand (Section 5) formalises discrete Abel summation and applies it to
a Chebyshev-to-prime bridge, closing the counting arc on the arithmetic side.

### 1.1 Contributions

- The first formalisation of the **critical-box contour integral** of the Xi
  log-derivative over explicit edge parametrisations, together with the unconditional
  identity `entireXiContourIntegral T = criticalBoxRectangleIntegral entireXiLogDeriv T`.
- A **typed argument-principle bridge** `ArgumentPrincipleBridge` that isolates the
  rectangular-residue input as three named fields, and the conditional counting theorem
  `contour_winding_equals_count_of_safe`.
- A **typed analytic frontier** `AnalyticFrontier` for the contour synthesis, and the
  conditional Riemann–von Mangoldt equivalence
  `riemann_von_mangoldt_from_contour_frontier : N ~ vonMangoldtMainTerm`.
- The first M4TH formalisation of **finite Abel summation** `abel_summation` and its
  application to a discrete Chebyshev bridge, with the residual estimate exposed as the
  typed hypothesis `ChebyshevErrorSumBound`.
- A demonstration that the argument-principle arc can be completed **without leaving the
  Mathlib-only foundation**, by typing the external ingredient rather than importing it.

### 1.2 Non-goals

We do not prove the rectangular residue theorem, and therefore do not discharge
`ArgumentPrincipleBridge`, `AnalyticFrontier`, or `ChebyshevErrorSumBound`; these are the
explicit analytic frontier of the release. We do not prove the Riemann Hypothesis, establish
zero-free regions, or supply the Stirling/gamma asymptotics that would make the frontier
fields theorems. These are the natural next steps, and each is a named `Prop` that a
subsequent development can target one field at a time.

### 1.3 Relation to earlier releases

This is the fourth major release of M4TH, after v1.0.0 (hyperbolic and dispersive PDE),
v2.0.0 (Riemann–von Mangoldt zero counting, logarithmic residues, digamma identity), and
v3.0.0 (Mertens' theorems, the Meissel–Mertens constant, compensated Euler-product
convergence). It is the direct continuation of v2.0.0: where that release *defined* the
counting function and *stated* the counting formula, this one supplies the argument-principle
machinery that connects the two, conditional on the typed analytic bridges. As with every
earlier release, the packages depend only on Mathlib and share no code, so each can be
reviewed, built, and upstreamed independently.

---

## 2. Setting and Mathlib background

All three packages are stated over the complex numbers (for the contour packages) and the
reals (for the Abel–Chebyshev package), using only core Mathlib: `completedRiemannZeta₀` and
`riemannZeta` for the zeta side; `Differentiable`, `AnalyticAt`, `analyticOrderAt`, and
`MeromorphicOn.divisor` for the complex-analytic side; `intervalIntegral` for the contour
integrals; the `Asymptotics.IsEquivalent` and `IsLittleO` API with the `atTop` filter for the
asymptotics; and `Finset.sum_range`, `IsPrimePow`, and `Nat.minFac` for the discrete side.
The entire Xi variant is the same one used throughout the series,

```lean
noncomputable def entireXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1
```

nonvanishing at the corners `0, 1` and agreeing with `s (s − 1) completedRiemannZeta s` on
the open critical strip. The public namespaces are `RiemannArgumentPrinciple`,
`RiemannAsymptoticFrontier`, and `DiscreteAbelChebyshev`.

---

## 3. XiArgumentPrinciple — the contour and the counting step

The critical box `{0 ≤ Re s ≤ 1, 0 ≤ Im s ≤ T}` is given with its four edges, its interior,
and the safe-height predicate `IsSafeHeight T`, which asserts that no nontrivial zero lies on
the top edge. Each edge is parametrised, and the contour integral of the Xi log-derivative is
the oriented sum of the four edge integrals:

```lean
noncomputable def entireXiContourIntegral (T : ℝ) : ℂ :=
  entireXiBottomEdgeIntegral + entireXiRightEdgeIntegral T +
    entireXiTopEdgeIntegral T + entireXiLeftEdgeIntegral T
```

The first main theorem is unconditional and purely algebraic: the contour integral equals
the rectangle integral of the same integrand.

```lean
theorem entireXiContourIntegral_eq_rectangleIntegral (T : ℝ) :
    entireXiContourIntegral T = criticalBoxRectangleIntegral entireXiLogDeriv T
```

The counting step is where the classical proof invokes the argument principle. Rather than
assume a rectangular residue theorem, the package records its exact content as a typed
structure,

```lean
structure ArgumentPrincipleBridge (T : ℝ) : Prop where
  index_one : ∀ {w : ℂ}, w ∈ criticalBoxInterior T →
    contourCauchyIndexIntegral w T = 2 * Real.pi * I
  index_zero : ∀ {w : ℂ}, w ∉ criticalBox T →
    contourCauchyIndexIntegral w T = 0
  residue_sum :
    entireXiContourIntegral T / (2 * Real.pi * I) = entireXiCriticalBoxResidueSum T
```

and proves the counting theorem conditionally on it:

```lean
theorem contour_winding_equals_count_of_safe {T : ℝ} (hT : 0 < T)
    (hSafe : IsSafeHeight T) (hBridge : ArgumentPrincipleBridge T) :
    ContourWindingEqualsCount T
```

whose payload is `entireXiContourIntegral T = 2πi · zeroCountingWithMultiplicity T`. The
package also proves the companion index statements
`contour_winding_index_one_of_safe` and `contour_residue_sum_equals_N_of_safe`, and an
`Eventually` version quantifying over safe heights above any given height. Of its eleven
theorems, the contour/rectangle identity and the index-equivalence lemmas are unconditional;
only the three winding/residue counting statements carry the `ArgumentPrincipleBridge`
hypothesis, and they carry it explicitly.

---

## 4. XiAsymptoticFrontier — from the contour to the main term

The synthesis package answers the question the counting step raises: once the contour counts
the zeros, why is the count asymptotic to `(T/2π)(log(T/2π) − 1)`? The answer is a
bookkeeping of contour contributions. A `ContourComponents` record splits the boundary
integral into named pieces — near-origin, polynomial horizontal/vertical, gamma
horizontal/vertical, zeta horizontal/vertical — and the typed frontier records which pieces
are negligible and which supplies the main term:

```lean
structure AnalyticFrontier (N Nsafe : ZeroCountingFunction) (C : ContourComponents) : Prop where
  reconstructs_safe : C.reconstructs Nsafe
  near_origin : NearOriginNegligible C
  polynomial : PolynomialContourNegligible C
  gamma_horizontal : GammaHorizontalStirlingGoal C
  gamma_vertical : GammaVerticalEdgesNegligible C
  zeta_edges : ZetaEdgesNegligible C
  safe_height_counting : SafeHeightCountingEquivalent N Nsafe
```

The negligibility of the residual follows from the individual negligibility fields
(`residual_negligible`), and the main synthesis theorem concludes that the counting function
is equivalent to the von Mangoldt main term:

```lean
theorem riemann_von_mangoldt_from_contour_frontier {N Nsafe : ZeroCountingFunction}
    {C : ContourComponents} (h : AnalyticFrontier N Nsafe C) :
    RiemannVonMangoldtMultiplicityCounting N
```

where `RiemannVonMangoldtMultiplicityCounting N` unfolds to `IsEquivalent atTop N
vonMangoldtMainTerm`. The reusable point-free form `riemann_von_mangoldt_from_contour_bridge`
packages the same implication as a single `Prop`. All four theorems of the package are
proved; the mathematics they leave open is entirely inside the frontier fields — the
Stirling asymptotics of the gamma term and the negligibility of the zeta edges — each a named
target rather than an assumption buried in a proof.

---

## 5. DiscreteAbelChebyshev — the arithmetic bridge

The third package closes the arc on the arithmetic side with the elementary tool the
counting theory ultimately rests on: summation by parts. The finite Abel identity is proved
outright,

```lean
lemma abel_summation (a f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, a n * f n =
      sumSeq a N * f N - ∑ n ∈ range N, sumSeq a (n + 1) * (f (n + 1) - f n)
```

and applied with `a = Λ` (the von Mangoldt weight `mangoldt`) and `f = 1/log`, giving an
exact decomposition of the prime-counting proxy into a main integral term, a boundary term,
and a residual error term (`pi_approx_final`). The per-step variation of the reciprocal
logarithm is bounded unconditionally,

```lean
lemma invLog_diff_bound (n : ℕ) (hn : n ≥ 2) :
    |invLog (n + 1) - invLog n| ≤ 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)
```

and the final transfer theorem — that a Chebyshev bound on `ψ(N) − N` yields the prime-error
estimate — is stated conditionally on the two explicit frontier hypotheses
`IsChebyshevBounded` and `ChebyshevErrorSumBound`:

```lean
theorem chebyshev_implies_prime_error (C : ℝ) (N₀ : ℕ) (hC : 0 ≤ C)
    (h_bound : IsChebyshevBounded C N₀) (h_sum : ChebyshevErrorSumBound C N₀)
    (N : ℕ) (hN : N ≥ max N₀ 2) : …
```

The package is small by design — one headline theorem over seventeen supporting lemmas — but
it supplies the summation-by-parts identity that the counting synthesis and any future
prime-counting refinement will reuse, and it is a natural first Mathlib PR to compare against
`Mathlib.NumberTheory.AbelSummation`.

---

## 6. Formalisation notes

**Typed interfaces instead of external dependencies.** The single design principle of this
release is that the non-elementary analytic inputs are represented as `Prop`-valued
structures — `ArgumentPrincipleBridge`, `AnalyticFrontier`, `ChebyshevErrorSumBound`,
`IsChebyshevBounded` — appearing as explicit hypotheses of the conditional theorems. This
keeps all three packages Mathlib-only, preserves the zero-axiom certificate, and turns each
missing analytic fact into a named, individually dischargeable target. The plan anticipated a
`PrimeNumberTheoremAnd` lake dependency for the rectangular residue; the released code avoids
it entirely.

**What is unconditional.** The contour/rectangle identity
(`entireXiContourIntegral_eq_rectangleIntegral`), the index-equivalence lemmas, finite Abel
summation (`abel_summation`), the reciprocal-logarithm bound (`invLog_diff_bound`), and the
exact Abel decomposition (`pi_approx_final`) are all proved outright. What is conditional —
winding equals count, counting equals the main term, Chebyshev implies the prime error — is
conditional on the typed frontier and nothing else.

**No axioms, no `sorry`, no `native_decide`.** Every result is kernel-checked; the axiom
certificate of each headline theorem is exactly `[propext, Classical.choice, Quot.sound]`.

**Independence and PR partition.** Each package has its own `lakefile.toml`
(pinned to Mathlib `fabf563a`, Lean 4 v4.31.0) and its own module chain, and can be built
independently. `XiArgumentPrinciple` and `XiLogResidue` are kept separate on purpose; their
shared `criticalBox` and `entireXi` definitions are resolved at Mathlib-PR time by a single
shared PR, exactly as with the `ConservationLaws`/`BurgersBlowUp` pair.

---

## 7. Related work

The Prime Number Theorem was formalised in Isabelle/HOL by Avigad et al. (2007) and in Lean 4
(Han, 2026), and the `PrimeNumberTheoremAnd` project develops, among other things, the
rectangular contour and residue machinery this release deliberately abstracts behind a typed
bridge. The divisor formalism `MeromorphicOn.divisor` used to phrase the multiplicity count
was developed in Mathlib and is employed in ProjectVD (Kebekus). The present work is
complementary to all three: rather than importing a contour-residue library, it fixes the
precise interface such a library must supply and proves the argument-principle counting and
asymptotic-synthesis theorems relative to that interface, so that the eventual dependency is a
theorem substitution rather than a re-architecture. Classical references for the mathematics
are Edwards's monograph [2], Titchmarsh's treatise [4], and Davenport [1]; the discrete
Abel/Chebyshev material follows Apostol [0] and Tenenbaum [3].

---

## 8. Availability

The three packages are available at <https://github.com/Alektronnik/M4TH> under the Apache 2.0
license, each with its own `lakefile.toml` (pinned to Mathlib `fabf563a`, Lean 4 v4.31.0), a
native Lean-generated SVG cover figure, and a `Live` single-file study version. After a
successful build the axiom certificate of each headline theorem may be reproduced with

```
#print axioms RiemannArgumentPrinciple.entireXiContourIntegral_eq_rectangleIntegral
#print axioms RiemannArgumentPrinciple.contour_winding_equals_count_of_safe
#print axioms RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_frontier
#print axioms RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_bridge
#print axioms DiscreteAbelChebyshev.abel_summation
#print axioms DiscreteAbelChebyshev.chebyshev_implies_prime_error
```

each returning `[propext, Classical.choice, Quot.sound]`.

---

## References

0. T. M. Apostol, *Introduction to Analytic Number Theory*, Springer, 1976.
1. H. Davenport, *Multiplicative Number Theory*, Springer, 3rd ed., 2000.
2. H. M. Edwards, *Riemann's Zeta Function*, Academic Press, 1974; Dover reprint, 2001.
3. G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, AMS, 3rd ed.,
   2015.
4. E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, Oxford, 2nd ed., 1986.
5. The mathlib Community, *The Lean Mathematical Library*, CPP 2020;
   <https://github.com/leanprover-community/mathlib4>.
