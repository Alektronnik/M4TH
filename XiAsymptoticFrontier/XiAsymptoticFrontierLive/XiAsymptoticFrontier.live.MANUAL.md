# XiAsymptoticFrontier.live

**Author:** Bezalel Izquierdo Pérez  
**License:** Apache 2.0  
**Live file:** `XiAsymptoticFrontier.live.lean`

---

## I. Purpose

This live file is the single-file study version of the `XiAsymptoticFrontier`
package.

It formalizes the final conditional layer of the Riemann-von Mangoldt contour
strategy: if the normalized contour expansion satisfies a typed analytic
frontier, then the zero-counting function is asymptotic to the classical
Riemann-von Mangoldt main term.

The package does not hide analytic estimates as trusted declarations.  The
estimates are fields of the structure:

```lean
RiemannAsymptoticFrontier.AnalyticFrontier N Nsafe C
```

The theorem is therefore a conditional synthesis theorem.

---

## II. Source Order

The live file is fused in dependency order:

```text
XiAsymptoticFrontier/Basic.lean
XiAsymptoticFrontier/Frontier.lean
XiAsymptoticFrontier/Synthesis.lean
```

The live file imports only Mathlib dependencies and does not import the local
package modules.

---

## III. Main Terms and Normalization

The classical Riemann-von Mangoldt main term is:

```lean
noncomputable def vonMangoldtMainTerm (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1)
```

The simplified equivalent form is:

```lean
noncomputable def vonMangoldtMainTermSimplified (T : ℝ) : ℝ :=
  T * Real.log T / (2 * Real.pi)
```

The abstract zero-counting type is:

```lean
abbrev ZeroCountingFunction := ℝ → ℝ
```

This package does not redefine the concrete zero-counting function.  It works
with an abstract function `N`, because the purpose here is the asymptotic
synthesis layer.

The normalized real part of a contour contribution is:

```lean
noncomputable def contourNormalizedRealPart (z : ℂ) : ℝ :=
  (z / (2 * Real.pi * Complex.I)).re
```

The basic algebra of this normalization is packaged as:

```lean
contourNormalizedRealPart_add
contourNormalizedRealPart_sub
contourNormalizedRealPart_neg
contourNormalizedRealPart_of_real_mul_I
abs_contourNormalizedRealPart_le_norm_div
```

---

## IV. Contour Components

The normalized contour expansion is represented by:

```lean
structure ContourComponents where
  origin : ℝ → ℝ
  polynomialHorizontal : ℝ → ℝ
  polynomialVertical : ℝ → ℝ
  gammaHorizontal : ℝ → ℝ
  gammaVertical : ℝ → ℝ
  zetaHorizontal : ℝ → ℝ
  zetaVertical : ℝ → ℝ
```

The residual term is the sum of all normalized non-gamma-horizontal pieces:

```lean
noncomputable def ContourComponents.residual (C : ContourComponents) : ℝ → ℝ :=
  fun T =>
    C.origin T +
      C.polynomialHorizontal T + C.polynomialVertical T +
        C.gammaVertical T + C.zetaHorizontal T + C.zetaVertical T
```

The reconstruction condition is:

```lean
def ContourComponents.reconstructs
    (C : ContourComponents) (N : ZeroCountingFunction) : Prop :=
  ∀ᶠ T in atTop, N T = C.gammaHorizontal T + C.residual T
```

This says that, eventually, the counting function is recovered from the
dominant gamma-horizontal contribution plus the residual contour terms.

---

## V. Typed Analytic Frontier

Each analytic estimate is given a named proposition:

```lean
def PolynomialContourNegligible (C : ContourComponents) : Prop :=
  C.polynomialHorizontal =o[atTop] vonMangoldtMainTerm ∧
    C.polynomialVertical =o[atTop] vonMangoldtMainTerm
```

```lean
def GammaVerticalEdgesNegligible (C : ContourComponents) : Prop :=
  C.gammaVertical =o[atTop] vonMangoldtMainTerm
```

```lean
def ZetaEdgesNegligible (C : ContourComponents) : Prop :=
  C.zetaHorizontal =o[atTop] vonMangoldtMainTerm ∧
    C.zetaVertical =o[atTop] vonMangoldtMainTerm
```

```lean
def NearOriginNegligible (C : ContourComponents) : Prop :=
  C.origin =o[atTop] vonMangoldtMainTerm
```

```lean
def GammaHorizontalStirlingGoal (C : ContourComponents) : Prop :=
  IsEquivalent atTop C.gammaHorizontal vonMangoldtMainTerm
```

The safe-height transfer is:

```lean
def SafeHeightCountingEquivalent (N Nsafe : ZeroCountingFunction) : Prop :=
  IsEquivalent atTop N Nsafe
```

The complete frontier is:

```lean
structure AnalyticFrontier
    (N Nsafe : ZeroCountingFunction) (C : ContourComponents) : Prop where
  reconstructs_safe : C.reconstructs Nsafe
  near_origin : NearOriginNegligible C
  polynomial : PolynomialContourNegligible C
  gamma_horizontal : GammaHorizontalStirlingGoal C
  gamma_vertical : GammaVerticalEdgesNegligible C
  zeta_edges : ZetaEdgesNegligible C
  safe_height_counting : SafeHeightCountingEquivalent N Nsafe
```

This is the central design of the package.  The analytic frontier is explicit,
typed, and inspectable.

---

## VI. Residual Negligibility

The residual theorem combines the individual negligible estimates:

```lean
lemma residual_negligible {C : ContourComponents}
    (hOrigin : NearOriginNegligible C)
    (hPoly : PolynomialContourNegligible C)
    (hGammaVert : GammaVerticalEdgesNegligible C)
    (hZeta : ZetaEdgesNegligible C) :
    C.residual =o[atTop] vonMangoldtMainTerm
```

This is a purely asymptotic algebra step.  It does not prove the individual
analytic estimates; it proves that once they are supplied, their sum is still
negligible.

---

## VII. Conditional Synthesis

The abstract Riemann-von Mangoldt statement is:

```lean
def RiemannVonMangoldtMultiplicityCounting
    (N : ZeroCountingFunction) : Prop :=
  IsEquivalent atTop N vonMangoldtMainTerm
```

The safe-height version follows from reconstruction, gamma dominance, and
residual negligibility:

```lean
theorem safe_counting_equiv_main {Nsafe : ZeroCountingFunction}
    {C : ContourComponents}
    (hReconstruct : C.reconstructs Nsafe)
    (hGamma : GammaHorizontalStirlingGoal C)
    (hResidual : C.residual =o[atTop] vonMangoldtMainTerm) :
    IsEquivalent atTop Nsafe vonMangoldtMainTerm
```

The full frontier gives the safe-height Riemann-von Mangoldt statement:

```lean
theorem safe_riemann_von_mangoldt_from_frontier
    {N Nsafe : ZeroCountingFunction} {C : ContourComponents}
    (h : AnalyticFrontier N Nsafe C) :
    RiemannVonMangoldtMultiplicityCounting Nsafe
```

The final transfer to the original count is:

```lean
theorem riemann_von_mangoldt_from_contour_frontier
    {N Nsafe : ZeroCountingFunction} {C : ContourComponents}
    (h : AnalyticFrontier N Nsafe C) :
    RiemannVonMangoldtMultiplicityCounting N
```

The package-level statement is:

```lean
def RiemannVonMangoldtFromContourFrontier : Prop :=
  ∀ {N Nsafe : ZeroCountingFunction} {C : ContourComponents},
    AnalyticFrontier N Nsafe C → RiemannVonMangoldtMultiplicityCounting N
```

and it is proved by:

```lean
theorem riemann_von_mangoldt_from_contour_bridge :
    RiemannVonMangoldtFromContourFrontier
```

This is the final conditional theorem of the package.

---

## VIII. Verification

Compile the live file directly:

```text
lake env lean XiAsymptoticFrontier/XiAsymptoticFrontierLive/XiAsymptoticFrontier.live.lean
```

A clean run produces no output.

Check for forbidden local dependencies or unfinished proof markers:

```text
rg -n "public import XiAsymptoticFrontier|import XiAsymptoticFrontier|RiemannSynthesis|NavierStokesWeb|BirchSwinnertonDyerWeb|ErdosWeb|source corpus|mother formalization|unpublished formalization|formalizacion madre|formalización madre|\bsorry\b|\baxiom\b|admit|native_decide" XiAsymptoticFrontier/XiAsymptoticFrontierLive/XiAsymptoticFrontier.live.lean
```

A clean run produces no output.

---

## IX. Axiom Certificate

The following command records the trusted kernel base used by representative
theorems:

```text
printf 'import XiAsymptoticFrontier
#print axioms RiemannAsymptoticFrontier.residual_negligible
#print axioms RiemannAsymptoticFrontier.safe_counting_equiv_main
#print axioms RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_frontier
#print axioms RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_bridge
' | lake env lean --stdin
```

Expected output:

```text
'RiemannAsymptoticFrontier.residual_negligible' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannAsymptoticFrontier.safe_counting_equiv_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_frontier' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is the standard Lean/Mathlib kernel base for this classical development.
