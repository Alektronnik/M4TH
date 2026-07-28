/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic

/-!
# XiAsymptoticFrontier.live

Single-file live version of the `XiAsymptoticFrontier` package.

This file is intentionally independent of local package imports. It fuses the
public source modules in dependency order for web inspection and study.
-/

@[expose] public section


/-!
## Source file: `XiAsymptoticFrontier/Basic.lean`
-/


/-!
# Basic asymptotic objects for the Xi contour frontier

This file defines the classical Riemann-von Mangoldt main term and records the
package-local names used by the typed analytic frontier.
-/


open Complex Topology Filter Asymptotics

namespace RiemannAsymptoticFrontier

/-- Classical Riemann-von Mangoldt main term. -/
noncomputable def vonMangoldtMainTerm (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1)

/-- Simplified asymptotic equivalent main term. -/
noncomputable def vonMangoldtMainTermSimplified (T : ℝ) : ℝ :=
  T * Real.log T / (2 * Real.pi)

/-- Abstract multiplicity-counting function used by the frontier package.

The concrete zero-counting definition belongs to the zero-counting package.
This package only needs a function whose asymptotic behaviour is synthesized
from contour hypotheses.
-/
abbrev ZeroCountingFunction := ℝ → ℝ

/-- Normalized real part of a contour contribution. -/
noncomputable def contourNormalizedRealPart (z : ℂ) : ℝ :=
  (z / (2 * Real.pi * Complex.I)).re

lemma contourNormalizedRealPart_add (z w : ℂ) :
    contourNormalizedRealPart (z + w) =
      contourNormalizedRealPart z + contourNormalizedRealPart w := by
  dsimp [contourNormalizedRealPart]
  rw [add_div, Complex.add_re]

lemma contourNormalizedRealPart_sub (z w : ℂ) :
    contourNormalizedRealPart (z - w) =
      contourNormalizedRealPart z - contourNormalizedRealPart w := by
  dsimp [contourNormalizedRealPart]
  rw [sub_div, Complex.sub_re]

lemma contourNormalizedRealPart_neg (z : ℂ) :
    contourNormalizedRealPart (-z) = -contourNormalizedRealPart z := by
  dsimp [contourNormalizedRealPart]
  rw [neg_div, Complex.neg_re]

lemma contourNormalizedRealPart_of_real_mul_I (x : ℝ) :
    contourNormalizedRealPart (2 * Real.pi * Complex.I * x) = x := by
  dsimp [contourNormalizedRealPart]
  field_simp [Complex.two_pi_I_ne_zero]
  simp [ofReal_re]

lemma abs_contourNormalizedRealPart_le_norm_div (z : ℂ) :
    |contourNormalizedRealPart z| ≤ ‖z‖ / (2 * Real.pi) := by
  dsimp [contourNormalizedRealPart]
  calc
    |(z / (2 * Real.pi * Complex.I)).re| ≤ ‖z / (2 * Real.pi * Complex.I)‖ :=
      Complex.abs_re_le_norm _
    _ = ‖z‖ / ‖(2 * Real.pi * Complex.I : ℂ)‖ := Complex.norm_div z _
    _ = ‖z‖ / (2 * Real.pi) := by
      simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]

end RiemannAsymptoticFrontier


/-!
## Source file: `XiAsymptoticFrontier/Frontier.lean`
-/


/-!
# Typed analytic frontier

The residual analytic estimates of the contour proof are represented here as
explicit hypotheses.  This file contains no trusted analytic declarations.
-/


open Complex Topology Filter Asymptotics

namespace RiemannAsymptoticFrontier

/-- Container for the real-valued components of a normalized contour expansion. -/
structure ContourComponents where
  origin : ℝ → ℝ
  polynomialHorizontal : ℝ → ℝ
  polynomialVertical : ℝ → ℝ
  gammaHorizontal : ℝ → ℝ
  gammaVertical : ℝ → ℝ
  zetaHorizontal : ℝ → ℝ
  zetaVertical : ℝ → ℝ

/-- The sum of all normalized non-gamma-horizontal residual terms. -/
noncomputable def ContourComponents.residual (C : ContourComponents) : ℝ → ℝ :=
  fun T =>
    C.origin T +
      C.polynomialHorizontal T + C.polynomialVertical T +
        C.gammaVertical T + C.zetaHorizontal T + C.zetaVertical T

/-- The normalized contour reconstruction of the zero-counting function. -/
def ContourComponents.reconstructs (C : ContourComponents) (N : ZeroCountingFunction) : Prop :=
  ∀ᶠ T in atTop, N T = C.gammaHorizontal T + C.residual T

/-- Polynomial contour terms are negligible. -/
def PolynomialContourNegligible (C : ContourComponents) : Prop :=
  C.polynomialHorizontal =o[atTop] vonMangoldtMainTerm ∧
    C.polynomialVertical =o[atTop] vonMangoldtMainTerm

/-- Gamma vertical edges are negligible. -/
def GammaVerticalEdgesNegligible (C : ContourComponents) : Prop :=
  C.gammaVertical =o[atTop] vonMangoldtMainTerm

/-- Zeta horizontal and vertical edges are negligible. -/
def ZetaEdgesNegligible (C : ContourComponents) : Prop :=
  C.zetaHorizontal =o[atTop] vonMangoldtMainTerm ∧
    C.zetaVertical =o[atTop] vonMangoldtMainTerm

/-- The near-origin block is negligible. -/
def NearOriginNegligible (C : ContourComponents) : Prop :=
  C.origin =o[atTop] vonMangoldtMainTerm

/-- Gamma horizontal/Stirling contribution supplies the main term. -/
def GammaHorizontalStirlingGoal (C : ContourComponents) : Prop :=
  IsEquivalent atTop C.gammaHorizontal vonMangoldtMainTerm

/-- Safe-height compression between the raw height and the chosen safe height. -/
def SafeHeightCountingEquivalent (N Nsafe : ZeroCountingFunction) : Prop :=
  IsEquivalent atTop N Nsafe

/-- The full typed analytic frontier for the Riemann-von Mangoldt contour synthesis. -/
structure AnalyticFrontier (N Nsafe : ZeroCountingFunction) (C : ContourComponents) : Prop where
  reconstructs_safe : C.reconstructs Nsafe
  near_origin : NearOriginNegligible C
  polynomial : PolynomialContourNegligible C
  gamma_horizontal : GammaHorizontalStirlingGoal C
  gamma_vertical : GammaVerticalEdgesNegligible C
  zeta_edges : ZetaEdgesNegligible C
  safe_height_counting : SafeHeightCountingEquivalent N Nsafe

lemma residual_negligible {C : ContourComponents}
    (hOrigin : NearOriginNegligible C)
    (hPoly : PolynomialContourNegligible C)
    (hGammaVert : GammaVerticalEdgesNegligible C)
    (hZeta : ZetaEdgesNegligible C) :
    C.residual =o[atTop] vonMangoldtMainTerm := by
  dsimp [ContourComponents.residual, NearOriginNegligible, PolynomialContourNegligible,
    GammaVerticalEdgesNegligible, ZetaEdgesNegligible] at hOrigin hPoly hGammaVert hZeta ⊢
  exact (hOrigin.add (hPoly.1.add (hPoly.2.add (hGammaVert.add (hZeta.1.add hZeta.2))))).congr
    (fun T => by dsimp [ContourComponents.residual]; ring_nf) (fun _ => rfl)

end RiemannAsymptoticFrontier


/-!
## Source file: `XiAsymptoticFrontier/Synthesis.lean`
-/


/-!
# Conditional synthesis of Riemann-von Mangoldt

This file proves that the typed analytic frontier implies the asymptotic
zero-counting theorem.  All analytic estimates are hypotheses of
`AnalyticFrontier`; no trusted declarations are introduced.
-/


open Complex Topology Filter Asymptotics

namespace RiemannAsymptoticFrontier

/-- Multiplicity-counting Riemann-von Mangoldt statement for an abstract zero-counting function. -/
def RiemannVonMangoldtMultiplicityCounting (N : ZeroCountingFunction) : Prop :=
  IsEquivalent atTop N vonMangoldtMainTerm

/-- Safe-height counting follows the main term once the gamma term is dominant
and all other contour terms are negligible. -/
theorem safe_counting_equiv_main {Nsafe : ZeroCountingFunction} {C : ContourComponents}
    (hReconstruct : C.reconstructs Nsafe)
    (hGamma : GammaHorizontalStirlingGoal C)
    (hResidual : C.residual =o[atTop] vonMangoldtMainTerm) :
    IsEquivalent atTop Nsafe vonMangoldtMainTerm := by
  have hsum : IsEquivalent atTop (fun T => C.gammaHorizontal T + C.residual T)
      vonMangoldtMainTerm :=
    IsEquivalent.add_isLittleO hGamma hResidual
  exact hsum.congr_left (Filter.EventuallyEq.symm hReconstruct)

/-- The typed analytic frontier implies Riemann-von Mangoldt for `Nsafe`. -/
theorem safe_riemann_von_mangoldt_from_frontier {N Nsafe : ZeroCountingFunction}
    {C : ContourComponents} (h : AnalyticFrontier N Nsafe C) :
    RiemannVonMangoldtMultiplicityCounting Nsafe := by
  dsimp [RiemannVonMangoldtMultiplicityCounting]
  exact safe_counting_equiv_main h.reconstructs_safe h.gamma_horizontal
    (residual_negligible h.near_origin h.polynomial h.gamma_vertical h.zeta_edges)

/-- The typed analytic frontier implies Riemann-von Mangoldt for the original count. -/
theorem riemann_von_mangoldt_from_contour_frontier {N Nsafe : ZeroCountingFunction}
    {C : ContourComponents} (h : AnalyticFrontier N Nsafe C) :
    RiemannVonMangoldtMultiplicityCounting N := by
  exact h.safe_height_counting.trans (safe_riemann_von_mangoldt_from_frontier h)

/-- Package-level conditional statement. -/
def RiemannVonMangoldtFromContourFrontier : Prop :=
  ∀ {N Nsafe : ZeroCountingFunction} {C : ContourComponents},
    AnalyticFrontier N Nsafe C → RiemannVonMangoldtMultiplicityCounting N

theorem riemann_von_mangoldt_from_contour_bridge :
    RiemannVonMangoldtFromContourFrontier := by
  intro N Nsafe C h
  exact riemann_von_mangoldt_from_contour_frontier h

end RiemannAsymptoticFrontier
