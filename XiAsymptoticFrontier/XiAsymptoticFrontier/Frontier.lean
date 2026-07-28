/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import XiAsymptoticFrontier.Basic

/-!
# Typed analytic frontier

The residual analytic estimates of the contour proof are represented here as
explicit hypotheses.  This file contains no trusted analytic declarations.
-/

@[expose] public section

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
