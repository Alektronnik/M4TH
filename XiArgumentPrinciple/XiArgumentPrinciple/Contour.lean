/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import XiArgumentPrinciple.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Critical-box contour integrals

This file defines the four oriented edges of the critical box and proves that
the edge-by-edge contour integral agrees with the rectangular integral
convention used by the argument-principle bridge.
-/

@[expose] public section

open Complex Topology Filter MeasureTheory
open scoped Interval

namespace RiemannArgumentPrinciple

/-- Bottom edge: `γ(t) = t`, `t ∈ [0, 1]`. -/
noncomputable def criticalBoxBottomParam (t : ℝ) : ℂ :=
  (t : ℂ)

/-- Right edge: `γ(t) = 1 + it`, `t ∈ [0, T]`. -/
noncomputable def criticalBoxRightParam (_T t : ℝ) : ℂ :=
  1 + (t : ℂ) * I

/-- Top edge: `γ(t) = t + iT`, traversed by the interval integral `1..0`. -/
noncomputable def criticalBoxTopParam (T t : ℝ) : ℂ :=
  (t : ℂ) + (T : ℂ) * I

/-- Left edge: `γ(t) = it`, traversed by the interval integral `T..0`. -/
noncomputable def criticalBoxLeftParam (_T t : ℝ) : ℂ :=
  (t : ℂ) * I

noncomputable def entireXiBottomLogIntegrand (t : ℝ) : ℂ :=
  deriv criticalBoxBottomParam t * entireXiLogDeriv (criticalBoxBottomParam t)

noncomputable def entireXiRightLogIntegrand (T t : ℝ) : ℂ :=
  deriv (criticalBoxRightParam T) t * entireXiLogDeriv (criticalBoxRightParam T t)

noncomputable def entireXiTopLogIntegrand (T t : ℝ) : ℂ :=
  deriv (criticalBoxTopParam T) t * entireXiLogDeriv (criticalBoxTopParam T t)

noncomputable def entireXiLeftLogIntegrand (T t : ℝ) : ℂ :=
  deriv (criticalBoxLeftParam T) t * entireXiLogDeriv (criticalBoxLeftParam T t)

noncomputable def entireXiBottomEdgeIntegral : ℂ :=
  ∫ t in (0 : ℝ)..1, entireXiBottomLogIntegrand t

noncomputable def entireXiRightEdgeIntegral (T : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..T, entireXiRightLogIntegrand T t

noncomputable def entireXiTopEdgeIntegral (T : ℝ) : ℂ :=
  ∫ t in (1 : ℝ)..0, entireXiTopLogIntegrand T t

noncomputable def entireXiLeftEdgeIntegral (T : ℝ) : ℂ :=
  ∫ t in T..0, entireXiLeftLogIntegrand T t

/-- Integral of `entireXi'/entireXi` around the critical-box boundary. -/
noncomputable def entireXiContourIntegral (T : ℝ) : ℂ :=
  entireXiBottomEdgeIntegral + entireXiRightEdgeIntegral T +
    entireXiTopEdgeIntegral T + entireXiLeftEdgeIntegral T

/-- Rectangular integral over `[0,1] × [0,T]` with counter-clockwise signs. -/
noncomputable def criticalBoxRectangleIntegral (f : ℂ → ℂ) (T : ℝ) : ℂ :=
  (∫ x in (0 : ℝ)..1, f (x : ℂ)) -
    (∫ x in (0 : ℝ)..1, f ((x : ℂ) + (T : ℂ) * I)) +
  (Complex.I • ∫ y in (0 : ℝ)..T, f (1 + (y : ℂ) * I)) -
    (Complex.I • ∫ y in (0 : ℝ)..T, f ((y : ℂ) * I))

lemma deriv_criticalBoxBottomParam (t : ℝ) :
    deriv criticalBoxBottomParam t = 1 := by
  unfold criticalBoxBottomParam
  simpa using (hasDerivAt_id t).ofReal_comp.deriv

lemma deriv_criticalBoxRightParam (T t : ℝ) :
    deriv (criticalBoxRightParam T) t = I := by
  unfold criticalBoxRightParam
  simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).deriv

lemma deriv_criticalBoxTopParam (T t : ℝ) :
    deriv (criticalBoxTopParam T) t = 1 := by
  unfold criticalBoxTopParam
  simpa using ((hasDerivAt_id t).ofReal_comp.add_const ((T : ℂ) * I)).deriv

lemma deriv_criticalBoxLeftParam (T t : ℝ) :
    deriv (criticalBoxLeftParam T) t = I := by
  unfold criticalBoxLeftParam
  simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).deriv

/-- The edge contour equals the rectangular integral. -/
theorem entireXiContourIntegral_eq_rectangleIntegral (T : ℝ) :
    entireXiContourIntegral T =
      criticalBoxRectangleIntegral entireXiLogDeriv T := by
  dsimp only [entireXiContourIntegral, criticalBoxRectangleIntegral,
    entireXiBottomEdgeIntegral, entireXiRightEdgeIntegral,
    entireXiTopEdgeIntegral, entireXiLeftEdgeIntegral,
    entireXiBottomLogIntegrand, entireXiRightLogIntegrand,
    entireXiTopLogIntegrand, entireXiLeftLogIntegrand,
    criticalBoxBottomParam, criticalBoxRightParam, criticalBoxTopParam, criticalBoxLeftParam]
  simp only [deriv_criticalBoxBottomParam, deriv_criticalBoxRightParam,
    deriv_criticalBoxTopParam, deriv_criticalBoxLeftParam, one_mul]
  have htop :
      (∫ t in (1 : ℝ)..0, entireXiLogDeriv (↑t + ↑T * I)) =
        - ∫ t in (0 : ℝ)..1, entireXiLogDeriv (↑t + ↑T * I) := by
    rw [← intervalIntegral.integral_symm]
  have hleft :
      (∫ t in T..0, I * entireXiLogDeriv (↑t * I)) =
        - (Complex.I • ∫ y in (0 : ℝ)..T, entireXiLogDeriv (↑y * I)) := by
    rw [intervalIntegral.integral_symm (0 : ℝ) T, intervalIntegral.integral_const_mul,
      smul_eq_mul]
  have hright :
      (∫ t in (0 : ℝ)..T, I * entireXiLogDeriv (1 + ↑t * I)) =
        Complex.I • ∫ y in (0 : ℝ)..T, entireXiLogDeriv (1 + ↑y * I) := by
    rw [intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [htop, hleft, hright]
  ring

/-- Generic contour logarithmic-derivative integral. -/
noncomputable def contourLogDerivIntegral (f : ℂ → ℂ) (T : ℝ) : ℂ :=
  criticalBoxRectangleIntegral f T

lemma entireXiContourIntegral_eq_contourLogDerivIntegral (T : ℝ) :
    entireXiContourIntegral T = contourLogDerivIntegral entireXiLogDeriv T := by
  dsimp [contourLogDerivIntegral]
  exact entireXiContourIntegral_eq_rectangleIntegral T

end RiemannArgumentPrinciple
