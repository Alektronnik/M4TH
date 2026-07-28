/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import XiLogDeriv.DigammaContinuity

/-!
# Full logarithmic-derivative expansion of Xi

This file combines the polynomial, `Gammaℝ`, and zeta logarithmic derivative
components.  Boundary-specific applications can supply the required nonzero
denominators from safe-height or contour hypotheses.
-/

@[expose] public section

open Complex Topology Filter

namespace RiemannLogDeriv

/-- The full decomposition
`ξ'/ξ = 1/s + 1/(s-1) + Gammaℝ'/Gammaℝ + ζ'/ζ`.
-/
theorem entireXiLogDeriv_full_expansion_of_factors_ne_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hξ : entireXi s ≠ 0)
    (hγ : Complex.Gammaℝ s ≠ 0) (hzeta : riemannZeta s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) :
    entireXiLogDeriv s =
      1 / s + 1 / (s - 1) + gammaRFactorLogDeriv s + riemannZetaLogDeriv s := by
  rw [entireXiLogDeriv_expansion_of_ne_zero_ne_one hs0 hs1 hξ hΛ,
    completedRiemannZetaLogDeriv_expansion_of_factors_ne_zero hs0 hs1 hγ hzeta hΛ]
  ring

/-- Regular-boundary form with the nonvanishing hypotheses exposed explicitly. -/
theorem entireXiLogDeriv_full_expansion_on_regular_boundary {T : ℝ} {s : ℂ}
    (hs_boundary : s ∈
      ({z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ z.im = T} ∪
        {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ z.im = 0} ∪
        {z : ℂ | z.re = 0 ∧ 0 ≤ z.im ∧ z.im ≤ T} ∪
        {z : ℂ | z.re = 1 ∧ 0 ≤ z.im ∧ z.im ≤ T}))
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hξ : entireXi s ≠ 0)
    (hγ : Complex.Gammaℝ s ≠ 0) (hzeta : riemannZeta s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) :
    entireXiLogDeriv s =
      entireXiPolynomialLogDeriv s + gammaRFactorLogDeriv s + riemannZetaLogDeriv s := by
  have _ := hs_boundary
  rw [entireXiPolynomialLogDeriv]
  exact entireXiLogDeriv_full_expansion_of_factors_ne_zero hs0 hs1 hξ hγ hzeta hΛ

/-- Digamma-substituted full decomposition of the Xi logarithmic derivative. -/
theorem entireXiLogDeriv_full_expansion_with_digamma {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hξ : entireXi s ≠ 0)
    (hγ : Complex.Gammaℝ s ≠ 0) (hzeta : riemannZeta s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) :
    entireXiLogDeriv s =
      entireXiPolynomialLogDeriv s -
        (1 / 2) * log (Real.pi : ℂ) +
        (1 / 2) * digamma (s / 2) +
        riemannZetaLogDeriv s := by
  rw [entireXiLogDeriv_full_expansion_of_factors_ne_zero hs0 hs1 hξ hγ hzeta hΛ,
    gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma hγ,
    entireXiPolynomialLogDeriv]
  ring

end RiemannLogDeriv

end

