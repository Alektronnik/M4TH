/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# Basic Xi and log-derivative infrastructure

This file isolates the package-local definitions used to expand the logarithmic
derivative of the entire Riemann Xi variant.  The namespace is deliberately
package-specific so that this package can coexist with the sibling
`ZetaZeroCounting` package in the same Lake workspace.
-/

@[expose] public section

open Complex Topology Filter

namespace RiemannLogDeriv

/-- The entire Xi variant used for critical-box contour arguments. -/
noncomputable def entireXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

/-- The polynomial factor `s(s-1)` in the completed-zeta factorization. -/
noncomputable def entireXiPolynomialFactor (s : ℂ) : ℂ :=
  s * (s - 1)

/-- Logarithmic derivative of the entire Xi variant. -/
noncomputable def entireXiLogDeriv (s : ℂ) : ℂ :=
  logDeriv entireXi s

/-- Logarithmic derivative of the polynomial factor `s(s-1)`. -/
noncomputable def entireXiPolynomialLogDeriv (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1)

/-- Logarithmic derivative of the completed zeta factor. -/
noncomputable def completedRiemannZetaLogDeriv (s : ℂ) : ℂ :=
  logDeriv completedRiemannZeta s

/-- Logarithmic derivative of the archimedean `Gammaℝ` factor. -/
noncomputable def gammaRFactorLogDeriv (s : ℂ) : ℂ :=
  logDeriv Complex.Gammaℝ s

/-- Classical logarithmic derivative of the Riemann zeta function. -/
noncomputable def riemannZetaLogDeriv (s : ℂ) : ℂ :=
  logDeriv riemannZeta s

lemma entireXiPolynomialFactor_eq (s : ℂ) :
    entireXiPolynomialFactor s = s * (s - 1) :=
  rfl

lemma entireXiLogDeriv_apply (s : ℂ) :
    entireXiLogDeriv s = deriv entireXi s / entireXi s :=
  logDeriv_apply entireXi s

lemma xi_polynomial_factor_ne_zero_of_ne_zero_ne_one {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s * (s - 1) ≠ 0 :=
  mul_ne_zero hs0 (sub_ne_zero.mpr hs1)

lemma differentiable_entireXi : Differentiable ℂ entireXi := by
  unfold entireXi
  exact ((differentiable_id.mul (differentiable_id.sub (differentiable_const (1 : ℂ)))).mul
    differentiable_completedZeta₀).add (differentiable_const (1 : ℂ))

lemma continuous_entireXi : Continuous entireXi :=
  differentiable_entireXi.continuous

lemma entireXi_ne_zero_at_zero : entireXi 0 ≠ 0 := by
  simp [entireXi]

lemma entireXi_ne_zero_at_one : entireXi 1 ≠ 0 := by
  simp [entireXi]

lemma analyticAt_entireXi (s : ℂ) : AnalyticAt ℂ entireXi s :=
  ((analyticOnNhd_univ_iff_differentiable).2 differentiable_entireXi) s (Set.mem_univ s)

/-- The entire Xi variant equals `s(s-1) completedRiemannZeta s` away from `0` and `1`. -/
lemma entireXi_eq_polynomial_times_completedZeta_of_ne_zero_ne_one {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireXi s = s * (s - 1) * completedRiemannZeta s := by
  have h_mathlib : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
    completedRiemannZeta_eq s
  have h_div1 : s * (s - 1) / s = s - 1 := by
    calc s * (s - 1) / s
      _ = (s - 1) * s / s := by ring
      _ = s - 1 := mul_div_cancel_right₀ (s - 1) hs0
  have h_div2 : s * (s - 1) / (1 - s) = -s := by
    have h_ne_one_sub : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
    calc s * (s - 1) / (1 - s)
      _ = -s * (1 - s) / (1 - s) := by ring
      _ = -s := mul_div_cancel_right₀ (-s) h_ne_one_sub
  calc
    entireXi s = s * (s - 1) * completedRiemannZeta₀ s + 1 := rfl
    _ = s * (s - 1) * completedRiemannZeta₀ s - (s - 1) + s := by ring
    _ = s * (s - 1) * completedRiemannZeta₀ s - s * (s - 1) / s -
        s * (s - 1) / (1 - s) := by
      rw [h_div1, h_div2]
      ring
    _ = s * (s - 1) * (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) := by ring
    _ = s * (s - 1) * completedRiemannZeta s := by rw [← h_mathlib]

lemma entireXi_eq_polynomial_mul_completedZeta_on_compl {z : ℂ}
    (hz : z ∈ ({0, 1} : Set ℂ)ᶜ) :
    entireXi z = entireXiPolynomialFactor z * completedRiemannZeta z := by
  have hz0 : z ≠ 0 := fun h => hz (Or.inl h)
  have hz1 : z ≠ 1 := fun h => hz (Or.inr h)
  exact entireXi_eq_polynomial_times_completedZeta_of_ne_zero_ne_one hz0 hz1

lemma logDeriv_linear_sub_one (s : ℂ) (_hs : s ≠ 1) :
    logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
  simp [logDeriv_apply, deriv_const, one_div]

lemma logDeriv_entireXiPolynomialFactor_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv entireXiPolynomialFactor s = 1 / s + 1 / (s - 1) := by
  rw [show entireXiPolynomialFactor = fun z => z * (z - 1) from
    funext entireXiPolynomialFactor_eq]
  have hmul := logDeriv_mul (f := fun w => w) (g := fun w => w - 1) s hs0
    (sub_ne_zero.mpr hs1) differentiableAt_id
    ((differentiableAt_id).sub (differentiableAt_const 1))
  rw [hmul, show logDeriv (fun w => w) = logDeriv id from funext fun _ => rfl,
    logDeriv_id, logDeriv_linear_sub_one s hs1]

lemma entireXiLogDeriv_eq_logDeriv_mul_completed_of_ne_zero_ne_one {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv entireXi s =
      logDeriv (fun z => entireXiPolynomialFactor z * completedRiemannZeta z) s := by
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (isClosed_singleton.union isClosed_singleton).isOpen_compl
  have hs_mem : s ∈ ({0, 1} : Set ℂ)ᶜ := by
    simpa [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using ⟨hs0, hs1⟩
  have hev : entireXi =ᶠ[𝓝 s] fun z => entireXiPolynomialFactor z * completedRiemannZeta z := by
    filter_upwards [hopen.mem_nhds hs_mem] with z hz using
      entireXi_eq_polynomial_mul_completedZeta_on_compl hz
  have heq : entireXi s = entireXiPolynomialFactor s * completedRiemannZeta s :=
    entireXi_eq_polynomial_mul_completedZeta_on_compl hs_mem
  rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, heq]

/-- First-stage expansion `ξ'/ξ = 1/s + 1/(s-1) + Λ'/Λ`. -/
theorem entireXiLogDeriv_expansion_of_ne_zero_ne_one {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (_hξ : entireXi s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) :
    entireXiLogDeriv s = 1 / s + 1 / (s - 1) + completedRiemannZetaLogDeriv s := by
  dsimp only [entireXiLogDeriv, completedRiemannZetaLogDeriv]
  have hpoly : entireXiPolynomialFactor s ≠ 0 :=
    xi_polynomial_factor_ne_zero_of_ne_zero_ne_one hs0 hs1
  rw [entireXiLogDeriv_eq_logDeriv_mul_completed_of_ne_zero_ne_one hs0 hs1,
    logDeriv_mul s hpoly hΛ
      ((differentiableAt_id).mul ((differentiableAt_id).sub (differentiableAt_const 1)))
      (differentiableAt_completedZeta hs0 hs1),
    logDeriv_entireXiPolynomialFactor_eq hs0 hs1]

end RiemannLogDeriv

end

