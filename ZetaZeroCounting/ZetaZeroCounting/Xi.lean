/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.NumberTheory.LSeries.Nonvanishing

import Mathlib.Tactic

/-!
# The Riemann Xi function, the entire Xi variant, and the nontrivial zeros

Two normalisations of the Riemann Xi function on top of Mathlib's completed
zeta:

* `Riemann.riemannXi s = (1/2) s (s-1) completedRiemannZeta s` — the classical
  Xi, vanishing at the corners `s = 0, 1` by construction;
* `Riemann.entireXi s = s (s-1) completedRiemannZeta₀ s + 1` — an entire
  variant built on Mathlib's `completedRiemannZeta₀`, **nonvanishing at the
  corners**, designed so that Cauchy contours around the critical box never
  cross artificial zeros.

The two agree with `s (s-1) completedRiemannZeta s` away from `s = 0, 1`
(`entireXi_eq_mul_completedRiemannZeta`), which yields the exact dictionary
between zeros of `entireXi` in the open critical strip and the nontrivial
zeros of `riemannZeta` (`entireXi_eq_zero_of_mem_nontrivialZeros`,
`mem_nontrivialZeros_of_entireXi_eq_zero`).

The symmetry `s ↦ 1 - s` of the nontrivial zeros is **proved** from Mathlib's
functional equation (`one_sub_mem_nontrivialZeros`), as is the functional
equation of `riemannXi` itself.

## Main definitions

- `Riemann.riemannXi`, `Riemann.entireXi`, `Riemann.nontrivialZeros`,
  `Riemann.entireXiZeros`.

## Main results

- `Riemann.completedRiemannZeta_zero_iff`: in the open strip, `ζ` and the
  completed zeta vanish together.
- `Riemann.one_sub_mem_nontrivialZeros`: symmetry of the nontrivial zeros.
- `Riemann.riemannXi_functional_equation`: `ξ (1 - s) = ξ (s)`.
- `Riemann.entireXi_eq_mul_completedRiemannZeta` and the two-way dictionary
  with `nontrivialZeros`.

## Implementation notes

`entireXi` is normalised with the additive constant `+1` so that
`entireXi 0 = entireXi 1 = 1 ≠ 0`; the algebraic identities with
`completedRiemannZeta` follow from Mathlib's `completedRiemannZeta_eq`.  The
glue lemmas on `completedRiemannZeta` nonvanishing at `Re = 0, 1` transport
Mathlib's zero-free region through the functional equation.

## References

- E. C. Titchmarsh, *The theory of the Riemann zeta-function*.

## Tags

Riemann zeta, Xi function, nontrivial zeros, functional equation
-/

@[expose] public section

open Complex Set

namespace Riemann

/-- The classical Riemann Xi function: the completed zeta multiplied by
`(1/2) s (s - 1)` to remove the poles at `s = 0` and `s = 1`. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 / 2) * s * (s - 1) * completedRiemannZeta s

/-- The set of nontrivial zeros of the Riemann zeta function, confined to the
open critical strip `0 < Re s < 1`. -/
def nontrivialZeros : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}

/-- In the open critical strip, `riemannZeta` and `completedRiemannZeta`
vanish together (the archimedean factor `Gammaℝ` does not vanish there). -/
lemma completedRiemannZeta_zero_iff (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    riemannZeta s = 0 ↔ completedRiemannZeta s = 0 := by
  have h_ne : s ≠ 0 := by
    intro hc
    rw [hc] at hs
    have : (0 : ℂ).re = 0 := rfl
    rw [this] at hs
    linarith
  rw [riemannZeta_def_of_ne_zero h_ne]
  have h_gamma_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs.1
  simp [div_eq_zero_iff, h_gamma_ne]

/-- **Symmetry of the nontrivial zeros** under `s ↦ 1 - s`, proved from
Mathlib's functional equation of the completed zeta. -/
theorem one_sub_mem_nontrivialZeros (s : ℂ) (hs : s ∈ nontrivialZeros) :
    (1 - s) ∈ nontrivialZeros := by
  have h_band : 0 < s.re ∧ s.re < 1 := hs.2
  have h_band2 : 0 < (1 - s).re ∧ (1 - s).re < 1 := by
    simp only [sub_re, one_re]
    constructor <;> linarith
  have h_zero : completedRiemannZeta s = 0 := by
    have h_zeta := hs.1
    rwa [completedRiemannZeta_zero_iff s h_band] at h_zeta
  have h_zero2 : completedRiemannZeta (1 - s) = 0 := by
    rwa [completedRiemannZeta_one_sub]
  have h_final : riemannZeta (1 - s) = 0 := by
    rwa [completedRiemannZeta_zero_iff (1 - s) h_band2]
  exact ⟨h_final, h_band2⟩

/-- **Functional equation of the Xi function**: `ξ (1 - s) = ξ (s)`, deduced
from the symmetry of Mathlib's completed zeta. -/
theorem riemannXi_functional_equation (s : ℂ) :
    riemannXi (1 - s) = riemannXi s := by
  have h_comp : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  unfold riemannXi
  rw [h_comp]
  ring

/-- In the open critical strip, `s` is neither `0` nor `1`. -/
lemma critical_strip_ne_zero_one (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    s ≠ 0 ∧ s ≠ 1 := by
  constructor
  · intro h
    rw [h] at hs
    have h_zero : (0 : ℂ).re = 0 := rfl
    rw [h_zero] at hs
    linarith
  · intro h
    rw [h] at hs
    have h_one : (1 : ℂ).re = 1 := rfl
    rw [h_one] at hs
    linarith

lemma xi_polynomial_factor_ne_zero_of_ne_zero_ne_one {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s * (s - 1) ≠ 0 :=
  mul_ne_zero hs0 (sub_ne_zero.mpr hs1)

/-- The polynomial factor of `ξ` does not vanish in the open critical strip. -/
lemma xi_polynomial_ne_zero (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
  rcases critical_strip_ne_zero_one s hs with ⟨hne_zero, hne_one⟩
  refine mul_ne_zero (mul_ne_zero ?_ hne_zero) (sub_ne_zero.mpr hne_one)
  norm_num

/-- The corners annihilate `ξ` through the polynomial factor. -/
lemma riemannXi_zero_at_zero : riemannXi 0 = 0 := by
  simp [riemannXi]

lemma riemannXi_zero_at_one : riemannXi 1 = 0 := by
  simp [riemannXi]

/-! ### Nonvanishing glue for the completed zeta on the vertical lines -/

lemma riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero {s : ℂ}
    (hs0 : s ≠ 0) (hγ : Gammaℝ s ≠ 0) :
    riemannZeta s = 0 ↔ completedRiemannZeta s = 0 := by
  rw [riemannZeta_def_of_ne_zero hs0]
  simp [div_eq_zero_iff, hγ]

lemma completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  intro h0
  have hzeta := riemannZeta_ne_zero_of_one_le_re hs
  rcases eq_or_ne s 0 with rfl | hs0
  · exfalso
    have : (1 : ℝ) ≤ 0 := by simpa using hs
    linarith
  · have hγ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (lt_of_lt_of_le zero_lt_one hs)
    exact hzeta ((riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero hs0 hγ).mpr h0)

lemma completedRiemannZeta_ne_zero_of_re_eq_one {s : ℂ} (hs : s.re = 1) :
    completedRiemannZeta s ≠ 0 :=
  completedRiemannZeta_ne_zero_of_one_le_re (by simp [hs])

lemma completedRiemannZeta_ne_zero_of_re_eq_zero {s : ℂ} (hs : s.re = 0) (_hs0 : s ≠ 0) :
    completedRiemannZeta s ≠ 0 := by
  rw [← completedRiemannZeta_one_sub s]
  exact completedRiemannZeta_ne_zero_of_re_eq_one (by simp [hs])

/-! ### The entire Xi variant -/

/-- The entire Riemann Xi function, built on Mathlib's pole-free
`completedRiemannZeta₀`.  Normalised with `+ 1` so that the corners `0, 1` are
**not** zeros. -/
noncomputable def entireXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

lemma continuous_entireXi : Continuous entireXi := by
  have h_cont_zeta0 : Continuous completedRiemannZeta₀ :=
    differentiable_completedZeta₀.continuous
  exact (continuous_id.mul (continuous_id.sub continuous_const)).mul h_cont_zeta0 |>.add
    continuous_const

/-- The zeros of the entire function form a closed subset of the plane. -/
lemma isClosed_entireXi_zeros : IsClosed {s : ℂ | entireXi s = 0} :=
  isClosed_eq continuous_entireXi continuous_const

lemma differentiable_entireXi : Differentiable ℂ entireXi := by
  unfold entireXi
  exact ((differentiable_id.mul (differentiable_id.sub (differentiable_const (1 : ℂ)))).mul
    differentiable_completedZeta₀).add (differentiable_const (1 : ℂ))

lemma entireXi_ne_zero_at_zero : entireXi 0 ≠ 0 := by
  simp [entireXi]

lemma entireXi_ne_zero_at_one : entireXi 1 ≠ 0 := by
  simp [entireXi]

/-- The zero set of `entireXi`. -/
def entireXiZeros : Set ℂ :=
  {z : ℂ | entireXi z = 0}

lemma mem_entireXiZeros_iff {z : ℂ} : z ∈ entireXiZeros ↔ entireXi z = 0 :=
  Iff.rfl

lemma analyticAt_entireXi (s : ℂ) : AnalyticAt ℂ entireXi s :=
  ((analyticOnNhd_univ_iff_differentiable).2 differentiable_entireXi) s (mem_univ s)

/-- Algebraic identity: away from the poles `s = 0, 1`, `entireXi` coincides
with the polynomial factor times `completedRiemannZeta` (the `+1` cancels
against the residue terms of Mathlib's `completedRiemannZeta_eq`). -/
lemma entireXi_eq_mul_completedRiemannZeta {s : ℂ}
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
    _ = s * (s - 1) * completedRiemannZeta₀ s - s * (s - 1) / s - s * (s - 1) / (1 - s) := by
      rw [h_div1, h_div2]
      ring
    _ = s * (s - 1) * (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) := by ring
    _ = s * (s - 1) * completedRiemannZeta s := by rw [← h_mathlib]

/-- A nontrivial zero of zeta is a zero of `entireXi`. -/
lemma entireXi_eq_zero_of_mem_nontrivialZeros (s : ℂ) (hs : s ∈ nontrivialZeros) :
    entireXi s = 0 := by
  have h_band : 0 < s.re ∧ s.re < 1 := hs.2
  have h_ne_zero : s ≠ 0 := by
    intro h
    rw [h] at h_band
    have : (0 : ℂ).re = 0 := rfl
    rw [this] at h_band
    linarith [h_band.1]
  have h_ne_one : s ≠ 1 := by
    intro h
    rw [h] at h_band
    have : (1 : ℂ).re = 1 := rfl
    rw [this] at h_band
    linarith [h_band.2]
  have h_zeta_comp : completedRiemannZeta s = 0 :=
    (completedRiemannZeta_zero_iff s h_band).mp hs.1
  have heq := entireXi_eq_mul_completedRiemannZeta h_ne_zero h_ne_one
  rw [heq, h_zeta_comp, mul_zero]

/-- Converse dictionary: a zero of `entireXi` in the open strip is a
nontrivial zero of zeta. -/
lemma mem_nontrivialZeros_of_entireXi_eq_zero {s : ℂ} (hzero : entireXi s = 0)
    (hband : 0 < s.re ∧ s.re < 1) : s ∈ nontrivialZeros := by
  rcases critical_strip_ne_zero_one s hband with ⟨hs0, hs1⟩
  have hcomp : completedRiemannZeta s = 0 := by
    have heq := entireXi_eq_mul_completedRiemannZeta hs0 hs1
    rw [heq] at hzero
    rw [mul_eq_zero] at hzero
    cases hzero with
    | inl h => exact (xi_polynomial_factor_ne_zero_of_ne_zero_ne_one hs0 hs1 h).elim
    | inr h => exact h
  exact ⟨(completedRiemannZeta_zero_iff s hband).mpr hcomp, hband⟩

end Riemann

end
