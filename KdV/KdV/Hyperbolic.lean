/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.Trigonometric
public import KdV.Basic

/-!
# Hyperbolic-function calculus for the KdV soliton

This file introduces the real hyperbolic secant used by the exact KdV soliton
and proves the derivative identities needed for the profile
`3 c sech^2 ((sqrt c / 2) x)`.

## Main definitions

- `KdV.sech`: the hyperbolic secant `x ↦ 1 / cosh x`.
- `KdV.solitonProfile`: the one-soliton profile
  `x ↦ 3 c sech ((sqrt c / 2) x)^2`.

## Main results

- `KdV.hasDerivAt_sech`.
- `KdV.hasDerivAt_sech_mul`, `KdV.hasDerivAt_tanh_mul`,
  `KdV.hasDerivAt_sech_sq_mul`.
- `KdV.sech_sq_eq_one_sub_tanh_sq`.

## Implementation notes

At Mathlib-contribution time, `sech` and its derivative should be checked
against `Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp`; if Mathlib
has no named `Real.sech`, these lemmas are candidates for the special-functions
PR before the PDE-specific KdV files.

## Tags

hyperbolic functions, sech, tanh, soliton
-/

@[expose] public section

namespace KdV

/-- The hyperbolic secant, `sech x = 1 / cosh x`. -/
noncomputable def sech (x : ℝ) : ℝ := 1 / Real.cosh x

/-- The exact KdV soliton profile with speed `c`:
`3 c sech^2 ((sqrt c / 2) x)`. -/
noncomputable def solitonProfile (c x : ℝ) : ℝ :=
  3 * c * sech (Real.sqrt c / 2 * x) ^ 2

lemma cosh_ne_zero (x : ℝ) : Real.cosh x ≠ 0 :=
  ne_of_gt (Real.cosh_pos x)

lemma sech_ne_zero (x : ℝ) : sech x ≠ 0 := by
  unfold sech
  exact div_ne_zero one_ne_zero (cosh_ne_zero x)

/-- Hyperbolic identity `sech x ^ 2 = 1 - tanh x ^ 2`. -/
lemma sech_sq_eq_one_sub_tanh_sq (x : ℝ) : sech x ^ 2 = 1 - Real.tanh x ^ 2 := by
  have h_cosh_pos : 0 < Real.cosh x := Real.cosh_pos x
  have h_cosh_ne : Real.cosh x ≠ 0 := ne_of_gt h_cosh_pos
  have h_id : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
  rw [Real.tanh_eq_sinh_div_cosh]
  unfold sech
  field_simp
  nlinarith [sq_nonneg (Real.sinh x), h_id]

/-- Derivative of the hyperbolic secant. -/
lemma hasDerivAt_sech (x : ℝ) :
    HasDerivAt sech (-sech x * Real.tanh x) x := by
  have h := (Real.hasDerivAt_cosh x).inv (cosh_ne_zero x)
  have h_eq : sech = Real.cosh⁻¹ := by
    ext y
    unfold sech
    exact (inv_eq_one_div (Real.cosh y)).symm
  rw [h_eq]
  have h_deriv_eq : -Real.sinh x / Real.cosh x ^ 2 = -(Real.cosh x)⁻¹ * Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    simp only [neg_mul]
    ring
  exact h.congr_deriv h_deriv_eq

/-- Derivative of `x ↦ sech (k x)`. -/
lemma hasDerivAt_sech_mul (k x : ℝ) :
    HasDerivAt (fun y => sech (k * y))
      (-k * sech (k * x) * Real.tanh (k * x)) x := by
  have h1 := hasDerivAt_sech (k * x)
  have h2 := hasDerivAt_const_mul k (x := x)
  have h3 := h1.comp x h2
  have h_simp : -sech (k * x) * Real.tanh (k * x) * k =
      -k * sech (k * x) * Real.tanh (k * x) := by
    ring
  rw [← h_simp]
  exact h3

/-- Derivative of `x ↦ tanh (k x)`, expressed using `sech`. -/
lemma hasDerivAt_tanh_mul (k x : ℝ) :
    HasDerivAt (fun y => Real.tanh (k * y))
      (k * sech (k * x) ^ 2) x := by
  have hs := (Real.hasDerivAt_sinh (k * x)).comp x (hasDerivAt_const_mul k)
  have hc := (Real.hasDerivAt_cosh (k * x)).comp x (hasDerivAt_const_mul k)
  have h := hs.div hc (cosh_ne_zero (k * x))
  have h_fun : (fun y => Real.tanh (k * y)) =
      fun y => Real.sinh (k * y) / Real.cosh (k * y) := by
    funext y
    exact Real.tanh_eq_sinh_div_cosh (k * y)
  have h' := h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq h_fun)
  have h_deriv :
      (Real.cosh (k * x) * k * Real.cosh (k * x) -
          Real.sinh (k * x) * (Real.sinh (k * x) * k)) /
          (Real.cosh (k * x)) ^ 2 =
        k * sech (k * x) ^ 2 := by
    unfold sech
    have hid := Real.cosh_sq_sub_sinh_sq (k * x)
    have h_num :
        Real.cosh (k * x) * k * Real.cosh (k * x) -
            Real.sinh (k * x) * (Real.sinh (k * x) * k) =
          k * (Real.cosh (k * x) ^ 2 - Real.sinh (k * x) ^ 2) := by
      ring
    rw [h_num, hid]
    field_simp [cosh_ne_zero (k * x)]
  exact h'.congr_deriv h_deriv

/-- Derivative of `x ↦ sech (k x)^2`. -/
lemma hasDerivAt_sech_sq_mul (k x : ℝ) :
    HasDerivAt (fun y => sech (k * y) ^ 2)
      (-2 * k * sech (k * x) ^ 2 * Real.tanh (k * x)) x := by
  have h1 := hasDerivAt_sech_mul k x
  have h2 := h1.pow 2
  have h_simp :
      2 * sech (k * x) ^ (2 - 1) *
          (-k * sech (k * x) * Real.tanh (k * x)) =
        -2 * k * sech (k * x) ^ 2 * Real.tanh (k * x) := by
    have h_pow : (2 - 1 : ℕ) = 1 := rfl
    rw [h_pow, pow_one]
    ring
  rw [← h_simp]
  exact h2

end KdV

end
