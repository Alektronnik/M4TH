/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import KdV.Hyperbolic

/-!
# The exact one-soliton profile for KdV

This file proves that the classical profile

`f(x) = 3 c sech^2 ((sqrt c / 2) x)`

satisfies the stationary travelling-wave ODE for the normalization
`u_t + u u_x + u_xxx = 0`.

## Main results

- `KdV.soliton_deriv1`, `KdV.soliton_deriv3`: explicit derivatives of the
  profile `3 c sech^2 (k x)`.
- `KdV.soliton_satisfies_kdv`: the exact soliton profile satisfies
  `-c f' + f f' + f''' = 0` when `c > 0`.

## Implementation notes

The derivative chain is proved with `HasDerivAt`, rather than by an external
symbolic engine, so the final theorem remains a kernel-checked analytic
identity.

## Tags

KdV equation, soliton, travelling wave, hyperbolic secant
-/

@[expose] public section

namespace KdV

set_option maxHeartbeats 600000

/-- First derivative of the scaled squared-sech profile. -/
lemma soliton_deriv1 (c k ξ : ℝ) :
    deriv (fun x => 3 * c * sech (k * x) ^ 2) ξ =
      -6 * c * k * sech (k * ξ) ^ 2 * Real.tanh (k * ξ) := by
  have h1 := hasDerivAt_sech_sq_mul k ξ
  have h2 := h1.const_mul (3 * c)
  have h_simp :
      3 * c * (-2 * k * sech (k * ξ) ^ 2 * Real.tanh (k * ξ)) =
        -6 * c * k * sech (k * ξ) ^ 2 * Real.tanh (k * ξ) := by
    ring
  rw [← h_simp]
  exact h2.deriv

private lemma hasDerivAt_soliton_deriv1 (c k x : ℝ) :
    HasDerivAt
      (fun y => -6 * c * k * sech (k * y) ^ 2 * Real.tanh (k * y))
      (12 * c * k ^ 2 * sech (k * x) ^ 2 * Real.tanh (k * x) ^ 2 -
        6 * c * k ^ 2 * sech (k * x) ^ 4) x := by
  have h := ((hasDerivAt_sech_sq_mul k x).mul (hasDerivAt_tanh_mul k x)).const_mul
    (-6 * c * k)
  have h_fun : (fun y => -6 * c * k * sech (k * y) ^ 2 * Real.tanh (k * y)) =
      fun y => -6 * c * k * ((fun y => sech (k * y) ^ 2) *
        fun y => Real.tanh (k * y)) y := by
    funext y
    simp only [Pi.mul_apply]
    ring
  have h_deriv :
      12 * c * k ^ 2 * sech (k * x) ^ 2 * Real.tanh (k * x) ^ 2 -
          6 * c * k ^ 2 * sech (k * x) ^ 4 =
        -6 * c * k *
          (-2 * k * sech (k * x) ^ 2 * Real.tanh (k * x) * Real.tanh (k * x) +
            sech (k * x) ^ 2 * (k * sech (k * x) ^ 2)) := by
    ring
  exact (h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq h_fun)).congr_deriv h_deriv.symm

private lemma soliton_deriv2 (c k ξ : ℝ) :
    deriv (fun z => deriv (fun x => 3 * c * sech (k * x) ^ 2) z) ξ =
      12 * c * k ^ 2 * sech (k * ξ) ^ 2 * Real.tanh (k * ξ) ^ 2 -
        6 * c * k ^ 2 * sech (k * ξ) ^ 4 := by
  simp_rw [soliton_deriv1]
  exact (hasDerivAt_soliton_deriv1 c k ξ).deriv

private lemma hasDerivAt_soliton_deriv2 (c k x : ℝ) :
    HasDerivAt
      (fun y =>
        12 * c * k ^ 2 * sech (k * y) ^ 2 * Real.tanh (k * y) ^ 2 -
          6 * c * k ^ 2 * sech (k * y) ^ 4)
      (24 * c * k ^ 3 * sech (k * x) ^ 2 * Real.tanh (k * x) *
        (2 - 3 * Real.tanh (k * x) ^ 2)) x := by
  have hq := hasDerivAt_sech_sq_mul k x
  have ht := hasDerivAt_tanh_mul k x
  have hleft := (hq.mul (ht.pow 2)).const_mul (12 * c * k ^ 2)
  have hright := (hq.pow 2).const_mul (6 * c * k ^ 2)
  have h := hleft.sub hright
  have h_simp :
      12 * c * k ^ 2 *
        (-2 * k * sech (k * x) ^ 2 * Real.tanh (k * x) * Real.tanh (k * x) ^ 2 +
          sech (k * x) ^ 2 * (2 * Real.tanh (k * x) * (k * sech (k * x) ^ 2))) -
      6 * c * k ^ 2 * (2 * sech (k * x) ^ 2 *
        (-2 * k * sech (k * x) ^ 2 * Real.tanh (k * x))) =
      24 * c * k ^ 3 * sech (k * x) ^ 2 * Real.tanh (k * x) *
        (2 - 3 * Real.tanh (k * x) ^ 2) := by
    set S := sech (k * x) ^ 2
    set Th := Real.tanh (k * x)
    have h_id2 : S = 1 - Th ^ 2 := sech_sq_eq_one_sub_tanh_sq (k * x)
    calc
      12 * c * k ^ 2 * (-2 * k * S * Th * Th ^ 2 + S * (2 * Th * (k * S))) -
          6 * c * k ^ 2 * (2 * S * (-2 * k * S * Th))
        = 24 * c * k ^ 3 * S * Th * (-Th ^ 2 + 2 * S) := by ring
      _ = 24 * c * k ^ 3 * S * Th * (-Th ^ 2 + 2 * (1 - Th ^ 2)) := by rw [h_id2]
      _ = 24 * c * k ^ 3 * S * Th * (2 - 3 * Th ^ 2) := by ring
  have h_fun :
      (fun y => 12 * c * k ^ 2 * sech (k * y) ^ 2 * Real.tanh (k * y) ^ 2 -
          6 * c * k ^ 2 * sech (k * y) ^ 4) =
        (fun y =>
          12 * c * k ^ 2 * ((fun y => sech (k * y) ^ 2) *
            (fun y => Real.tanh (k * y)) ^ 2) y) -
            fun y => 6 * c * k ^ 2 * ((fun y => sech (k * y) ^ 2) ^ 2) y := by
    ext y
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
    ring
  have h_deriv :
      24 * c * k ^ 3 * sech (k * x) ^ 2 * Real.tanh (k * x) *
          (2 - 3 * Real.tanh (k * x) ^ 2) =
        12 * c * k ^ 2 *
            (-2 * k * sech (k * x) ^ 2 * Real.tanh (k * x) *
                ((fun y => Real.tanh (k * y)) ^ 2) x +
              sech (k * x) ^ 2 *
                (↑2 * Real.tanh (k * x) ^ (2 - 1) * (k * sech (k * x) ^ 2))) -
          6 * c * k ^ 2 *
            (↑2 * (sech (k * x) ^ 2) ^ (2 - 1) *
              (-2 * k * sech (k * x) ^ 2 * Real.tanh (k * x))) := by
    simp only [Pi.pow_apply]
    have h_pow : (2 - 1 : ℕ) = 1 := rfl
    simp only [h_pow, pow_one]
    exact h_simp.symm
  exact (h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq h_fun)).congr_deriv h_deriv.symm

/-- Third derivative of the scaled squared-sech profile. -/
lemma soliton_deriv3 (c k ξ : ℝ) :
    deriv (fun y => deriv (fun z => deriv (fun x => 3 * c * sech (k * x) ^ 2) z) y) ξ =
      24 * c * k ^ 3 * sech (k * ξ) ^ 2 * Real.tanh (k * ξ) *
        (2 - 3 * Real.tanh (k * ξ) ^ 2) := by
  simp_rw [soliton_deriv2]
  exact (hasDerivAt_soliton_deriv2 c k ξ).deriv

private lemma soliton_ode_check (c k : ℝ) (hk : k ^ 2 = c / 4) (ξ : ℝ) :
    -c * (-6 * c * k * sech (k * ξ) ^ 2 * Real.tanh (k * ξ)) +
      (3 * c * sech (k * ξ) ^ 2) *
        (-6 * c * k * sech (k * ξ) ^ 2 * Real.tanh (k * ξ)) +
      24 * c * k ^ 3 * sech (k * ξ) ^ 2 * Real.tanh (k * ξ) *
        (2 - 3 * Real.tanh (k * ξ) ^ 2) = 0 := by
  have h_s : sech (k * ξ) ^ 2 = 1 - Real.tanh (k * ξ) ^ 2 :=
    sech_sq_eq_one_sub_tanh_sq (k * ξ)
  simp only [h_s]
  conv_lhs => rw [show k ^ 3 = k * k ^ 2 from by ring, hk]
  ring

/-- The exact KdV one-soliton profile satisfies the stationary travelling-wave
ODE `-c f' + f f' + f''' = 0`. -/
theorem soliton_satisfies_kdv (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    -c * deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) ξ +
      (3 * c * sech (Real.sqrt c / 2 * ξ) ^ 2) *
        deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) ξ +
      deriv (fun y => deriv (fun z =>
        deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) z) y) ξ = 0 := by
  set k := Real.sqrt c / 2
  have hk_sq : k ^ 2 = c / 4 := by
    show (Real.sqrt c / 2) ^ 2 = c / 4
    rw [div_pow, Real.sq_sqrt (le_of_lt hc)]
    norm_num
  rw [soliton_deriv1 c k ξ, soliton_deriv3 c k ξ]
  exact soliton_ode_check c k hk_sq ξ

end KdV

end
