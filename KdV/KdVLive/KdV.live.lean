/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Tactic.SetNotationForOrder
import Mathlib.Tactic

/-!
# KdV live file

This file is a single-file live presentation of the Korteweg-de Vries package.
It fuses the package source files in dependency order for web verification and
mathematical study.

The public package remains the modular library under `KdV/`; this file is the
self-contained live version.
-/

open MeasureTheory

@[expose] public section

namespace KdV

/-!
## Source: `KdV/Basic.lean`
-/

set_option maxHeartbeats 600000

/-- Smooth solutions of the one-dimensional KdV equation
`u_t + u u_x + u_xxx = 0` on the time interval `[0, T)`. -/
structure IsSolution (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  differentiable : Differentiable ℝ (fun p : ℝ × ℝ => u p.1 p.2)
  differentiable_dx : ∀ t, Differentiable ℝ (fun x => deriv (u t) x)
  differentiable_dxx : ∀ t, Differentiable ℝ (fun y => deriv (fun x => deriv (u t) x) y)
  pde : ∀ t ∈ Set.Ico 0 T, ∀ x,
    deriv (fun s => u s x) t + u t x * deriv (u t) x +
      deriv (fun y => deriv (fun z => deriv (u t) z) y) x = 0

/-- A three-times differentiable travelling-wave profile.  The wave speed is
kept in the structure parameter because later files use the same profile in the
ansatz `u(t, x) = f (x - c t)`. -/
structure TravellingWave (c : ℝ) where
  profile : ℝ → ℝ
  differentiable : Differentiable ℝ profile
  differentiable_deriv : Differentiable ℝ (fun x => deriv profile x)
  differentiable_deriv2 : Differentiable ℝ (fun y => deriv (fun x => deriv profile x) y)

/-- Time derivative of a travelling-wave ansatz. -/
lemma travellingWave_deriv_time (f : ℝ → ℝ) (c t x : ℝ) :
    deriv (fun s => f (x - c * s)) t = -c * deriv f (x - c * t) := by
  calc
    deriv (fun s => f (x - c * s)) t =
        c * deriv (fun y => f (x - y)) (c * t) := by
      simpa only [smul_eq_mul] using
        deriv_comp_mul_left c (fun y => f (x - y)) t
    _ = -c * deriv f (x - c * t) := by
      rw [deriv_comp_const_sub]
      ring

/-- Spatial derivative of a travelling-wave ansatz. -/
lemma travellingWave_deriv_space (f : ℝ → ℝ) (c t x : ℝ) :
    deriv (fun y => f (y - c * t)) x = deriv f (x - c * t) := by
  exact deriv_comp_sub_const f (c * t) x

/-- Third spatial derivative of a travelling-wave ansatz. -/
lemma travellingWave_deriv_space3 (f : ℝ → ℝ) (c t x : ℝ) :
    deriv (fun y => deriv (fun z => deriv (fun w => f (w - c * t)) z) y) x =
      deriv (fun y => deriv (fun z => deriv f z) y) (x - c * t) := by
  rw [show (fun w => f (w - c * t)) = fun w => f (w - (c * t)) by rfl]
  simp_rw [deriv_comp_sub_const]

/-- Travelling-wave reduction of KdV to the stationary soliton ODE. -/
theorem travellingWave_reduction {T : ℝ} {u : ℝ → ℝ → ℝ} (sol : IsSolution T u)
    (c : ℝ) (wave : TravellingWave c)
    (h_wave : ∀ t x, u t x = wave.profile (x - c * t))
    (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : ℝ) :
    -c * deriv wave.profile (x - c * t) +
      wave.profile (x - c * t) * deriv wave.profile (x - c * t) +
      deriv (fun y => deriv (fun z => deriv wave.profile z) y) (x - c * t) = 0 := by
  have h_pde := sol.pde t ht x
  have h_u_eq : u = fun t x => wave.profile (x - c * t) := by
    ext t' x'
    exact h_wave t' x'
  rw [h_u_eq] at h_pde
  have h_ut := travellingWave_deriv_time wave.profile c t x
  have h_ux := travellingWave_deriv_space wave.profile c t x
  have h_uxxx := travellingWave_deriv_space3 wave.profile c t x
  dsimp at h_pde
  rw [h_ut, h_ux, h_uxxx] at h_pde
  exact h_pde

/-!
## Source: `KdV/Hyperbolic.lean`
-/

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

/-!
## Source: `KdV/Soliton.lean`
-/

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

/-!
## Source: `KdV/ConservationLaws.lean`
-/

open MeasureTheory



set_option maxHeartbeats 600000

/-- Total spatial mass of a time slice. -/
noncomputable def mass (u : ℝ → ℝ) : ℝ :=
  ∫ x, u x

/-- Quadratic spatial energy of a time slice. -/
noncomputable def energy (u : ℝ → ℝ) : ℝ :=
  ∫ x, u x ^ 2 / 2

/-- Time derivative `u_t(t, x)`. -/
noncomputable def ut (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun s => u s x) t

/-- Spatial derivative `u_x(t, x)`. -/
noncomputable def ux (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (u t) x

/-- Third spatial derivative `u_xxx(t, x)`. -/
noncomputable def uxxx (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun y => deriv (fun z => deriv (u t) z) y) x

/-- KdV solutions with a uniform compact spatial support on `[0, T)`. -/
structure ConservedSolution (T : ℝ) (u : ℝ → ℝ → ℝ) where
  solution : IsSolution T u
  support_K : Set ℝ
  support_K_compact : IsCompact support_K
  support_subset : ∀ t ∈ Set.Ico 0 T, tsupport (fun x => u t x) ⊆ support_K
  smooth_space : ∀ t ∈ Set.Ico 0 T, ContDiff ℝ 3 (fun x => u t x)

namespace ConservedSolution

variable {T : ℝ} {u : ℝ → ℝ → ℝ}

private lemma hasCompactSupport_timeSlice (sol : ConservedSolution T u)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
    HasCompactSupport (fun x => u t x) := by
  refine HasCompactSupport.intro sol.support_K_compact ?_
  intro x hx
  by_contra hne
  have hmem : x ∈ Function.support (fun x => u t x) := by
    simpa [Function.mem_support] using hne
  have hts : x ∈ tsupport (fun x => u t x) := subset_closure hmem
  exact hx (sol.support_subset t ht hts)

private lemma hasCompactSupport_half_sq {v : ℝ → ℝ}
    (hcs : HasCompactSupport v) :
    HasCompactSupport (fun x => v x ^ 2 / 2) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hcs ⊢
  exact hcs.mono fun x hx => by simp [hx]

private lemma hasCompactSupport_cube_third {v : ℝ → ℝ}
    (hcs : HasCompactSupport v) :
    HasCompactSupport (fun x => v x ^ 3 / 3) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hcs ⊢
  exact hcs.mono fun x hx => by simp [hx]

private lemma hasDerivAt_half_sq {v : ℝ → ℝ} {x : ℝ}
    (hv : DifferentiableAt ℝ v x) :
    HasDerivAt (fun x => v x ^ 2 / 2) (v x * deriv v x) x := by
  have h := hv.hasDerivAt.pow 2 |>.div_const 2
  have h_deriv : 2 * v x ^ (2 - 1) * deriv v x / 2 = v x * deriv v x := by
    have h_pow : (2 - 1 : ℕ) = 1 := rfl
    rw [h_pow, pow_one]
    ring
  exact h.congr_deriv h_deriv

private lemma hasDerivAt_cube_third {v : ℝ → ℝ} {x : ℝ}
    (hv : DifferentiableAt ℝ v x) :
    HasDerivAt (fun x => v x ^ 3 / 3) (v x ^ 2 * deriv v x) x := by
  have h := hv.hasDerivAt.pow 3 |>.div_const 3
  have h_deriv : 3 * v x ^ (3 - 1) * deriv v x / 3 = v x ^ 2 * deriv v x := by
    have h_pow : (3 - 1 : ℕ) = 2 := rfl
    rw [h_pow]
    ring
  exact h.congr_deriv h_deriv

private lemma hasCompactSupport_uxxx {v : ℝ → ℝ} (hcs : HasCompactSupport v) :
    HasCompactSupport (fun x => deriv (fun y => deriv (fun z => deriv v z) y) x) :=
  hcs.deriv.deriv.deriv

private lemma continuous_uxxx {v : ℝ → ℝ} (hv : ContDiff ℝ 3 v) :
    Continuous (fun x => deriv (fun y => deriv (fun z => deriv v z) y) x) := by
  have hv1 : ContDiff ℝ 2 (deriv v) := ContDiff.deriv' hv
  have hv2 : ContDiff ℝ 1 (deriv (deriv v)) := ContDiff.deriv' hv1
  have hv3 : ContDiff ℝ 0 (deriv (deriv (deriv v))) := ContDiff.deriv' hv2
  simpa using hv3.continuous

private lemma integral_deriv_eq_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) :
    ∫ x, deriv f x = 0 := by
  have hdiff := fun x => hf.differentiable one_ne_zero x |>.hasDerivAt
  have hf_int : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcs
  have hf'_int : Integrable (deriv f) :=
    hf.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hcs.deriv
  exact integral_eq_zero_of_hasDerivAt_of_integrable hdiff hf'_int hf_int

private lemma integral_u_mul_ux_eq_zero {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hcs : HasCompactSupport v) :
    ∫ x, v x * deriv v x = 0 := by
  set g := fun x => v x ^ 2 / 2
  have hg : ContDiff ℝ 1 g :=
    ((hv.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)).pow 2).div_const 2
  have hcs_g := hasCompactSupport_half_sq hcs
  have heq : deriv g = fun x => v x * deriv v x := by
    funext x
    exact (hasDerivAt_half_sq (hv.differentiable
      (by simp : (2 : WithTop ℕ∞) ≠ 0) x)).deriv
  rw [← heq]
  exact integral_deriv_eq_zero hg hcs_g

private lemma integral_u_sq_ux_eq_zero {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hcs : HasCompactSupport v) :
    ∫ x, v x ^ 2 * deriv v x = 0 := by
  set g := fun x => v x ^ 3 / 3
  have hg : ContDiff ℝ 1 g :=
    ((hv.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)).pow 3).div_const 3
  have hcs_g := hasCompactSupport_cube_third hcs
  have heq : deriv g = fun x => v x ^ 2 * deriv v x := by
    funext x
    exact (hasDerivAt_cube_third (hv.differentiable
      (by simp : (2 : WithTop ℕ∞) ≠ 0) x)).deriv
  rw [← heq]
  exact integral_deriv_eq_zero hg hcs_g

private lemma integral_uxxx_eq_zero {v : ℝ → ℝ}
    (hv : ContDiff ℝ 3 v) (hcs : HasCompactSupport v) :
    ∫ x, deriv (fun y => deriv (fun z => deriv v z) y) x = 0 := by
  set v2 := fun x => deriv (fun y => deriv v y) x
  have hv2 : ContDiff ℝ 1 v2 := by
    simpa [v2] using ContDiff.deriv' (ContDiff.deriv' hv)
  have hcs_v2 : HasCompactSupport v2 := hcs.deriv.deriv
  simpa [v2] using integral_deriv_eq_zero hv2 hcs_v2

private lemma integral_u_mul_uxxx_eq_zero {v : ℝ → ℝ}
    (hv : ContDiff ℝ 3 v) (hcs : HasCompactSupport v) :
    ∫ x, v x * deriv (fun y => deriv (fun z => deriv v z) y) x = 0 := by
  set v1 := fun x => deriv v x
  set v2 := fun x => deriv v1 x
  set v3 := fun x => deriv v2 x
  have hv1 : ContDiff ℝ 2 v1 := by simpa [v1] using ContDiff.deriv' hv
  have hv2 : ContDiff ℝ 1 v2 := by simpa [v2] using ContDiff.deriv' hv1
  have hcs_v1 : HasCompactSupport v1 := hcs.deriv
  have hcs_v2 : HasCompactSupport v2 := hcs_v1.deriv
  have hprod :
      deriv (fun x => v x * v2 x) = fun x => v1 x * v2 x + v x * v3 x := by
    funext x
    have hd := hv.differentiable (by simp : (3 : WithTop ℕ∞) ≠ 0) x
    have hd2 := hv2.differentiable one_ne_zero x
    exact (hd.hasDerivAt.mul hd2.hasDerivAt).deriv
  have hcs_prod : HasCompactSupport (fun x => v x * v2 x) :=
    HasCompactSupport.mul_left hcs_v2
  have hcont_prod : ContDiff ℝ 1 (fun x => v x * v2 x) :=
    (hv.of_le (by simp : (1 : WithTop ℕ∞) ≤ 3)).mul hv2
  have hsplit :
      ∫ x, v x * v3 x = -∫ x, v1 x * v2 x := by
    have heq : (fun x => v x * v3 x) =
        (fun x => deriv (fun x => v x * v2 x) x - v1 x * v2 x) := by
      funext x
      linarith [congr_fun hprod x]
    rw [heq, integral_sub]
    · rw [integral_deriv_eq_zero hcont_prod hcs_prod, zero_sub]
    · exact (hcont_prod.continuous_deriv le_rfl).integrable_of_hasCompactSupport
        hcs_prod.deriv
    · exact (hv1.continuous.mul hv2.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_left hcs_v2)
  have hhalf :
      ∫ x, v1 x * v2 x = 0 := by
    set w := fun x => v1 x ^ 2 / 2
    have hw : ContDiff ℝ 1 w :=
      ((hv1.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)).pow 2).div_const 2
    have hcs_w := hasCompactSupport_half_sq hcs_v1
    have hw' : deriv w = fun x => v1 x * v2 x := by
      funext x
      exact (hasDerivAt_half_sq (hv1.differentiable
        (by simp : (2 : WithTop ℕ∞) ≠ 0) x)).deriv
    rw [← hw']
    exact integral_deriv_eq_zero hw hcs_w
  linarith

private lemma integral_ut_eq_zero (sol : ConservedSolution T u)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
    ∫ x, KdV.ut u t x = 0 := by
  have hcs := hasCompactSupport_timeSlice sol ht
  have hsmooth := sol.smooth_space t ht
  have hsmooth2 := hsmooth.of_le (by decide : (2 : WithTop ℕ∞) ≤ 3)
  have hux := integral_u_mul_ux_eq_zero hsmooth2 hcs
  have huxxx := integral_uxxx_eq_zero hsmooth hcs
  have hcs_ux := hcs.deriv
  have hcs_uxxx := hasCompactSupport_uxxx hcs
  have hux_int :
      Integrable (fun x => u t x * KdV.ux u t x) :=
    hsmooth.continuous.mul (hsmooth.continuous_deriv (by decide : (1 : WithTop ℕ∞) ≤ 3))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.mul_left hcs_ux)
  have huxxx_int :
      Integrable (fun x => KdV.uxxx u t x) :=
    continuous_uxxx hsmooth |>.integrable_of_hasCompactSupport hcs_uxxx
  have hug :
      Integrable (fun x => u t x * KdV.ux u t x + KdV.uxxx u t x) :=
    hux_int.add huxxx_int
  have hint : Integrable (fun x => KdV.ut u t x) := by
    have h_eq : (fun x => KdV.ut u t x) =
        fun x => - (u t x * KdV.ux u t x + KdV.uxxx u t x) := by
      funext x
      dsimp [ut, ux, uxxx]
      linarith [sol.solution.pde t ht x]
    rw [h_eq]
    exact hug.neg
  have hpoint : ∀ x,
      KdV.ut u t x + u t x * KdV.ux u t x + KdV.uxxx u t x = 0 := by
    intro x
    dsimp [ut, ux, uxxx]
    linarith [sol.solution.pde t ht x]
  have hsum : ∫ x, KdV.ut u t x + u t x * KdV.ux u t x +
      KdV.uxxx u t x = 0 := by
    rw [← integral_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have h_assoc :
      (fun x => KdV.ut u t x + u t x * KdV.ux u t x + KdV.uxxx u t x) =
        fun x => KdV.ut u t x +
          (u t x * KdV.ux u t x + KdV.uxxx u t x) :=
    funext fun x => by ring
  have hsum' :
      ∫ x, KdV.ut u t x + (u t x * KdV.ux u t x + KdV.uxxx u t x) = 0 := by
    simpa [h_assoc] using hsum
  have hux' : ∫ x, u t x * KdV.ux u t x = 0 := by
    simp only [ux]
    exact hux
  have huxxx' : ∫ x, KdV.uxxx u t x = 0 := by
    simp only [uxxx]
    exact huxxx
  rw [integral_add hint hug, integral_add hux_int huxxx_int, hux', huxxx'] at hsum'
  linarith

private lemma integral_u_ut_eq_zero (sol : ConservedSolution T u)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
    ∫ x, u t x * KdV.ut u t x = 0 := by
  have hcs := hasCompactSupport_timeSlice sol ht
  have hsmooth := sol.smooth_space t ht
  have hsmooth2 := hsmooth.of_le (by decide : (2 : WithTop ℕ∞) ≤ 3)
  have hsq := integral_u_sq_ux_eq_zero hsmooth2 hcs
  have hxxx := integral_u_mul_uxxx_eq_zero hsmooth hcs
  have hcs_ux := hcs.deriv
  have hcs_uxxx := hasCompactSupport_uxxx hcs
  have hsq_int :
      Integrable (fun x => u t x ^ 2 * KdV.ux u t x) :=
    (hsmooth.continuous.pow 2).mul
      (hsmooth.continuous_deriv (by decide : (1 : WithTop ℕ∞) ≤ 3))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.mul_left hcs_ux)
  have hxxx_int :
      Integrable (fun x => u t x * KdV.uxxx u t x) :=
    hsmooth.continuous.mul (continuous_uxxx hsmooth)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.mul_left hcs_uxxx)
  have hneg :
      Integrable (fun x => u t x ^ 2 * KdV.ux u t x +
        u t x * KdV.uxxx u t x) :=
    hsq_int.add hxxx_int
  have hint : Integrable (fun x => u t x * KdV.ut u t x) := by
    have h_eq : (fun x => u t x * KdV.ut u t x) =
        fun x => - (u t x ^ 2 * KdV.ux u t x +
          u t x * KdV.uxxx u t x) := by
      funext x
      dsimp only [ut, ux, uxxx]
      have h := congr_arg (fun z => u t x * z) (sol.solution.pde t ht x)
      linarith
    rw [h_eq]
    exact hneg.neg
  have hpoint : ∀ x,
      u t x * KdV.ut u t x + u t x ^ 2 * KdV.ux u t x +
        u t x * KdV.uxxx u t x = 0 := by
    intro x
    dsimp only [ut, ux, uxxx]
    have h := congr_arg (fun z => u t x * z) (sol.solution.pde t ht x)
    linarith
  have hsum : ∫ x, u t x * KdV.ut u t x +
      u t x ^ 2 * KdV.ux u t x + u t x * KdV.uxxx u t x = 0 := by
    rw [← integral_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have h_assoc :
      (fun x => u t x * KdV.ut u t x + u t x ^ 2 * KdV.ux u t x +
        u t x * KdV.uxxx u t x) =
        fun x => u t x * KdV.ut u t x +
          (u t x ^ 2 * KdV.ux u t x + u t x * KdV.uxxx u t x) :=
    funext fun x => by ring
  have hsum' :
      ∫ x, u t x * KdV.ut u t x +
        (u t x ^ 2 * KdV.ux u t x + u t x * KdV.uxxx u t x) = 0 := by
    simpa [h_assoc] using hsum
  rw [integral_add hint hneg, integral_add hsq_int hxxx_int] at hsum'
  have hsq' : ∫ x, u t x ^ 2 * KdV.ux u t x =
      ∫ x, u t x ^ 2 * deriv (fun x => u t x) x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [ux])
  have hxxx' : ∫ x, u t x * KdV.uxxx u t x =
      ∫ x, u t x * deriv (fun y => deriv (fun z => deriv (fun x => u t x) z) y) x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [uxxx])
  rw [hsq', hsq, hxxx', hxxx] at hsum'
  linarith

/-- Conservation of mass in rate form: `∫ u_t dx = 0`.  This is the integrated
form of `d/dt ∫ u dx = 0` whenever the derivative can be moved under the
integral sign. -/
theorem massRate_conserved (sol : ConservedSolution T u)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
    ∫ x, KdV.ut u t x = 0 :=
  integral_ut_eq_zero sol ht

/-- Conservation of quadratic energy in rate form: `∫ u u_t dx = 0`.  This is
the integrated form of `d/dt ∫ u^2/2 dx = 0` whenever differentiation under the
integral is justified. -/
theorem energyRate_conserved (sol : ConservedSolution T u)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
    ∫ x, u t x * KdV.ut u t x = 0 :=
  integral_u_ut_eq_zero sol ht

end ConservedSolution

end KdV

end
