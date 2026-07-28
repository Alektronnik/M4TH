/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.Algebra.Support
public import KdV.Basic

/-!
# Conservation laws for compactly supported KdV solutions

For smooth KdV solutions with uniformly compact spatial support, this file proves
the formal conservation identities for mass and quadratic energy:

* `∫ u_t = 0`;
* `∫ u u_t = 0`.

The proofs use the five basic vanishing identities behind the classical
calculation: total derivatives integrate to zero under compact support,
`∫ u u_x = 0`, `∫ u^2 u_x = 0`, `∫ u_xxx = 0`, and the double integration by
parts identity `∫ u u_xxx = 0`.

## Main definitions

- `KdV.mass`: total spatial mass of a slice.
- `KdV.energy`: quadratic spatial energy of a slice.
- `KdV.ConservedSolution`: a KdV solution with a fixed compact set containing
  the support of every spatial slice.

## Main results

- `KdV.ConservedSolution.massRate_conserved`.
- `KdV.ConservedSolution.energyRate_conserved`.

## Implementation notes

The compact-support assumption is deliberately explicit.  At Mathlib review
time, the generic lemma `integral_deriv_eq_zero` should be compared with any
existing theorem of the form `HasCompactSupport.integral_deriv_eq_zero`, and the
special cases should be replaced by the most general available statement.

## Tags

KdV equation, conservation law, compact support, integration by parts
-/

open MeasureTheory

@[expose] public section

namespace KdV

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
