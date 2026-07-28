/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Homeomorph.Defs
public import ConservationLaws.TestFunction

/-!
# Galilean change of coordinates for test functions

Along the moving frame `x = ξ + s * t` (velocity `s`), the time-derivative term
of the weak formulation of a conservation law against a *constant* state becomes
a total time derivative.  Its time integral then vanishes by the support
conditions of the test function at `t = 0, T`, and Fubini's theorem propagates
this cancellation to the double integrals over the half-planes
`(0, T) × (-∞, 0]` and `(0, T) × (0, ∞)`.

This is the analytic engine behind the exact reduction of the shock residual to
the Rankine–Hugoniot jump proved in `ConservationLaws.ShockReduction`.

## Main definitions

- `ConservationLaw.TestFunction.galilean`: the pullback `φ (t, ξ + s t)`.
- `ConservationLaw.galileanHomeo`: the plane homeomorphism `(t, ξ) ↦ (t, ξ + s t)`.
- `ConservationLaw.TestFunction.galileanTimeDeriv`: the total time derivative in
  the moving frame, as a joint function on the plane.

## Main results

- `ConservationLaw.TestFunction.deriv_galilean_time`: the chain rule
  `d/dt φ(t, ξ + s t) = ∂ₜφ + s ∂ₓφ` (evaluated on the moving line).
- `ConservationLaw.TestFunction.constant_state_galilean`: for constants `a, F`,
  the combination `a ∂ₜφ + F ∂ₓφ` on the moving line splits into a total time
  derivative plus `(F - s a) ∂ₓφ`.
- `ConservationLaw.TestFunction.integral_Ioo_Iic_galilean_time_deriv_zero`,
  `ConservationLaw.TestFunction.integral_Ioo_Ioi_galilean_time_deriv_zero`:
  the double integrals of the total-time-derivative term vanish
  (Fubini + one-dimensional cancellation).

## Implementation notes

Integrability certificates are obtained by transporting compact support through
`galileanHomeo` (`HasCompactSupport.comp_homeomorph`) rather than by direct
estimates; this keeps every integrability proof a composition of continuity and
compact-support facts.
-/

open MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ConservationLaw

/-- The Galilean homeomorphism `(t, ξ) ↦ (t, ξ + s t)` of the plane. -/
noncomputable def galileanHomeo (s : ℝ) : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun p := (p.1, p.2 + s * p.1)
  invFun p := (p.1, p.2 - s * p.1)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

namespace TestFunction

/-- A test function seen from the Galilean frame `x = ξ + s t`. -/
noncomputable def galilean {T : ℝ} (φ : TestFunction T) (s : ℝ) (t ξ : ℝ) : ℝ :=
  φ t (ξ + s * t)

/-- Chain rule in time for the Galilean pullback. -/
lemma deriv_galilean_time {T : ℝ} (φ : TestFunction T) (s t ξ : ℝ) :
    deriv (fun τ => φ.galilean s τ ξ) t =
      φ.dt t (ξ + s * t) + s * φ.dx t (ξ + s * t) := by
  let γ : ℝ → ℝ × ℝ := fun τ => (τ, ξ + s * τ)
  have hγ : HasDerivAt γ (1, s) t := by
    have hsecond : HasDerivAt (fun τ : ℝ => ξ + s * τ) s t := by
      exact (hasDerivAt_const_mul (x := t) s).const_add ξ
    exact hasDerivAt_prodMk (hasDerivAt_id' t) hsecond
  have hφ : DifferentiableAt ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (γ t) :=
    (φ.smooth.differentiable (by simp)) (γ t)
  have hcomp := hφ.hasFDerivAt.comp_hasDerivAt t hγ
  rw [fderiv_apply_decomp φ.toFun (γ t) (1, s) hφ] at hcomp
  dsimp [γ] at hcomp
  simpa only [Function.comp_def, one_mul, galilean, dt, dx] using hcomp.deriv

/-- Galilean transformation of the weak integrand against a constant state `a`
with flux value `F`.  The time term becomes a total derivative.  In applications
`F = f a` for the flux `f` of the conservation law. -/
lemma constant_state_galilean {T : ℝ} (φ : TestFunction T)
    (a F s t ξ : ℝ) :
    a * φ.dt t (ξ + s * t) + F * φ.dx t (ξ + s * t) =
      a * deriv (fun τ => φ.galilean s τ ξ) t +
        (F - s * a) * φ.dx t (ξ + s * t) := by
  rw [φ.deriv_galilean_time s t ξ]
  ring

/-- The Galilean pullback is `C¹` in time for each `ξ`. -/
lemma contDiff_one_galilean_time {T : ℝ} (φ : TestFunction T) (s ξ : ℝ) :
    ContDiff ℝ 1 (fun t => φ.galilean s t ξ) := by
  have hcurve : ContDiff ℝ 1 (fun t : ℝ => (t, ξ + s * t)) := by
    exact contDiff_id.prodMk (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hsmooth : ContDiff ℝ 1 (fun p : ℝ × ℝ => φ p.1 p.2) :=
    φ.smooth.of_le (by simp)
  simpa only [galilean, Function.comp_def] using hsmooth.comp hcurve

/-- The time integral of the total Galilean derivative vanishes by the support
conditions at `t = 0, T`. -/
lemma integral_Ioo_deriv_galilean_time {T : ℝ} (φ : TestFunction T)
    (s ξ : ℝ) :
    (∫ t in Ioo 0 T, deriv (fun τ => φ.galilean s τ ξ) t) = 0 := by
  by_cases hT : 0 ≤ T
  · have hg := φ.contDiff_one_galilean_time s ξ
    have hFTC :
        (∫ t in (0 : ℝ)..T, deriv (fun τ => φ.galilean s τ ξ) t) =
          φ.galilean s T ξ - φ.galilean s 0 ξ := by
      exact intervalIntegral.integral_deriv_eq_sub
        (fun t _ => (hg.differentiable (by norm_num)) t)
        ((hg.continuous_deriv le_rfl).intervalIntegrable 0 T)
    rw [intervalIntegral.integral_of_le hT] at hFTC
    rw [integral_Ioc_eq_integral_Ioo] at hFTC
    simpa [galilean] using hFTC
  · rw [Ioo_eq_empty (not_lt_of_ge (le_of_not_ge hT))]
    simp

/-- Version multiplied by a constant state, as it appears in the transformed
integrand. -/
lemma integral_Ioo_const_mul_deriv_galilean_time {T : ℝ}
    (φ : TestFunction T) (C s ξ : ℝ) :
    (∫ t in Ioo 0 T, C * deriv (fun τ => φ.galilean s τ ξ) t) = 0 := by
  rw [integral_const_mul]
  rw [φ.integral_Ioo_deriv_galilean_time s ξ]
  simp

/-! ### Galilean integrability (technical `MeasureTheory` certificates) -/

/-- Joint time derivative `∂ₜφ` as a function on `(t, x)`. -/
noncomputable def jointDt {T : ℝ} (φ : TestFunction T) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun q : ℝ × ℝ => φ q.1 q.2) p (1, 0)

/-- Joint space derivative `∂ₓφ` as a function on `(t, x)`. -/
noncomputable def jointDx {T : ℝ} (φ : TestFunction T) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun q : ℝ × ℝ => φ q.1 q.2) p (0, 1)

lemma jointDt_eq {T : ℝ} (φ : TestFunction T) (p : ℝ × ℝ) :
    φ.jointDt p = φ.dt p.1 p.2 := by
  simp only [jointDt, TestFunction.dt]
  exact fderiv_coord_fst φ.toFun p ((φ.smooth.differentiable (by simp)) p)

lemma jointDx_eq {T : ℝ} (φ : TestFunction T) (p : ℝ × ℝ) :
    φ.jointDx p = φ.dx p.1 p.2 := by
  simp only [jointDx, TestFunction.dx]
  exact fderiv_coord_snd φ.toFun p ((φ.smooth.differentiable (by simp)) p)

lemma continuous_jointDt {T : ℝ} (φ : TestFunction T) :
    Continuous φ.jointDt := by
  have h := φ.smooth.continuous_fderiv_apply (by simp)
  have hconst : Continuous fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ)) := continuous_const
  exact (h.comp (continuous_id.prodMk hconst)).congr fun p => by simp [jointDt]

lemma continuous_jointDx {T : ℝ} (φ : TestFunction T) :
    Continuous φ.jointDx := by
  have h := φ.smooth.continuous_fderiv_apply (by simp)
  have hconst : Continuous fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ)) := continuous_const
  exact (h.comp (continuous_id.prodMk hconst)).congr fun p => by simp [jointDx]

private lemma jointDt_eq_zero_of_notMem_tsupport {T : ℝ} (φ : TestFunction T) {p : ℝ × ℝ}
    (hp : p ∉ tsupport (fun q : ℝ × ℝ => φ q.1 q.2)) : φ.jointDt p = 0 := by
  have hf : fderiv ℝ (fun q : ℝ × ℝ => φ q.1 q.2) p = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := fun q : ℝ × ℝ => φ q.1 q.2) (x := p) hp
  simp [jointDt, hf]

private lemma jointDx_eq_zero_of_notMem_tsupport {T : ℝ} (φ : TestFunction T) {p : ℝ × ℝ}
    (hp : p ∉ tsupport (fun q : ℝ × ℝ => φ q.1 q.2)) : φ.jointDx p = 0 := by
  have hf : fderiv ℝ (fun q : ℝ × ℝ => φ q.1 q.2) p = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := fun q : ℝ × ℝ => φ q.1 q.2) (x := p) hp
  simp [jointDx, hf]

private lemma support_jointDt_subset {T : ℝ} (φ : TestFunction T) :
    Function.support φ.jointDt ⊆ tsupport (fun q : ℝ × ℝ => φ q.1 q.2) := by
  intro p hp
  by_contra hmem
  exact hp (φ.jointDt_eq_zero_of_notMem_tsupport hmem)

private lemma support_jointDx_subset {T : ℝ} (φ : TestFunction T) :
    Function.support φ.jointDx ⊆ tsupport (fun q : ℝ × ℝ => φ q.1 q.2) := by
  intro p hp
  by_contra hmem
  exact hp (φ.jointDx_eq_zero_of_notMem_tsupport hmem)

lemma hasCompactSupport_jointDt {T : ℝ} (φ : TestFunction T) :
    HasCompactSupport φ.jointDt :=
  φ.compactSupport.mono' (φ.support_jointDt_subset)

lemma hasCompactSupport_jointDx {T : ℝ} (φ : TestFunction T) :
    HasCompactSupport φ.jointDx :=
  φ.compactSupport.mono' (φ.support_jointDx_subset)

private lemma hasCompactSupport_const_mul_jointDx {T : ℝ} (φ : TestFunction T) (s : ℝ) :
    HasCompactSupport (fun q : ℝ × ℝ => s * φ.jointDx q) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
    exact HasCompactSupport.zero
  · refine HasCompactSupport.mono (φ.hasCompactSupport_jointDx) ?_
    rintro p hp
    simp only [Function.mem_support] at hp ⊢
    exact fun h => hp (by simp [h])

private lemma hasCompactSupport_jointGalileanDeriv {T : ℝ} (φ : TestFunction T) (s : ℝ) :
    HasCompactSupport (fun q : ℝ × ℝ => φ.jointDt q + s * φ.jointDx q) :=
  (φ.hasCompactSupport_jointDt).add (φ.hasCompactSupport_const_mul_jointDx s)

/-- Galilean total time derivative as a joint function on `(t, ξ)`. -/
noncomputable def galileanTimeDeriv {T : ℝ} (φ : TestFunction T) (s : ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun τ => φ.galilean s τ p.2) p.1

lemma galileanTimeDeriv_eq {T : ℝ} (φ : TestFunction T) (s : ℝ) (p : ℝ × ℝ) :
    φ.galileanTimeDeriv s p =
      φ.dt p.1 (p.2 + s * p.1) + s * φ.dx p.1 (p.2 + s * p.1) := by
  simpa [galileanTimeDeriv, galilean] using φ.deriv_galilean_time s p.1 p.2

@[simp] lemma galileanTimeDeriv_uncurry {T : ℝ} (φ : TestFunction T) (s t ξ : ℝ) :
    φ.galileanTimeDeriv s (t, ξ) = deriv (fun τ => φ.galilean s τ ξ) t :=
  rfl

lemma galileanTimeDeriv_eq_joint {T : ℝ} (φ : TestFunction T) (s : ℝ) (p : ℝ × ℝ) :
    φ.galileanTimeDeriv s p =
      (fun q : ℝ × ℝ => φ.jointDt q + s * φ.jointDx q) (galileanHomeo s p) := by
  simp [galileanTimeDeriv_eq, jointDt_eq, jointDx_eq, galileanHomeo]

lemma integrable_galileanTimeDeriv {T : ℝ} (φ : TestFunction T) (s : ℝ) :
    Integrable (φ.galileanTimeDeriv s) := by
  set joint : ℝ × ℝ → ℝ := fun q => φ.jointDt q + s * φ.jointDx q
  have hcont : Continuous joint :=
    φ.continuous_jointDt.add (continuous_const.mul φ.continuous_jointDx)
  have hsupport : HasCompactSupport (joint ∘ (galileanHomeo s)) :=
    (φ.hasCompactSupport_jointGalileanDeriv s).comp_homeomorph (galileanHomeo s)
  have h : Integrable (joint ∘ (galileanHomeo s)) :=
    (hcont.comp (galileanHomeo s).continuous).integrable_of_hasCompactSupport hsupport
  convert h using 1
  funext p
  simpa [joint] using φ.galileanTimeDeriv_eq_joint s p

lemma integrable_smul_dx_galilean {T : ℝ} (φ : TestFunction T) (s c : ℝ) :
    Integrable (fun p : ℝ × ℝ => c * φ.dx p.1 (p.2 + s * p.1)) := by
  set f : ℝ × ℝ → ℝ := (fun q => c * φ.jointDx q) ∘ (galileanHomeo s)
  have hcont : Continuous f :=
    (continuous_const.mul φ.continuous_jointDx).comp (galileanHomeo s).continuous
  have heq :
      (fun p : ℝ × ℝ => c * φ.dx p.1 (p.2 + s * p.1)) = f := by
    funext p
    simp [f, jointDx_eq, galileanHomeo]
  have hsupport : HasCompactSupport f :=
    (φ.hasCompactSupport_const_mul_jointDx c).comp_homeomorph (galileanHomeo s)
  rw [heq]
  exact hcont.integrable_of_hasCompactSupport hsupport

lemma integrableOn_Ioo_Iic_smul_dx_galilean {T : ℝ} (φ : TestFunction T) (s c : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => c * φ.dx p.1 (p.2 + s * p.1)) (Ioo 0 T ×ˢ Iic 0) planeMeasure :=
  integrableOn_plane_of_integrable (φ.integrable_smul_dx_galilean s c)

lemma integrableOn_Ioo_Ioi_smul_dx_galilean {T : ℝ} (φ : TestFunction T) (s c : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => c * φ.dx p.1 (p.2 + s * p.1)) (Ioo 0 T ×ˢ Ioi 0) planeMeasure :=
  integrableOn_plane_of_integrable (φ.integrable_smul_dx_galilean s c)

/-- Fubini + `integral_Ioo_const_mul_deriv_galilean_time` on `Ioo × Iic`. -/
lemma integral_Ioo_Iic_galilean_time_deriv_zero {T : ℝ} (φ : TestFunction T)
    (C s : ℝ) :
    (∫ t in Ioo 0 T, ∫ ξ in Iic 0,
      C * deriv (fun τ => φ.galilean s τ ξ) t) = 0 := by
  set g : ℝ × ℝ → ℝ := fun p => C * φ.galileanTimeDeriv s p
  have hg : IntegrableOn g (Ioo 0 T ×ˢ Iic 0) planeMeasure :=
    integrableOn_plane_of_integrable ((φ.integrable_galileanTimeDeriv s).const_mul C)
  have hf_swap :
      Integrable (Function.uncurry fun t ξ => g (t, ξ))
        ((volume.restrict (Ioo 0 T)).prod (volume.restrict (Iic 0))) := by
    dsimp [IntegrableOn, planeMeasure, Function.uncurry] at hg ⊢
    rw [Measure.prod_restrict]
    exact hg
  calc
    ∫ t in Ioo 0 T, ∫ ξ in Iic 0, C * deriv (fun τ => φ.galilean s τ ξ) t
        = ∫ p in Ioo 0 T ×ˢ Iic 0, g p := by
      simpa [g, galileanTimeDeriv_uncurry] using
        (setIntegral_plane_prod_symm hg).trans setIntegral_plane.symm
    _ = ∫ ξ in Iic 0, ∫ t in Ioo 0 T, g (t, ξ) := by
      trans (∫ t in Ioo 0 T, ∫ ξ in Iic 0, g (t, ξ))
      · rw [setIntegral_plane]
        exact setIntegral_plane_prod hg
      · exact integral_integral_swap (μ := volume.restrict (Ioo 0 T))
          (ν := volume.restrict (Iic 0)) hf_swap
    _ = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun ξ _ => ?_
      simpa [g, galileanTimeDeriv] using φ.integral_Ioo_const_mul_deriv_galilean_time C s ξ

/-- Right (`Ioi`) version of the same Fubini argument. -/
lemma integral_Ioo_Ioi_galilean_time_deriv_zero {T : ℝ} (φ : TestFunction T)
    (C s : ℝ) :
    (∫ t in Ioo 0 T, ∫ ξ in Ioi 0,
      C * deriv (fun τ => φ.galilean s τ ξ) t) = 0 := by
  set g : ℝ × ℝ → ℝ := fun p => C * φ.galileanTimeDeriv s p
  have hg : IntegrableOn g (Ioo 0 T ×ˢ Ioi 0) planeMeasure :=
    integrableOn_plane_of_integrable ((φ.integrable_galileanTimeDeriv s).const_mul C)
  have hf_swap :
      Integrable (Function.uncurry fun t ξ => g (t, ξ))
        ((volume.restrict (Ioo 0 T)).prod (volume.restrict (Ioi 0))) := by
    dsimp [IntegrableOn, planeMeasure, Function.uncurry] at hg ⊢
    rw [Measure.prod_restrict]
    exact hg
  calc
    ∫ t in Ioo 0 T, ∫ ξ in Ioi 0, C * deriv (fun τ => φ.galilean s τ ξ) t
        = ∫ p in Ioo 0 T ×ˢ Ioi 0, g p := by
      simpa [g, galileanTimeDeriv_uncurry] using
        (setIntegral_plane_prod_symm hg).trans setIntegral_plane.symm
    _ = ∫ ξ in Ioi 0, ∫ t in Ioo 0 T, g (t, ξ) := by
      trans (∫ t in Ioo 0 T, ∫ ξ in Ioi 0, g (t, ξ))
      · rw [setIntegral_plane]
        exact setIntegral_plane_prod hg
      · exact integral_integral_swap (μ := volume.restrict (Ioo 0 T))
          (ν := volume.restrict (Ioi 0)) hf_swap
    _ = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun ξ _ => ?_
      simpa [g, galileanTimeDeriv] using φ.integral_Ioo_const_mul_deriv_galilean_time C s ξ

end TestFunction

end ConservationLaw

end
