/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import ConservationLaws.Galilean
public import ConservationLaws.ShockProfile

/-!
# Exact reduction of the shock residual to the Rankine–Hugoniot jump

The fundamental theorem of this development: for **any** flux `f : ℝ → ℝ` and
any states and speed, the distributional residual of the travelling step
collapses exactly to the boundary integral of the Rankine–Hugoniot deficit along
the moving interface,

  `weakResidual f (shockProfile uL uR s) φ
     = ∫_{(0,T)} ((f uL - f uR) - s (uL - uR)) · φ (t, s t) dt`.

In particular the step is a weak solution **iff** its speed satisfies the
Rankine–Hugoniot condition — with no hypotheses whatsoever on the flux, which
only ever enters through the two constants `f uL` and `f uR`.

The proof proceeds in three phases:

1. *Static domain* (spatial shifts): the translation `x = ξ + s t` converts the
   moving half-lines into `(-∞, 0]` and `(0, ∞)`, with translation invariance of
   Lebesgue measure.
2. *Analytic evaluation and Fubini*: on each half, the Galilean total-time
   derivative integrates to zero (`ConservationLaws.Galilean`) and only the
   `∂ₓφ` term survives, evaluated by the improper FTC boundary formulas.
3. *Assembly*: the spatial split of `ConservationLaws.ShockProfile`, additivity
   of the time marginals, and the two half-plane collapses.

## Main results

- `ConservationLaw.shock_integral_left`, `ConservationLaw.shock_integral_right`:
  each half of the double integral collapses to a boundary term.
- `ConservationLaw.hasShockIntegralReduction`: the reduction holds for all
  parameters (the fundamental theorem).
- `ConservationLaw.isWeakSolution_shockProfile_of_rankineHugoniot`: the
  unconditional packaging — a Rankine–Hugoniot step is a weak solution.

## Tags

shock wave, Rankine-Hugoniot, Fubini, conservation law, weak solution
-/

open MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ConservationLaw

/-! ### Phase 1: static domain via spatial shifts -/

/-- Spatial translation `x = ξ + c`: converts `Iic c` into `Iic 0`. -/
private lemma integral_Iic_shift (c : ℝ) {f : ℝ → ℝ} :
    (∫ x in Iic c, f x) = ∫ ξ in Iic 0, f (ξ + c) := by
  let e := (Homeomorph.addRight c)
  have he := e.isClosedEmbedding.measurableEmbedding
  have hμ : volume = Measure.map e volume := by
    simpa only [e, Homeomorph.coe_addRight] using (map_add_right_eq_self volume c).symm
  have hpre :
      ∫ ξ in Iic 0, f (ξ + c) = ∫ ξ in e ⁻¹' Iic c, f (e ξ) := by
    simp only [e, Homeomorph.coe_addRight, preimage_add_const_Iic, sub_self]
  calc
    ∫ x in Iic c, f x
        = ∫ x in Iic c, f x ∂(Measure.map e volume) :=
      congr_arg (fun μ => ∫ x in Iic c, f x ∂μ) hμ
    _ = ∫ ξ in e ⁻¹' Iic c, f (e ξ) := he.setIntegral_map (μ := volume) f (Iic c)
    _ = ∫ ξ in Iic 0, f (ξ + c) := hpre.symm

/-- Spatial translation `x = ξ + c`: converts `Ioi c` into `Ioi 0`. -/
private lemma integral_Ioi_shift (c : ℝ) {f : ℝ → ℝ} :
    (∫ x in Ioi c, f x) = ∫ ξ in Ioi 0, f (ξ + c) := by
  let e := (Homeomorph.addRight c)
  have he := e.isClosedEmbedding.measurableEmbedding
  have hμ : volume = Measure.map e volume := by
    simpa only [e, Homeomorph.coe_addRight] using (map_add_right_eq_self volume c).symm
  have hpre :
      ∫ ξ in Ioi 0, f (ξ + c) = ∫ ξ in e ⁻¹' Ioi c, f (e ξ) := by
    simp only [e, Homeomorph.coe_addRight, preimage_add_const_Ioi, sub_self]
  calc
    ∫ x in Ioi c, f x
        = ∫ x in Ioi c, f x ∂(Measure.map e volume) :=
      congr_arg (fun μ => ∫ x in Ioi c, f x ∂μ) hμ
    _ = ∫ ξ in e ⁻¹' Ioi c, f (e ξ) := he.setIntegral_map (μ := volume) f (Ioi c)
    _ = ∫ ξ in Ioi 0, f (ξ + c) := hpre.symm

lemma integral_Iic_shift_weakIntegrand {f : ℝ → ℝ} {T : ℝ}
    (φ : TestFunction T) (uL s t : ℝ) :
    (∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) =
    ∫ ξ in Iic 0, weakIntegrand f (fun _ _ => uL) φ t (ξ + s * t) :=
  integral_Iic_shift (s * t)

lemma integral_Ioi_shift_weakIntegrand {f : ℝ → ℝ} {T : ℝ}
    (φ : TestFunction T) (uR s t : ℝ) :
    (∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) =
    ∫ ξ in Ioi 0, weakIntegrand f (fun _ _ => uR) φ t (ξ + s * t) :=
  integral_Ioi_shift (s * t)

/-- Time marginal: the spatial integral over the moving left domain is
integrable in `t`. -/
private lemma integrableOn_time_weakIntegrand_Iic {f : ℝ → ℝ} {T : ℝ}
    (φ : TestFunction T) (uL s : ℝ) :
    IntegrableOn
      (fun t => ∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) (Ioo 0 T) := by
  set G : ℝ × ℝ → ℝ := fun p => weakIntegrand f (fun _ _ => uL) φ p.1 (p.2 + s * p.1)
  have hf₁₂ : IntegrableOn
      (fun p => uL * φ.galileanTimeDeriv s p + (f uL - s * uL) * φ.dx p.1 (p.2 + s * p.1))
      (Ioo 0 T ×ˢ Iic 0) planeMeasure :=
    (integrableOn_plane_of_integrable ((φ.integrable_galileanTimeDeriv s).const_mul uL)).add
      (φ.integrableOn_Ioo_Iic_smul_dx_galilean s (f uL - s * uL))
  have hG_eq : G = fun p =>
      uL * φ.galileanTimeDeriv s p + (f uL - s * uL) * φ.dx p.1 (p.2 + s * p.1) := by
    funext p
    simp only [G]
    exact φ.constant_state_galilean uL (f uL) s p.1 p.2
  have hG : IntegrableOn G (Ioo 0 T ×ˢ Iic 0) planeMeasure := hG_eq ▸ hf₁₂
  have hG_int : Integrable G ((volume.restrict (Ioo 0 T)).prod (volume.restrict (Iic 0))) := by
    dsimp [IntegrableOn, planeMeasure] at hG
    convert hG using 2
    rw [Measure.prod_restrict]
  have hmarg := Integrable.integral_prod_left (E := ℝ) hG_int
  have hfun :
      (fun t => ∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) =
        fun t => ∫ ξ in Iic 0, G (t, ξ) := by
    funext t
    simp only [G]
    exact integral_Iic_shift_weakIntegrand φ uL s t
  simpa [IntegrableOn, hfun] using hmarg

private lemma integrableOn_time_weakIntegrand_Ioi {f : ℝ → ℝ} {T : ℝ}
    (φ : TestFunction T) (uR s : ℝ) :
    IntegrableOn
      (fun t => ∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) (Ioo 0 T) := by
  set G : ℝ × ℝ → ℝ := fun p => weakIntegrand f (fun _ _ => uR) φ p.1 (p.2 + s * p.1)
  have hf₁₂ : IntegrableOn
      (fun p => uR * φ.galileanTimeDeriv s p + (f uR - s * uR) * φ.dx p.1 (p.2 + s * p.1))
      (Ioo 0 T ×ˢ Ioi 0) planeMeasure :=
    (integrableOn_plane_of_integrable ((φ.integrable_galileanTimeDeriv s).const_mul uR)).add
      (φ.integrableOn_Ioo_Ioi_smul_dx_galilean s (f uR - s * uR))
  have hG_eq : G = fun p =>
      uR * φ.galileanTimeDeriv s p + (f uR - s * uR) * φ.dx p.1 (p.2 + s * p.1) := by
    funext p
    simp only [G]
    exact φ.constant_state_galilean uR (f uR) s p.1 p.2
  have hG : IntegrableOn G (Ioo 0 T ×ˢ Ioi 0) planeMeasure := hG_eq ▸ hf₁₂
  have hG_int : Integrable G ((volume.restrict (Ioo 0 T)).prod (volume.restrict (Ioi 0))) := by
    dsimp [IntegrableOn, planeMeasure] at hG
    convert hG using 2
    rw [Measure.prod_restrict]
  have hmarg := Integrable.integral_prod_left (E := ℝ) hG_int
  have hfun :
      (fun t => ∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) =
        fun t => ∫ ξ in Ioi 0, G (t, ξ) := by
    funext t
    simp only [G]
    exact integral_Ioi_shift_weakIntegrand φ uR s t
  simpa [IntegrableOn, hfun] using hmarg

/-- Boundary formula on the shifted left half-line. -/
private lemma integral_Iic_shift_dx {T : ℝ} (φ : TestFunction T) (s t : ℝ) :
    (∫ ξ in Iic 0, φ.dx t (ξ + s * t)) = φ t (s * t) := by
  calc
    ∫ ξ in Iic 0, φ.dx t (ξ + s * t)
        = ∫ x in Iic (s * t), φ.dx t x := (integral_Iic_shift (s * t)).symm
    _ = φ t (s * t) := φ.integral_Iic_dx t (s * t)

/-- Boundary formula on the shifted right half-line. -/
private lemma integral_Ioi_shift_dx {T : ℝ} (φ : TestFunction T) (s t : ℝ) :
    (∫ ξ in Ioi 0, φ.dx t (ξ + s * t)) = -φ t (s * t) := by
  calc
    ∫ ξ in Ioi 0, φ.dx t (ξ + s * t)
        = ∫ x in Ioi (s * t), φ.dx t x := (integral_Ioi_shift (s * t)).symm
    _ = -φ t (s * t) := φ.integral_Ioi_dx t (s * t)

/-- The interface boundary function `t ↦ c · φ (t, s t)` has compact support. -/
private lemma hasCompactSupport_shock_boundary {T : ℝ} (φ : TestFunction T) (c s : ℝ) :
    HasCompactSupport (fun t => c * φ t (s * t)) := by
  by_cases hc : c = 0
  · subst hc
    simp
    exact HasCompactSupport.zero
  · let K := Prod.fst '' tsupport (fun p : ℝ × ℝ => φ p.1 p.2)
    refine HasCompactSupport.intro (φ.compactSupport.image continuous_fst) ?_
    intro t ht
    by_contra hφ
    have hpTSupport : (t, s * t) ∈ tsupport (fun p : ℝ × ℝ => φ p.1 p.2) := by
      have hpSupport : (t, s * t) ∈ Function.support (fun p : ℝ × ℝ => φ p.1 p.2) := by
        simpa [Function.mem_support, hc] using hφ
      exact subset_closure hpSupport
    exact ht ⟨(t, s * t), hpTSupport, rfl⟩

private lemma integrableOn_shock_boundary {T : ℝ} (φ : TestFunction T) (c s : ℝ) :
    IntegrableOn (fun t => c * φ t (s * t)) (Ioo 0 T) := by
  have hcurve : Continuous fun t : ℝ => (t, s * t) :=
    continuous_id.prodMk (continuous_const.mul continuous_id)
  have hcont : Continuous (fun t => c * φ t (s * t)) :=
    continuous_const.mul (φ.smooth.continuous.comp hcurve)
  exact hcont.integrable_of_hasCompactSupport (hasCompactSupport_shock_boundary φ c s) |>.integrableOn

/-! ### Phase 2: analytic evaluation and Fubini -/

/-- The time integral of the left half collapses to the boundary term. -/
lemma shock_integral_left {f : ℝ → ℝ} {T : ℝ} (φ : TestFunction T) (uL s : ℝ) :
    (∫ t in Ioo 0 T, ∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) =
    ∫ t in Ioo 0 T, (f uL - s * uL) * φ t (s * t) := by
  set f₁ : ℝ × ℝ → ℝ := fun p => uL * φ.galileanTimeDeriv s p
  set f₂ : ℝ × ℝ → ℝ := fun p => (f uL - s * uL) * φ.dx p.1 (p.2 + s * p.1)
  have hf₁ : IntegrableOn f₁ (Ioo 0 T ×ˢ Iic 0) planeMeasure := by
    simpa [f₁] using integrableOn_plane_of_integrable
      ((φ.integrable_galileanTimeDeriv s).const_mul uL)
  have hf₂ : IntegrableOn f₂ (Ioo 0 T ×ˢ Iic 0) planeMeasure :=
    φ.integrableOn_Ioo_Iic_smul_dx_galilean s (f uL - s * uL)
  have hf₁₂ : IntegrableOn (f₁ + f₂) (Ioo 0 T ×ˢ Iic 0) planeMeasure := hf₁.add hf₂
  calc
    (∫ t in Ioo 0 T, ∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x)
        = ∫ t in Ioo 0 T, ∫ ξ in Iic 0, weakIntegrand f (fun _ _ => uL) φ t (ξ + s * t) := by
      congr 1
      funext t
      exact integral_Iic_shift_weakIntegrand φ uL s t
    _ = ∫ t in Ioo 0 T, ∫ ξ in Iic 0, f₁ (t, ξ) + f₂ (t, ξ) := by
      congr 1
      funext t
      congr 1
      funext ξ
      simp only [f₁, f₂, TestFunction.galileanTimeDeriv]
      exact φ.constant_state_galilean uL (f uL) s t ξ
    _ = ∫ p in Ioo 0 T ×ˢ Iic 0, f₁ p + f₂ p := by
      rw [setIntegral_plane]
      exact (setIntegral_plane_prod hf₁₂).symm
    _ = (∫ p in Ioo 0 T ×ˢ Iic 0, f₁ p) + (∫ p in Ioo 0 T ×ˢ Iic 0, f₂ p) :=
      integral_add hf₁ hf₂
    _ = ∫ p in Ioo 0 T ×ˢ Iic 0, f₂ p := by
      have h₁ : ∫ p in Ioo 0 T ×ˢ Iic 0, f₁ p = 0 := by
        rw [setIntegral_plane]
        refine (setIntegral_plane_prod hf₁).trans ?_
        simpa [f₁, TestFunction.galileanTimeDeriv_uncurry] using
          φ.integral_Ioo_Iic_galilean_time_deriv_zero uL s
      rw [h₁, zero_add]
    _ = ∫ t in Ioo 0 T, ∫ ξ in Iic 0, f₂ (t, ξ) := by
      rw [setIntegral_plane]
      exact setIntegral_plane_prod hf₂
    _ = ∫ t in Ioo 0 T, (f uL - s * uL) * φ t (s * t) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      rw [integral_const_mul]
      congr 1
      exact integral_Iic_shift_dx φ s t

/-- The right-half integral collapses to the boundary term with opposite sign. -/
lemma shock_integral_right {f : ℝ → ℝ} {T : ℝ} (φ : TestFunction T) (uR s : ℝ) :
    (∫ t in Ioo 0 T, ∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) =
    - ∫ t in Ioo 0 T, (f uR - s * uR) * φ t (s * t) := by
  set f₁ : ℝ × ℝ → ℝ := fun p => uR * φ.galileanTimeDeriv s p
  set f₂ : ℝ × ℝ → ℝ := fun p => (f uR - s * uR) * φ.dx p.1 (p.2 + s * p.1)
  have hf₁ : IntegrableOn f₁ (Ioo 0 T ×ˢ Ioi 0) planeMeasure := by
    simpa [f₁] using integrableOn_plane_of_integrable
      ((φ.integrable_galileanTimeDeriv s).const_mul uR)
  have hf₂ : IntegrableOn f₂ (Ioo 0 T ×ˢ Ioi 0) planeMeasure :=
    φ.integrableOn_Ioo_Ioi_smul_dx_galilean s (f uR - s * uR)
  have hf₁₂ : IntegrableOn (f₁ + f₂) (Ioo 0 T ×ˢ Ioi 0) planeMeasure := hf₁.add hf₂
  calc
    (∫ t in Ioo 0 T, ∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x)
        = ∫ t in Ioo 0 T, ∫ ξ in Ioi 0, weakIntegrand f (fun _ _ => uR) φ t (ξ + s * t) := by
      congr 1
      funext t
      exact integral_Ioi_shift_weakIntegrand φ uR s t
    _ = ∫ t in Ioo 0 T, ∫ ξ in Ioi 0, f₁ (t, ξ) + f₂ (t, ξ) := by
      congr 1
      funext t
      congr 1
      funext ξ
      simp only [f₁, f₂, TestFunction.galileanTimeDeriv]
      exact φ.constant_state_galilean uR (f uR) s t ξ
    _ = ∫ p in Ioo 0 T ×ˢ Ioi 0, f₁ p + f₂ p := by
      rw [setIntegral_plane]
      exact (setIntegral_plane_prod hf₁₂).symm
    _ = (∫ p in Ioo 0 T ×ˢ Ioi 0, f₁ p) + (∫ p in Ioo 0 T ×ˢ Ioi 0, f₂ p) :=
      integral_add hf₁ hf₂
    _ = ∫ p in Ioo 0 T ×ˢ Ioi 0, f₂ p := by
      have h₁ : ∫ p in Ioo 0 T ×ˢ Ioi 0, f₁ p = 0 := by
        rw [setIntegral_plane]
        refine (setIntegral_plane_prod hf₁).trans ?_
        simpa [f₁, TestFunction.galileanTimeDeriv_uncurry] using
          φ.integral_Ioo_Ioi_galilean_time_deriv_zero uR s
      rw [h₁, zero_add]
    _ = ∫ t in Ioo 0 T, ∫ ξ in Ioi 0, f₂ (t, ξ) := by
      rw [setIntegral_plane]
      exact setIntegral_plane_prod hf₂
    _ = - ∫ t in Ioo 0 T, (f uR - s * uR) * φ t (s * t) := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      calc
        ∫ ξ in Ioi 0, (f uR - s * uR) * φ.dx t (ξ + s * t)
            = (f uR - s * uR) * ∫ ξ in Ioi 0, φ.dx t (ξ + s * t) := by
              rw [integral_const_mul]
        _ = (f uR - s * uR) * (-φ t (s * t)) := by
              rw [integral_Ioi_shift_dx φ s t]
        _ = -((f uR - s * uR) * φ t (s * t)) := by
              ring

/-! ### Phase 3: assembly -/

/-- **Fundamental theorem.**  For any flux, the residual of the travelling step
collapses to the Rankine–Hugoniot jump along the moving interface. -/
theorem hasShockIntegralReduction (f : ℝ → ℝ) (T uL uR s : ℝ) :
    HasShockIntegralReduction f T uL uR s := by
  intro φ
  dsimp only [HasShockIntegralReduction, weakResidual]
  calc
    (∫ t in Ioo 0 T, ∫ x, weakIntegrand f (shockProfile uL uR s) φ t x)
        = ∫ t in Ioo 0 T, ((∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) +
            (∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x)) := by
      congr 1
      funext t
      exact integral_spatial_split φ uL uR s t
    _ = (∫ t in Ioo 0 T, ∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) +
        (∫ t in Ioo 0 T, ∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) := by
      exact integral_add (integrableOn_time_weakIntegrand_Iic φ uL s)
        (integrableOn_time_weakIntegrand_Ioi φ uR s)
    _ = (∫ t in Ioo 0 T, (f uL - s * uL) * φ t (s * t)) -
        (∫ t in Ioo 0 T, (f uR - s * uR) * φ t (s * t)) := by
      rw [shock_integral_left, shock_integral_right]
      simp [sub_eq_add_neg]
    _ = ∫ t in Ioo 0 T, ((f uL - f uR) - s * (uL - uR)) * φ t (s * t) := by
      rw [← integral_sub
        (integrableOn_shock_boundary φ (f uL - s * uL) s)
        (integrableOn_shock_boundary φ (f uR - s * uR) s)]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      ring

/-- **Unconditional packaging.**  A travelling step whose speed satisfies the
Rankine–Hugoniot condition is a weak solution of the conservation law, for any
flux. -/
theorem isWeakSolution_shockProfile_of_rankineHugoniot {f : ℝ → ℝ}
    (T uL uR s : ℝ) (hRH : RankineHugoniot f uL uR s) :
    IsWeakSolution f T (shockProfile uL uR s) :=
  isWeakSolution_shockProfile T uL uR s
    (hasShockIntegralReduction f T uL uR s) hRH

end ConservationLaw

end
