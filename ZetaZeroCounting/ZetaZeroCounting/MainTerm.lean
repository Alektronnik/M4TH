/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import ZetaZeroCounting.SafeHeights

/-!
# The von Mangoldt main term and its asymptotic theory

The main term of the Riemann–von Mangoldt counting formula,

  `vonMangoldtMainTerm T = (T / 2π) (log (T / 2π) - 1)`,

together with its simplified form `(T / 2π) log T`, and the complete
unconditional asymptotic theory: the two forms are asymptotically equivalent,
the main term tends to infinity, is eventually nonzero, and dominates both
`T` and `log T` (`T_isLittleO_vonMangoldtMainTerm`,
`log_isLittleO_vonMangoldtMainTerm`).

The Riemann–von Mangoldt counting theorem itself,

  `distinctZeroCount ~ vonMangoldtMainTerm`  (at `atTop`),

is stated here as the typed `Prop` `RiemannVonMangoldtCounting`.  It is **not**
an axiom of this package: its proof belongs to the argument-principle series
(the contour packages), and every consequence in this file takes it as an
explicit hypothesis (`riemannVonMangoldtCounting_simplified`).

## Main definitions

- `Riemann.vonMangoldtMainTerm`, `Riemann.vonMangoldtMainTermSimplified`.
- `Riemann.RiemannVonMangoldtCounting` (the typed counting statement).

## Main results

- `Riemann.vonMangoldt_mainTerm_simplified_equiv_classical`.
- `Riemann.vonMangoldtMainTerm_tendsto_atTop`.
- `Riemann.T_isLittleO_vonMangoldtMainTerm`,
  `Riemann.log_isLittleO_vonMangoldtMainTerm`.
- `Riemann.riemannVonMangoldtCounting_simplified` (conditional transfer).

## Implementation notes

The name `vonMangoldtMainTerm` lives inside the `Riemann` namespace and does
not collide with `ArithmeticFunction.vonMangoldt`; the final global name is a
review decision.  All lemmas in this file are unconditional; the only
statement about the actual zero count is the `Prop` definition and its
hypothesis-guarded corollary.

## Tags

Riemann-von Mangoldt, zero counting, main term, asymptotics
-/

@[expose] public section

open Complex Set Filter Topology Asymptotics

namespace Riemann

/-- Classical main term: `(T / 2π) (log (T / 2π) - 1)`. -/
noncomputable def vonMangoldtMainTerm (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1)

/-- Simplified form used in asymptotic equivalences: `(T / 2π) log T`. -/
noncomputable def vonMangoldtMainTermSimplified (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * Real.log T

lemma vonMangoldtMainTerm_sub_simplified {T : ℝ} (hT : 0 < T) :
    vonMangoldtMainTermSimplified T - vonMangoldtMainTerm T =
      (T / (2 * Real.pi)) * (Real.log (2 * Real.pi) + 1) := by
  dsimp [vonMangoldtMainTermSimplified, vonMangoldtMainTerm]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [Real.log_div hT.ne' hpi.ne']
  field_simp
  ring_nf

/-- The two forms of the main term are asymptotically equivalent. -/
theorem vonMangoldt_mainTerm_simplified_equiv_classical :
    IsEquivalent atTop vonMangoldtMainTermSimplified vonMangoldtMainTerm := by
  rw [isEquivalent_iff_tendsto_one]
  · have hpi : 0 < 2 * Real.pi := by positivity
    have h_ratio : (fun T => vonMangoldtMainTermSimplified T / vonMangoldtMainTerm T) =ᶠ[atTop]
        fun T => 1 + (Real.log (2 * Real.pi) + 1) / (Real.log (T / (2 * Real.pi)) - 1) := by
      filter_upwards [eventually_gt_atTop (2 * Real.pi * Real.exp 1)] with T hT
      have hTpos : 0 < T := lt_trans (by positivity) hT
      have hsub := vonMangoldtMainTerm_sub_simplified hTpos
      have hsum : vonMangoldtMainTermSimplified T =
          vonMangoldtMainTerm T + (T / (2 * Real.pi)) * (Real.log (2 * Real.pi) + 1) := by
        linarith
      have hden_ne : Real.log (T / (2 * Real.pi)) - 1 ≠ 0 := by
        have hpi' : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
        have hlog : 1 < Real.log (T / (2 * Real.pi)) := by
          have hgt : Real.exp 1 < T / (2 * Real.pi) := by
            rw [lt_div_iff₀ hpi, mul_comm]
            exact hT
          rw [← Real.log_exp 1]
          exact (Real.log_lt_log_iff (Real.exp_pos 1) hpi').2 hgt
        linarith
      have hmain_ne : vonMangoldtMainTerm T ≠ 0 := by
        dsimp [vonMangoldtMainTerm]
        exact mul_ne_zero (div_ne_zero hTpos.ne' hpi.ne') hden_ne
      calc
        vonMangoldtMainTermSimplified T / vonMangoldtMainTerm T
            = (vonMangoldtMainTerm T + (T / (2 * Real.pi)) * (Real.log (2 * Real.pi) + 1)) /
                vonMangoldtMainTerm T := by rw [hsum]
        _ = 1 + ((T / (2 * Real.pi)) * (Real.log (2 * Real.pi) + 1)) / vonMangoldtMainTerm T := by
          rw [add_div, div_self hmain_ne]
        _ = 1 + (Real.log (2 * Real.pi) + 1) / (Real.log (T / (2 * Real.pi)) - 1) := by
          dsimp [vonMangoldtMainTerm]
          field_simp [hmain_ne, hTpos.ne', hpi.ne', Real.log_div hTpos.ne' hpi.ne', hden_ne]
    have hden_top : Tendsto (fun T => Real.log (T / (2 * Real.pi)) - 1) atTop atTop := by
      have hlog : Tendsto (fun T => Real.log (T / (2 * Real.pi))) atTop atTop := by
        have hdiv : Tendsto (fun T => T / (2 * Real.pi)) atTop atTop := by
          rw [tendsto_atTop_atTop]
          intro b
          use max (b * (2 * Real.pi)) 0
          intro T hT
          have hT' : b * (2 * Real.pi) ≤ T := le_trans (le_max_left _ _) hT
          calc b = (b * (2 * Real.pi)) / (2 * Real.pi) := by field_simp
            _ ≤ T / (2 * Real.pi) := div_le_div_of_nonneg_right hT' (by positivity)
        exact Real.tendsto_log_atTop.comp hdiv
      rw [tendsto_atTop_atTop]
      intro b
      rcases (tendsto_atTop_atTop.mp hlog) (b + 1) with ⟨a, ha⟩
      use a
      intro T hT
      linarith [ha T hT]
    have h_err :
        Tendsto
          (fun T => (Real.log (2 * Real.pi) + 1) /
            (Real.log (T / (2 * Real.pi)) - 1))
          atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden_top
    refine Tendsto.congr' h_ratio.symm ?_
    simpa [add_zero] using Filter.Tendsto.const_add 1 h_err
  · filter_upwards [eventually_gt_atTop (2 * Real.pi * Real.exp 1)] with T hT
    dsimp [vonMangoldtMainTerm]
    have hTpos : 0 < T := lt_trans (by positivity) hT
    have hpi : 0 < 2 * Real.pi := by positivity
    refine mul_ne_zero (div_ne_zero hTpos.ne' hpi.ne') ?_
    have hlog : 1 < Real.log (T / (2 * Real.pi)) := by
      have hpi' : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
      have hgt : Real.exp 1 < T / (2 * Real.pi) := by
        rw [lt_div_iff₀ hpi]
        linarith
      rw [← Real.log_exp 1]
      exact (Real.log_lt_log_iff (Real.exp_pos 1) hpi').2 hgt
    linarith

/-! ### Unconditional asymptotics of the main term -/

lemma vonMangoldtMainTerm_eventually_ne_zero :
    ∀ᶠ T in atTop, vonMangoldtMainTerm T ≠ 0 := by
  filter_upwards [eventually_gt_atTop (Real.exp 1 * (2 * Real.pi))] with T hT
  dsimp [vonMangoldtMainTerm]
  have hTpos : 0 < T := lt_trans (by positivity) hT
  have hpi : 0 < 2 * Real.pi := by positivity
  refine mul_ne_zero (div_ne_zero hTpos.ne' hpi.ne') ?_
  have hlog : 1 < Real.log (T / (2 * Real.pi)) := by
    have hpi' : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
    have hgt : Real.exp 1 < T / (2 * Real.pi) := by
      rw [lt_div_iff₀ hpi]
      linarith
    rw [← Real.log_exp 1]
    exact (Real.log_lt_log_iff (Real.exp_pos 1) hpi').2 hgt
  linarith

lemma vonMangoldtMainTerm_log_den_tendsto_atTop :
    Tendsto (fun T => Real.log (T / (2 * Real.pi)) - 1) atTop atTop := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hdiv : Tendsto (fun T => T / (2 * Real.pi)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    use max (b * (2 * Real.pi)) 0
    intro T hT
    have hT' : b * (2 * Real.pi) ≤ T := le_trans (le_max_left _ _) hT
    calc b = (b * (2 * Real.pi)) / (2 * Real.pi) := by field_simp
      _ ≤ T / (2 * Real.pi) := div_le_div_of_nonneg_right hT' (by positivity)
  have hlog : Tendsto (fun T => Real.log (T / (2 * Real.pi))) atTop atTop :=
    Real.tendsto_log_atTop.comp hdiv
  rw [tendsto_atTop_atTop]
  intro b
  rcases (tendsto_atTop_atTop.mp hlog) (b + 1) with ⟨a, ha⟩
  use a
  intro T hT
  linarith [ha T hT]

/-- Numeric bound: `π > 3` gives `2π ≥ 1`. -/
lemma one_le_two_mul_pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]

/-- Numeric bound for the von Mangoldt threshold: `e > 2` and `π > 3`. -/
lemma one_le_exp_one_mul_two_pi : (1 : ℝ) ≤ Real.exp 1 * (2 * Real.pi) := by
  nlinarith [Real.pi_gt_three, Real.exp_one_gt_two]

lemma vonMangoldtMainTerm_tendsto_atTop : Tendsto vonMangoldtMainTerm atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  rcases (tendsto_atTop_atTop.mp vonMangoldtMainTerm_log_den_tendsto_atTop) (b + 1) with
    ⟨a, ha_den⟩
  use max (Real.exp 1 * (2 * Real.pi) * max a 0) (Real.exp 1 * (2 * Real.pi))
  intro T hT
  have hT_ge_exp : Real.exp 1 * (2 * Real.pi) ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T :=
    lt_of_lt_of_le (by positivity : 0 < Real.exp 1 * (2 * Real.pi)) hT_ge_exp
  have hT' : a ≤ T := by
    rcases lt_or_ge 0 a with ha_pos | ha_nonpos
    · have hmax : max a 0 = a := max_eq_left ha_pos.le
      have hscale : a ≤ Real.exp 1 * (2 * Real.pi) * a := by
        exact le_mul_of_one_le_left (le_of_lt ha_pos) one_le_exp_one_mul_two_pi
      have hmid : Real.exp 1 * (2 * Real.pi) * a ≤
          max (Real.exp 1 * (2 * Real.pi) * max a 0) (Real.exp 1 * (2 * Real.pi)) := by
        rw [hmax]
        exact le_max_left _ _
      exact le_trans hscale (le_trans hmid hT)
    · have hmax : max a 0 = 0 := max_eq_right ha_nonpos
      have hstep : max a 0 ≤
          max (Real.exp 1 * (2 * Real.pi) * max a 0) (Real.exp 1 * (2 * Real.pi)) := by
        rw [hmax]
        simp only [mul_zero]
        exact le_max_left (0 : ℝ) (Real.exp 1 * (2 * Real.pi))
      exact le_trans (le_max_left a 0) (le_trans hstep hT)
  have hlog : Real.log (T / (2 * Real.pi)) - 1 ≥ b + 1 := by
    simpa using ha_den T hT'
  have hpi : 0 < 2 * Real.pi := by positivity
  dsimp [vonMangoldtMainTerm]
  have hpos : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
  have hlog_nonneg : 0 ≤ Real.log (T / (2 * Real.pi)) - 1 := by
    have hle : Real.exp 1 ≤ T / (2 * Real.pi) := by rwa [le_div_iff₀ (by positivity)]
    have hlog_ge_one : 1 ≤ Real.log (T / (2 * Real.pi)) := (Real.le_log_iff_exp_le hpos).mpr hle
    linarith
  have hcoef : 1 ≤ T / (2 * Real.pi) := by
    have h2pi_le : (2 : ℝ) * Real.pi ≤ T := by
      have hle : (2 : ℝ) * Real.pi ≤ Real.exp 1 * (2 * Real.pi) := by
        nlinarith [Real.pi_pos, Real.add_one_le_exp 1]
      exact le_trans hle hT_ge_exp
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      (by simpa [one_mul] using h2pi_le)
  calc
    b ≤ b + 1 := by linarith
    _ ≤ Real.log (T / (2 * Real.pi)) - 1 := by linarith [hlog]
    _ ≤ (T / (2 * Real.pi)) *
        (Real.log (T / (2 * Real.pi)) - 1) := by
      nlinarith [hlog_nonneg, hcoef]

lemma vonMangoldtMainTerm_log_den_ne_zero {T : ℝ} (hmain : vonMangoldtMainTerm T ≠ 0) :
    Real.log (T / (2 * Real.pi)) - 1 ≠ 0 := by
  intro h
  have hz : vonMangoldtMainTerm T = 0 := by
    show (T / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1) = 0
    rw [h, mul_zero]
  exact hmain hz

/-- The identity `T` is negligible against the main term. -/
lemma T_isLittleO_vonMangoldtMainTerm :
    (fun T : ℝ => T) =o[atTop] vonMangoldtMainTerm := by
  have hgf : ∀ᶠ T in atTop, vonMangoldtMainTerm T = 0 → T = 0 :=
    vonMangoldtMainTerm_eventually_ne_zero.mono fun T hT h0 => absurd h0 hT
  refine (isLittleO_iff_tendsto' hgf).2 ?_
  have h_main_div_T : Tendsto (fun T => vonMangoldtMainTerm T / T) atTop atTop := by
    have h_eq : (fun T => vonMangoldtMainTerm T / T) =ᶠ[atTop]
        fun T => (1 / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1) := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      dsimp [vonMangoldtMainTerm]
      field_simp [hT.ne']
    have hscaled :
        Tendsto
          (fun T => (1 / (2 * Real.pi)) *
            (Real.log (T / (2 * Real.pi)) - 1))
          atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) vonMangoldtMainTerm_log_den_tendsto_atTop
    exact Tendsto.congr' h_eq.symm hscaled
  have h_congr : (fun T => T / vonMangoldtMainTerm T) =ᶠ[atTop]
      fun T => (vonMangoldtMainTerm T / T)⁻¹ := by
    filter_upwards [vonMangoldtMainTerm_eventually_ne_zero] with T hT
    field_simp [hT]
  exact Tendsto.congr' h_congr.symm (tendsto_inv_atTop_zero.comp h_main_div_T)

/-- `log` is negligible against the main term. -/
lemma log_isLittleO_vonMangoldtMainTerm :
    (fun T : ℝ => Real.log T) =o[atTop] vonMangoldtMainTerm := by
  have hgf : ∀ᶠ T in atTop, vonMangoldtMainTerm T = 0 → Real.log T = 0 :=
    vonMangoldtMainTerm_eventually_ne_zero.mono fun T hT h0 => absurd h0 hT
  refine (isLittleO_iff_tendsto' hgf).2 ?_
  have h_eq : (fun T => Real.log T / vonMangoldtMainTerm T) =ᶠ[atTop]
      fun T => (2 * Real.pi / T) * (Real.log T / (Real.log (T / (2 * Real.pi)) - 1)) := by
    filter_upwards [eventually_gt_atTop 1, vonMangoldtMainTerm_eventually_ne_zero] with T hT hmain
    have hTpos : 0 < T := lt_trans zero_lt_one hT
    have hpi : 0 < 2 * Real.pi := by positivity
    have hden_ne := vonMangoldtMainTerm_log_den_ne_zero hmain
    have hlogpos : 0 < Real.log T := Real.log_pos hT
    dsimp [vonMangoldtMainTerm]
    field_simp [hTpos.ne', hpi.ne', hden_ne, hlogpos.ne']
  have h_inv_T : Tendsto (fun T => (2 * Real.pi) / T) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (2 * Real.pi)
  have h_ratio :
      Tendsto (fun T => Real.log T / (Real.log (T / (2 * Real.pi)) - 1))
        atTop (𝓝 1) := by
    have h_factor : (fun T => Real.log T / (Real.log (T / (2 * Real.pi)) - 1)) =ᶠ[atTop]
        fun T => 1 + (Real.log (2 * Real.pi) + 1) / (Real.log (T / (2 * Real.pi)) - 1) := by
      filter_upwards [eventually_gt_atTop (2 * Real.pi * Real.exp 1)] with T hT
      have hTpos : 0 < T := lt_trans (by positivity) hT
      have hpi : 0 < 2 * Real.pi := by positivity
      have hsum : Real.log T = Real.log (T / (2 * Real.pi)) + Real.log (2 * Real.pi) := by
        have hpi' : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
        calc
          Real.log T = Real.log ((T / (2 * Real.pi)) * (2 * Real.pi)) := by
            congr 1; field_simp [hTpos.ne', hpi.ne']
          _ = Real.log (T / (2 * Real.pi)) + Real.log (2 * Real.pi) :=
              Real.log_mul hpi'.ne' hpi.ne'
      have hden_ne : Real.log (T / (2 * Real.pi)) - 1 ≠ 0 := by
        have hpi' : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
        have hlog : 1 < Real.log (T / (2 * Real.pi)) := by
          have hgt : Real.exp 1 < T / (2 * Real.pi) := by
            rw [lt_div_iff₀ hpi]
            linarith
          rw [← Real.log_exp 1]
          exact (Real.log_lt_log_iff (Real.exp_pos 1) hpi').2 hgt
        linarith
      rw [hsum]
      field_simp [hden_ne]
      ring
    have h_err :
        Tendsto
          (fun T => (Real.log (2 * Real.pi) + 1) /
            (Real.log (T / (2 * Real.pi)) - 1))
          atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop vonMangoldtMainTerm_log_den_tendsto_atTop
    have h_add := Filter.Tendsto.const_add 1 h_err
    simpa [add_zero] using Tendsto.congr' h_factor.symm h_add
  simpa using Tendsto.congr' h_eq.symm (h_inv_T.mul h_ratio)

/-! ### The typed counting statement -/

/-- **The Riemann–von Mangoldt counting theorem, as a typed statement.**
Its proof belongs to the argument-principle series over the critical box; no
result in this package assumes it except as an explicit hypothesis. -/
def RiemannVonMangoldtCounting : Prop :=
  IsEquivalent atTop distinctZeroCount vonMangoldtMainTerm

/-- Conditional transfer: the counting statement in classical form yields the
simplified form `(T / 2π) log T`. -/
theorem riemannVonMangoldtCounting_simplified (h : RiemannVonMangoldtCounting) :
    IsEquivalent atTop distinctZeroCount vonMangoldtMainTermSimplified :=
  h.trans vonMangoldt_mainTerm_simplified_equiv_classical.symm

/-! ### Certificates

Concrete instances checked by the kernel.  After `lake build`, running

  `#print axioms Riemann.zerosUpToIm_finite`
  `#print axioms Riemann.T_isLittleO_vonMangoldtMainTerm`

must report only the foundational axioms `propext`, `Classical.choice`,
`Quot.sound`. -/

section Certificates

/-- Monotonicity instance of the counting function. -/
example : zeroCountingFun 1 ≤ zeroCountingFun 2 :=
  zeroCountingFun_mono (by norm_num : (1 : ℝ) ≤ 2)

/-- Nonnegativity instance. -/
example : 0 ≤ zeroCountingFun 100 :=
  zeroCountingFun_nonneg 100

/-- A safe height exists above `100`. -/
example : ∃ T', 100 ≤ T' ∧ IsSafeHeight T' :=
  exists_safe_height_above 100 (by norm_num)

end Certificates

end Riemann

end
