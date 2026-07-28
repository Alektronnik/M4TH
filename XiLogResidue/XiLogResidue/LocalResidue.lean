/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import XiLogResidue.Basic

/-!
# Local logarithmic residue of `entireXi`

This file proves that the local logarithmic residue of the entire Xi variant at
each zero is its analytic multiplicity.
-/

@[expose] public section

open Complex Topology Filter Asymptotics

namespace RiemannLogResidue

/-- At a simple zero, the logarithmic residue tends to `1`. -/
theorem entireXi_logDeriv_residue_simple_zero {s : ℂ} (hs : entireXi s = 0)
    (hs' : deriv entireXi s ≠ 0) :
    Tendsto (fun w => (w - s) * entireXiLogDeriv w) (𝓝[≠] s) (𝓝 1) :=
  AnalyticAt.tendsto_mul_logDeriv_simple_zero (analyticAt_entireXi s) hs hs'

/-- If `f - c/(z-p)` is bounded on the punctured neighborhood, then
`(z-p) f z` tends to `c`. -/
private lemma tendsto_mul_sub_principal_isBigO_one
    {f : ℂ → ℂ} {p c : ℂ}
    (h : (f - fun z : ℂ => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 c) := by
  have hp_tendsto :
      Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) := by
    simpa [sub_self] using
      (continuousWithinAt_id (s := ({p}ᶜ : Set ℂ)) (x := p)).tendsto.sub
        (tendsto_const_nhds : Tendsto (fun _ => p) (𝓝[≠] p) (𝓝 p))
  have hp_small :
      (fun z : ℂ => z - p) =o[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (isLittleO_one_iff ℂ).2 hp_tendsto
  have hrem_tendsto :
      Tendsto
        (fun z : ℂ => (z - p) * ((f - fun w : ℂ => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 0) := by
    simpa using hp_small.mul_isBigO h
  have hprincipal :
      (fun z : ℂ => (z - p) * (c / (z - p))) =ᶠ[𝓝[≠] p] fun _ : ℂ => c := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    field_simp [sub_ne_zero.mpr hz]
  have hprincipal_tendsto :
      Tendsto (fun z : ℂ => (z - p) * (c / (z - p))) (𝓝[≠] p) (𝓝 c) :=
    tendsto_const_nhds.congr' hprincipal.symm
  have hsum_tendsto :
      Tendsto
        (fun z : ℂ =>
          (z - p) * (c / (z - p))
            + (z - p) * ((f - fun w : ℂ => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 (c + 0)) :=
    hprincipal_tendsto.add hrem_tendsto
  have hsum :
      (fun z : ℂ => (z - p) * f z) =ᶠ[𝓝[≠] p]
        fun z : ℂ =>
          (z - p) * (c / (z - p))
            + (z - p) * ((f - fun w : ℂ => c / (w - p)) z) := by
    filter_upwards with z
    simp only [Pi.sub_apply]
    ring
  simpa using hsum_tendsto.congr' hsum.symm

/-- Local decomposition:
`logDeriv f = n/(z-p) + bounded`, where `n` is the analytic order. -/
private lemma logDeriv_sub_principal_isBigO_one_of_analyticOrderNatAt
    {f : ℂ → ℂ} {p : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f p) (htop : analyticOrderAt f p ≠ ⊤)
    (hn : analyticOrderNatAt f p = n) :
    (logDeriv f - fun s : ℂ => (n : ℂ) / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg, hg0, hf_eq⟩ := (hf.analyticOrderAt_ne_top).mp htop
  set F : ℂ → ℂ := fun s => (s - p) ^ n * g s
  have hf_eq_ne : f =ᶠ[𝓝[≠] p] F := by
    refine (hf_eq.filter_mono nhdsWithin_le_nhds).congr ?_
    filter_upwards with z
    simp [F, hn, smul_eq_mul]
  have hderiv_ne : deriv f =ᶠ[𝓝[≠] p] deriv F := hf_eq_ne.nhdsNE_deriv
  have hg_nonzero_ne : ∀ᶠ s in 𝓝[≠] p, g s ≠ 0 := by
    exact (hg.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg0
      |>.filter_mono nhdsWithin_le_nhds
  have hg_analytic_ne : ∀ᶠ s in 𝓝[≠] p, AnalyticAt ℂ g s := by
    exact hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hlog_eq :
      (logDeriv f - fun s : ℂ => (n : ℂ) / (s - p)) =ᶠ[𝓝[≠] p] logDeriv g := by
    filter_upwards [hf_eq_ne, hderiv_ne, self_mem_nhdsWithin, hg_nonzero_ne, hg_analytic_ne]
      with s hfs hderiv hs_ne hgs_ne hgs_analytic
    have hpow_ne : (s - p) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hs_ne)
    have hdiff_pow : DifferentiableAt ℂ (fun z : ℂ => (z - p) ^ n) s :=
      DifferentiableAt.pow (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - p) s) n
    have hlogF :
        logDeriv F s =
          logDeriv (fun z : ℂ => (z - p) ^ n) s + logDeriv g s := by
      exact logDeriv_mul (f := fun z : ℂ => (z - p) ^ n) (g := g) s
        hpow_ne hgs_ne hdiff_pow hgs_analytic.differentiableAt
    have hlogpow : logDeriv (fun z : ℂ => (z - p) ^ n) s = (n : ℂ) / (s - p) := by
      rw [logDeriv_fun_pow (f := fun z : ℂ => z - p) (x := s) (by fun_prop) n]
      simp [logDeriv_apply, div_eq_mul_inv]
    simp only [Pi.sub_apply]
    calc
      logDeriv f s - (n : ℂ) / (s - p)
          = logDeriv F s - (n : ℂ) / (s - p) := by
            simp [logDeriv_apply, hfs, hderiv]
      _ = logDeriv g s := by
            rw [hlogF, hlogpow]
            ring
  have hderiv_bounded : deriv g =O[𝓝 p] (1 : ℂ → ℂ) :=
    hg.deriv.continuousAt.norm.isBoundedUnder_le.isBigO_one ℂ
  have hinv_bounded : g⁻¹ =O[𝓝 p] (1 : ℂ → ℂ) :=
    (hg.continuousAt.inv₀ hg0).norm.isBoundedUnder_le.isBigO_one ℂ
  have hlog_bounded : logDeriv g =O[𝓝 p] (1 : ℂ → ℂ) := by
    have hmul_bounded :
        (deriv g * g⁻¹) =O[𝓝 p] ((1 : ℂ → ℂ) * (1 : ℂ → ℂ)) :=
      Asymptotics.IsBigO.mul hderiv_bounded hinv_bounded
    have hmul_bounded' :
        (fun x => deriv g x * (g x)⁻¹) =O[𝓝 p] (1 : ℂ → ℂ) := by
      refine hmul_bounded.congr ?_ ?_
      · intro x
        rfl
      · intro x
        simp
    change (fun x => deriv g x / g x) =O[𝓝 p] (1 : ℂ → ℂ)
    simpa only [div_eq_mul_inv] using hmul_bounded'
  exact hlog_eq.trans_isBigO (hlog_bounded.mono nhdsWithin_le_nhds)

/-- Local logarithmic residue equals the analytic multiplicity at each zero of `entireXi`. -/
theorem entireXi_logDeriv_residue_eq_multiplicity {s : ℂ} (hs : entireXi s = 0) :
    Tendsto (fun w => (w - s) * entireXiLogDeriv w) (𝓝[≠] s)
      (𝓝 (entireXiZeroMultiplicity s : ℂ)) := by
  dsimp only [entireXiLogDeriv, entireXiZeroMultiplicity]
  have hf := analyticAt_entireXi s
  have htop := entireXi_analyticOrderAt_ne_top hs
  set n := analyticOrderNatAt entireXi s
  refine tendsto_mul_sub_principal_isBigO_one ?_
  exact logDeriv_sub_principal_isBigO_one_of_analyticOrderNatAt hf htop rfl

/-- Package statement: local logarithmic residue equals analytic multiplicity. -/
def EntireXiLogResidueEqualsMultiplicity : Prop :=
  ∀ {s : ℂ}, entireXi s = 0 →
    Tendsto (fun w => (w - s) * entireXiLogDeriv w) (𝓝[≠] s)
      (𝓝 (entireXiZeroMultiplicity s : ℂ))

theorem entireXi_logResidue_equals_multiplicity :
    EntireXiLogResidueEqualsMultiplicity :=
  fun hs => entireXi_logDeriv_residue_eq_multiplicity hs

end RiemannLogResidue
