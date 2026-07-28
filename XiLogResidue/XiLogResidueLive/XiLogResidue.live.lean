/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Tactic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.DiscreteSubset

/-!
# XiLogResidue.live

Single-file live version of the `XiLogResidue` package.

This file is intentionally independent of local package imports.  It fuses the
public source modules in dependency order for web inspection and study.
-/

@[expose] public section

/-!
## Source file: `XiLogResidue/Basic.lean`
-/

/-!
# Basic infrastructure for `XiLogResidue`

This file defines the entire Xi variant, its logarithmic derivative, the
critical box, the finite set of nontrivial zeros up to height `T`, and the
analytic multiplicity used in the residue-divisor dictionary.
-/

open Complex Topology Filter Set

namespace RiemannLogResidue

/-- Nontrivial zeros of the Riemann zeta function in the open critical strip. -/
def nontrivialZeros : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}

lemma nontrivialZeros_subset_riemannZetaZeros :
    nontrivialZeros ⊆ riemannZetaZeros := by
  intro s hs
  exact hs.1

/-- Nontrivial zeros with positive imaginary part bounded by `T`. -/
def zerosUpToIm (T : ℝ) : Set ℂ :=
  {s : ℂ | s ∈ nontrivialZeros ∧ 0 < s.im ∧ s.im ≤ T}

lemma zerosUpToIm_subset_nontrivial (T : ℝ) :
    zerosUpToIm T ⊆ nontrivialZeros := by
  intro s hs
  exact hs.1

/-- The closed critical box `0 ≤ Re(s) ≤ 1`, `0 ≤ Im(s) ≤ T`. -/
def criticalBox (T : ℝ) : Set ℂ :=
  {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}

/-- The top edge of the critical box. -/
def criticalBoxTopEdge (T : ℝ) : Set ℂ :=
  {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im = T}

/-- The bottom edge of the critical box. -/
def criticalBoxBottomEdge : Set ℂ :=
  {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im = 0}

/-- The left edge of the critical box. -/
def criticalBoxLeftEdge (T : ℝ) : Set ℂ :=
  {s : ℂ | s.re = 0 ∧ 0 ≤ s.im ∧ s.im ≤ T}

/-- The right edge of the critical box. -/
def criticalBoxRightEdge (T : ℝ) : Set ℂ :=
  {s : ℂ | s.re = 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}

/-- Boundary of the critical box. -/
def criticalBoxBoundary (T : ℝ) : Set ℂ :=
  criticalBoxTopEdge T ∪ criticalBoxBottomEdge ∪ criticalBoxLeftEdge T ∪ criticalBoxRightEdge T

lemma mem_criticalBoxBoundary_iff {T : ℝ} {s : ℂ} :
    s ∈ criticalBoxBoundary T ↔
      s ∈ criticalBoxTopEdge T ∨ s ∈ criticalBoxBottomEdge ∨
        s ∈ criticalBoxLeftEdge T ∨ s ∈ criticalBoxRightEdge T := by
  simp [criticalBoxBoundary, or_assoc]

/-- Interior of the critical box. -/
def criticalBoxInterior (T : ℝ) : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im < T}

lemma criticalBoxInterior_subset_criticalBox {T : ℝ} :
    criticalBoxInterior T ⊆ criticalBox T := by
  intro s hs
  exact ⟨le_of_lt hs.1, le_of_lt hs.2.1, le_of_lt hs.2.2.1, le_of_lt hs.2.2.2⟩

/-- Safe heights avoid zeros on the top edge. -/
def IsSafeHeight (T : ℝ) : Prop :=
  ∀ s ∈ criticalBoxTopEdge T, ¬ s ∈ nontrivialZeros

lemma zerosUpToIm_subset_criticalBoxInterior {T : ℝ} (hSafe : IsSafeHeight T) :
    zerosUpToIm T ⊆ criticalBoxInterior T := by
  intro s hs
  have hz := hs.1
  have himlt : s.im < T := by
    have hle := hs.2.2
    by_contra hnot
    push Not at hnot
    have him : s.im = T := le_antisymm hle hnot
    have htop : s ∈ criticalBoxTopEdge T := by
      exact ⟨le_of_lt hz.2.1, le_of_lt hz.2.2, him⟩
    exact hSafe s htop hz
  exact ⟨hz.2.1, hz.2.2, hs.2.1, himlt⟩

/-- The critical box is the image of a compact real rectangle. -/
lemma isCompact_criticalBox (T : ℝ) : IsCompact (criticalBox T) := by
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * I
  have h_cont : Continuous f :=
    (continuous_ofReal.comp continuous_fst).add
      ((continuous_ofReal.comp continuous_snd).mul continuous_const)
  have h_comp : IsCompact (Set.Icc (0 : ℝ) (1 : ℝ) ×ˢ Set.Icc (0 : ℝ) T) :=
    isCompact_Icc.prod isCompact_Icc
  have h_eq : f '' (Set.Icc (0 : ℝ) (1 : ℝ) ×ˢ Set.Icc (0 : ℝ) T) = criticalBox T := by
    ext s
    simp only [criticalBox, Set.mem_image, Set.mem_prod, Set.mem_Icc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨x, y⟩, ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩, rfl⟩
      simp only [f, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_zero,
        add_zero, mul_zero, add_im, mul_one, mul_im, zero_add]
      exact ⟨hx0, hx1, hy0, hy1⟩
    · intro hs
      refine ⟨(s.re, s.im), ⟨⟨hs.1, hs.2.1⟩, ⟨hs.2.2.1, hs.2.2.2⟩⟩, ?_⟩
      apply Complex.ext <;>
        simp only [f, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_zero,
          add_zero, mul_zero, add_im, mul_one, mul_im, zero_add]
  rw [← h_eq]
  exact IsCompact.image h_comp h_cont

/-- The entire Xi variant used for the residue-divisor dictionary. -/
noncomputable def entireXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

lemma differentiable_entireXi : Differentiable ℂ entireXi := by
  unfold entireXi
  exact ((differentiable_id.mul
    (differentiable_id.sub (differentiable_const (1 : ℂ)))).mul
      differentiable_completedZeta₀).add (differentiable_const (1 : ℂ))

lemma continuous_entireXi : Continuous entireXi :=
  differentiable_entireXi.continuous

lemma entireXi_ne_zero_at_zero : entireXi 0 ≠ 0 := by
  simp [entireXi]

lemma analyticAt_entireXi (s : ℂ) : AnalyticAt ℂ entireXi s :=
  ((analyticOnNhd_univ_iff_differentiable).2 differentiable_entireXi) s (Set.mem_univ s)

/-- Zeros of the entire Xi variant. -/
def entireXiZeros : Set ℂ :=
  {z : ℂ | entireXi z = 0}

lemma mem_entireXiZeros_iff {z : ℂ} : z ∈ entireXiZeros ↔ entireXi z = 0 :=
  Iff.rfl

lemma critical_strip_ne_zero_one (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    s ≠ 0 ∧ s ≠ 1 := by
  constructor
  · intro h
    rw [h] at hs
    norm_num at hs
  · intro h
    rw [h] at hs
    norm_num at hs

lemma xi_polynomial_factor_ne_zero_of_ne_zero_ne_one {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s * (s - 1) ≠ 0 :=
  mul_ne_zero hs0 (sub_ne_zero.mpr hs1)

lemma completedRiemannZeta_zero_iff (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    riemannZeta s = 0 ↔ completedRiemannZeta s = 0 := by
  have hs0 : s ≠ 0 := (critical_strip_ne_zero_one s hs).1
  constructor
  · intro hz
    have hγ : Complex.Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs.1
    rw [riemannZeta_def_of_ne_zero hs0] at hz
    rcases div_eq_zero_iff.mp hz with hc | hgamma
    · exact hc
    · exact (hγ hgamma).elim
  · intro hc
    rw [riemannZeta_def_of_ne_zero hs0]
    simp [hc]

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

lemma nontrivial_zero_implies_entireXi_zero (s : ℂ) (hs : s ∈ nontrivialZeros) :
    entireXi s = 0 := by
  have h_band : 0 < s.re ∧ s.re < 1 := hs.2
  rcases critical_strip_ne_zero_one s h_band with ⟨h_ne_zero, h_ne_one⟩
  have h_zeta_comp : completedRiemannZeta s = 0 :=
    (completedRiemannZeta_zero_iff s h_band).mp hs.1
  have h_mathlib : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
    completedRiemannZeta_eq s
  rw [h_mathlib] at h_zeta_comp
  have h_mul : s * (s - 1) * (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) = 0 := by
    rw [h_zeta_comp, mul_zero]
  have h_div1 : s * (s - 1) / s = s - 1 := by
    calc s * (s - 1) / s
      _ = (s - 1) * s / s := by ring
      _ = s - 1 := mul_div_cancel_right₀ (s - 1) h_ne_zero
  have h_div2 : s * (s - 1) / (1 - s) = -s := by
    have h_ne_one_sub : 1 - s ≠ 0 := sub_ne_zero.mpr h_ne_one.symm
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
    _ = 0 := h_mul

lemma entireXi_zero_implies_nontrivial {s : ℂ} (hzero : entireXi s = 0)
    (hband : 0 < s.re ∧ s.re < 1) : s ∈ nontrivialZeros := by
  rcases critical_strip_ne_zero_one s hband with ⟨hs0, hs1⟩
  have hcomp : completedRiemannZeta s = 0 := by
    have heq := entireXi_eq_polynomial_times_completedZeta_of_ne_zero_ne_one hs0 hs1
    rw [heq] at hzero
    rw [mul_eq_zero] at hzero
    cases hzero with
    | inl h => exact (xi_polynomial_factor_ne_zero_of_ne_zero_ne_one hs0 hs1 h).elim
    | inr h => exact h
  exact ⟨(completedRiemannZeta_zero_iff s hband).mpr hcomp, hband⟩

lemma mem_zerosUpToIm_of_entireXi_zero {T : ℝ} {s : ℂ} (hzero : entireXi s = 0)
    (hband : 0 < s.re ∧ s.re < 1) (him : 0 < s.im) (himle : s.im ≤ T) :
    s ∈ zerosUpToIm T :=
  ⟨entireXi_zero_implies_nontrivial hzero hband, him, himle⟩

lemma isDiscrete_entireXi_zeros : IsDiscrete entireXiZeros := by
  have h_analytic : AnalyticOnNhd ℂ entireXi Set.univ :=
    (analyticOnNhd_univ_iff_differentiable).2 differentiable_entireXi
  have h_codisc : (entireXi ⁻¹' {0})ᶜ ∈ Filter.codiscrete ℂ :=
    h_analytic.preimage_zero_mem_codiscrete (x := 0) entireXi_ne_zero_at_zero
  simpa [entireXiZeros, Set.preimage, Set.mem_setOf_eq] using (mem_codiscrete'.mp h_codisc).2

lemma not_eventuallyConst_entireXi_at_zero {s : ℂ} (hs : entireXi s = 0) :
    ¬ EventuallyConst entireXi (𝓝 s) := by
  intro h
  have htop : analyticOrderAt entireXi s = ⊤ := by
    have htop := (eventuallyConst_iff_analyticOrderAt_sub_eq_top (f := entireXi) (z₀ := s)).mp h
    simpa [hs, sub_zero] using htop
  have hentire : entireXi = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s (hf := analyticAt_entireXi)).mp htop
  exact entireXi_ne_zero_at_zero (congr_fun hentire 0)

lemma entireXi_analyticOrderAt_ne_top {s : ℂ} (hs : entireXi s = 0) :
    analyticOrderAt entireXi s ≠ ⊤ := by
  intro htop
  exact not_eventuallyConst_entireXi_at_zero hs
    ((eventuallyConst_iff_analyticOrderAt_sub_eq_top (f := entireXi) (z₀ := s)).mpr
      (by simpa [hs, sub_zero] using htop))

theorem zeros_discrete_entireXi (T : ℝ) :
    DiscreteTopology (Set.inter (criticalBox T) {s : ℂ | entireXi s = 0}) :=
  (IsDiscrete.mono isDiscrete_entireXi_zeros Set.inter_subset_right).to_subtype

theorem finite_zeros_in_box (T : ℝ) : (zerosUpToIm T).Finite := by
  have h_subset : zerosUpToIm T ⊆ criticalBox T ∩ riemannZetaZeros := by
    intro s hs
    constructor
    · simp only [criticalBox, zerosUpToIm, Set.mem_setOf_eq] at hs ⊢
      have h_band := hs.1.2
      exact ⟨by linarith [h_band.1], by linarith [h_band.2], by linarith [hs.2.1], hs.2.2⟩
    · exact nontrivialZeros_subset_riemannZetaZeros hs.1
  exact (IsCompact.inter_riemannZetaZeros_finite (isCompact_criticalBox T)).subset h_subset

theorem zerosUpToIm_finite (T : ℝ) : (zerosUpToIm T).Finite :=
  finite_zeros_in_box T

/-- Finset of nontrivial zeros with `0 < Im(s) ≤ T`. -/
noncomputable def zerosUpToImFinset (T : ℝ) : Finset ℂ :=
  (zerosUpToIm_finite T).toFinset

/-- Analytic multiplicity of a zero of the entire Xi variant. -/
noncomputable def entireXiZeroMultiplicity (s : ℂ) : ℕ :=
  analyticOrderNatAt entireXi s

/-- Logarithmic derivative of the entire Xi variant. -/
noncomputable def entireXiLogDeriv (s : ℂ) : ℂ :=
  logDeriv entireXi s

/-- The package-local multiplicity-counting function. -/
noncomputable def zeroCountingWithMultiplicity (T : ℝ) : ℝ :=
  Nat.cast ((zerosUpToImFinset T).sum entireXiZeroMultiplicity)

end RiemannLogResidue

/-!
## Source file: `XiLogResidue/LocalResidue.lean`
-/

/-!
# Local logarithmic residue of `entireXi`

This file proves that the local logarithmic residue of the entire Xi variant at
each zero is its analytic multiplicity.
-/

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

/-!
## Source file: `XiLogResidue/Divisor.lean`
-/

/-!
# Divisor dictionary for `entireXi`

This file relates the meromorphic divisor of the entire Xi variant on the
critical box to the analytic multiplicity used by the zero-counting finset.
-/

open Complex Topology Filter Set

namespace RiemannLogResidue

/-- Boundary nonvanishing condition used by the divisor support dictionary. -/
def entireXi_ne_zero_on_box_boundary (T : ℝ) : Prop :=
  ∀ s ∈ criticalBoxBoundary T, entireXi s ≠ 0

lemma entireXi_meromorphicOn_criticalBox (T : ℝ) :
    MeromorphicOn entireXi (criticalBox T) :=
  fun s _ => (analyticAt_entireXi s).meromorphicAt

lemma entireXiLogDeriv_meromorphicOn_criticalBox (T : ℝ) :
    MeromorphicOn entireXiLogDeriv (criticalBox T) := by
  unfold entireXiLogDeriv
  exact (entireXi_meromorphicOn_criticalBox T).logDeriv

/-- The support of the divisor on a compact critical box is finite. -/
lemma divisor_support_criticalBox_finite (T : ℝ) :
    (MeromorphicOn.divisor entireXi (criticalBox T)).support.Finite :=
  (MeromorphicOn.divisor entireXi (criticalBox T)).finiteSupport (isCompact_criticalBox T)

lemma entireXi_meromorphicOrder_ne_top_on_criticalBox (T : ℝ) (p : ℂ)
    (_hp : p ∈ criticalBox T) :
    meromorphicOrderAt entireXi p ≠ ⊤ := by
  rw [(analyticAt_entireXi p).meromorphicOrderAt_eq]
  cases hO : analyticOrderAt entireXi p with
  | top =>
    exfalso
    have hs0 : entireXi p = 0 :=
      congr_fun
        ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero p (hf := analyticAt_entireXi)).mp hO) p
    exact entireXi_analyticOrderAt_ne_top hs0 hO
  | coe n =>
    simp [ENat.map_coe]

lemma mem_divisor_support_entireXi_zero {T : ℝ} {s : ℂ} (hs : s ∈ criticalBox T)
    (hmem : s ∈ (MeromorphicOn.divisor entireXi (criticalBox T)).support) :
    entireXi s = 0 := by
  rw [Function.mem_support, MeromorphicOn.divisor_apply (entireXi_meromorphicOn_criticalBox T) hs]
    at hmem
  have hA := analyticAt_entireXi s
  by_contra hne
  have h0 : analyticOrderAt entireXi s = 0 := (hA.analyticOrderAt_eq_zero).mpr hne
  have hzero : (meromorphicOrderAt entireXi s).untop₀ = 0 := by
    simp [hA.meromorphicOrderAt_eq, h0, ENat.map_zero, WithTop.untop₀_zero]
  exact absurd hzero hmem

/-- The divisor of `entireXi` on the critical box equals analytic multiplicity at a zero. -/
lemma entireXi_divisor_eq_multiplicity {T : ℝ} {s : ℂ} (hs : s ∈ criticalBox T)
    (hzero : entireXi s = 0) :
    (MeromorphicOn.divisor entireXi (criticalBox T) s : ℂ) =
      (entireXiZeroMultiplicity s : ℂ) := by
  rw [MeromorphicOn.divisor_apply (entireXi_meromorphicOn_criticalBox T) hs,
    (analyticAt_entireXi s).meromorphicOrderAt_eq, entireXiZeroMultiplicity]
  have htop := entireXi_analyticOrderAt_ne_top hzero
  rw [← Nat.cast_analyticOrderNatAt htop, ENat.map_coe, WithTop.untop₀_coe, Int.cast_natCast]

lemma mem_divisor_finset_zerosUpToIm {T : ℝ} (_hSafe : IsSafeHeight T)
    (hne : entireXi_ne_zero_on_box_boundary T) {p : ℂ}
    (hp : p ∈ (divisor_support_criticalBox_finite T).toFinset) :
    p ∈ zerosUpToImFinset T := by
  have hp_support : p ∈ (MeromorphicOn.divisor entireXi (criticalBox T)).support := by
    simpa [divisor_support_criticalBox_finite, Function.mem_support, MeromorphicOn.divisor] using hp
  have hpR : p ∈ criticalBox T :=
    (MeromorphicOn.divisor entireXi (criticalBox T)).supportWithinDomain hp_support
  have hzero := mem_divisor_support_entireXi_zero hpR hp_support
  rcases hpR with ⟨hre0, hre1, him0, himle⟩
  have hband : 0 < p.re ∧ p.re < 1 := by
    constructor
    · by_contra h
      push Not at h
      have hre_eq : p.re = 0 := le_antisymm h hre0
      have hleft : p ∈ criticalBoxLeftEdge T := by
        simp [criticalBoxLeftEdge, hre_eq, him0, himle]
      exact hne p (mem_criticalBoxBoundary_iff.mpr (Or.inr (Or.inr (Or.inl hleft)))) hzero
    · by_contra h
      push Not at h
      have hre_eq : p.re = 1 := le_antisymm hre1 h
      have hright : p ∈ criticalBoxRightEdge T := by
        simp [criticalBoxRightEdge, hre_eq, him0, himle]
      exact hne p (mem_criticalBoxBoundary_iff.mpr (Or.inr (Or.inr (Or.inr hright)))) hzero
  have himpos : 0 < p.im := by
    by_contra h
    push Not at h
    have him_eq : p.im = 0 := le_antisymm h him0
    have hbot : p ∈ criticalBoxBottomEdge := by
      simp [criticalBoxBottomEdge, him_eq, hre0, hre1]
    exact hne p (mem_criticalBoxBoundary_iff.mpr (Or.inr (Or.inl hbot))) hzero
  simpa [zerosUpToImFinset, zerosUpToIm, nontrivialZeros, Set.mem_setOf_eq,
    Set.Finite.mem_toFinset] using
    mem_zerosUpToIm_of_entireXi_zero hzero hband himpos himle

lemma mem_zerosUpToIm_finset_divisor_support {T : ℝ} (hSafe : IsSafeHeight T)
    {p : ℂ} (hp : p ∈ zerosUpToImFinset T) :
    p ∈ (divisor_support_criticalBox_finite T).toFinset := by
  simp only [zerosUpToImFinset, Set.Finite.mem_toFinset, zerosUpToIm, nontrivialZeros,
    Set.mem_setOf_eq] at hp
  have hzero := nontrivial_zero_implies_entireXi_zero p hp.1
  have hpbox : p ∈ criticalBoxInterior T := zerosUpToIm_subset_criticalBoxInterior hSafe hp
  have hpR : p ∈ criticalBox T := criticalBoxInterior_subset_criticalBox hpbox
  have hpdiv : p ∈ (MeromorphicOn.divisor entireXi (criticalBox T)).support := by
    rw [Function.mem_support, MeromorphicOn.divisor_apply (entireXi_meromorphicOn_criticalBox T) hpR]
    have hA := analyticAt_entireXi p
    rw [hA.meromorphicOrderAt_eq]
    have hord : analyticOrderAt entireXi p ≠ 0 := (hA.analyticOrderAt_ne_zero).mpr hzero
    cases hO : analyticOrderAt entireXi p with
    | top => exact absurd hO (entireXi_analyticOrderAt_ne_top hzero)
    | coe n =>
      have hn : n ≠ 0 := by
        intro hn0
        exact hord (by rw [hO, hn0, ENat.coe_zero])
      simp [ENat.map_coe]
      exact Nat.cast_ne_zero.mpr hn
  simpa [divisor_support_criticalBox_finite, Set.Finite.mem_toFinset, Function.mem_support,
    MeromorphicOn.divisor] using hpdiv

/-- The finite support of the divisor in the critical box is the zero finset. -/
lemma entireXi_divisor_finset_eq_zerosUpToImFinset (T : ℝ) (hSafe : IsSafeHeight T)
    (hne : entireXi_ne_zero_on_box_boundary T) :
    (divisor_support_criticalBox_finite T).toFinset = zerosUpToImFinset T :=
  Finset.ext fun _ => ⟨
    fun hp => mem_divisor_finset_zerosUpToIm hSafe hne hp,
    fun hp => mem_zerosUpToIm_finset_divisor_support hSafe hp⟩

end RiemannLogResidue
