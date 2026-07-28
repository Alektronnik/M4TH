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
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# XiArgumentPrinciple.live

Single-file live version of the `XiArgumentPrinciple` package.

This file is intentionally independent of local package imports. It fuses the
public source modules in dependency order for web inspection and study.
-/

@[expose] public section


/-!
## Source file: `XiArgumentPrinciple/Basic.lean`
-/


/-!
# Basic infrastructure for `XiArgumentPrinciple`

This file defines the entire Xi variant, its logarithmic derivative, the
critical box, the finite set of nontrivial zeros up to height `T`, and the
analytic multiplicity used in the argument-principle contour chain.
-/


open Complex Topology Filter Set

namespace RiemannArgumentPrinciple

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

/-- The entire Xi variant used for the argument-principle contour chain. -/
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

end RiemannArgumentPrinciple


/-!
## Source file: `XiArgumentPrinciple/Contour.lean`
-/


/-!
# Critical-box contour integrals

This file defines the four oriented edges of the critical box and proves that
the edge-by-edge contour integral agrees with the rectangular integral
convention used by the argument-principle bridge.
-/


open Complex Topology Filter MeasureTheory
open scoped Interval

namespace RiemannArgumentPrinciple

/-- Bottom edge: `γ(t) = t`, `t ∈ [0, 1]`. -/
noncomputable def criticalBoxBottomParam (t : ℝ) : ℂ :=
  (t : ℂ)

/-- Right edge: `γ(t) = 1 + it`, `t ∈ [0, T]`. -/
noncomputable def criticalBoxRightParam (_T t : ℝ) : ℂ :=
  1 + (t : ℂ) * I

/-- Top edge: `γ(t) = t + iT`, traversed by the interval integral `1..0`. -/
noncomputable def criticalBoxTopParam (T t : ℝ) : ℂ :=
  (t : ℂ) + (T : ℂ) * I

/-- Left edge: `γ(t) = it`, traversed by the interval integral `T..0`. -/
noncomputable def criticalBoxLeftParam (_T t : ℝ) : ℂ :=
  (t : ℂ) * I

noncomputable def entireXiBottomLogIntegrand (t : ℝ) : ℂ :=
  deriv criticalBoxBottomParam t * entireXiLogDeriv (criticalBoxBottomParam t)

noncomputable def entireXiRightLogIntegrand (T t : ℝ) : ℂ :=
  deriv (criticalBoxRightParam T) t * entireXiLogDeriv (criticalBoxRightParam T t)

noncomputable def entireXiTopLogIntegrand (T t : ℝ) : ℂ :=
  deriv (criticalBoxTopParam T) t * entireXiLogDeriv (criticalBoxTopParam T t)

noncomputable def entireXiLeftLogIntegrand (T t : ℝ) : ℂ :=
  deriv (criticalBoxLeftParam T) t * entireXiLogDeriv (criticalBoxLeftParam T t)

noncomputable def entireXiBottomEdgeIntegral : ℂ :=
  ∫ t in (0 : ℝ)..1, entireXiBottomLogIntegrand t

noncomputable def entireXiRightEdgeIntegral (T : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..T, entireXiRightLogIntegrand T t

noncomputable def entireXiTopEdgeIntegral (T : ℝ) : ℂ :=
  ∫ t in (1 : ℝ)..0, entireXiTopLogIntegrand T t

noncomputable def entireXiLeftEdgeIntegral (T : ℝ) : ℂ :=
  ∫ t in T..0, entireXiLeftLogIntegrand T t

/-- Integral of `entireXi'/entireXi` around the critical-box boundary. -/
noncomputable def entireXiContourIntegral (T : ℝ) : ℂ :=
  entireXiBottomEdgeIntegral + entireXiRightEdgeIntegral T +
    entireXiTopEdgeIntegral T + entireXiLeftEdgeIntegral T

/-- Rectangular integral over `[0,1] × [0,T]` with counter-clockwise signs. -/
noncomputable def criticalBoxRectangleIntegral (f : ℂ → ℂ) (T : ℝ) : ℂ :=
  (∫ x in (0 : ℝ)..1, f (x : ℂ)) -
    (∫ x in (0 : ℝ)..1, f ((x : ℂ) + (T : ℂ) * I)) +
  (Complex.I • ∫ y in (0 : ℝ)..T, f (1 + (y : ℂ) * I)) -
    (Complex.I • ∫ y in (0 : ℝ)..T, f ((y : ℂ) * I))

lemma deriv_criticalBoxBottomParam (t : ℝ) :
    deriv criticalBoxBottomParam t = 1 := by
  unfold criticalBoxBottomParam
  simpa using (hasDerivAt_id t).ofReal_comp.deriv

lemma deriv_criticalBoxRightParam (T t : ℝ) :
    deriv (criticalBoxRightParam T) t = I := by
  unfold criticalBoxRightParam
  simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).deriv

lemma deriv_criticalBoxTopParam (T t : ℝ) :
    deriv (criticalBoxTopParam T) t = 1 := by
  unfold criticalBoxTopParam
  simpa using ((hasDerivAt_id t).ofReal_comp.add_const ((T : ℂ) * I)).deriv

lemma deriv_criticalBoxLeftParam (T t : ℝ) :
    deriv (criticalBoxLeftParam T) t = I := by
  unfold criticalBoxLeftParam
  simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).deriv

/-- The edge contour equals the rectangular integral. -/
theorem entireXiContourIntegral_eq_rectangleIntegral (T : ℝ) :
    entireXiContourIntegral T =
      criticalBoxRectangleIntegral entireXiLogDeriv T := by
  dsimp only [entireXiContourIntegral, criticalBoxRectangleIntegral,
    entireXiBottomEdgeIntegral, entireXiRightEdgeIntegral,
    entireXiTopEdgeIntegral, entireXiLeftEdgeIntegral,
    entireXiBottomLogIntegrand, entireXiRightLogIntegrand,
    entireXiTopLogIntegrand, entireXiLeftLogIntegrand,
    criticalBoxBottomParam, criticalBoxRightParam, criticalBoxTopParam, criticalBoxLeftParam]
  simp only [deriv_criticalBoxBottomParam, deriv_criticalBoxRightParam,
    deriv_criticalBoxTopParam, deriv_criticalBoxLeftParam, one_mul]
  have htop :
      (∫ t in (1 : ℝ)..0, entireXiLogDeriv (↑t + ↑T * I)) =
        - ∫ t in (0 : ℝ)..1, entireXiLogDeriv (↑t + ↑T * I) := by
    rw [← intervalIntegral.integral_symm]
  have hleft :
      (∫ t in T..0, I * entireXiLogDeriv (↑t * I)) =
        - (Complex.I • ∫ y in (0 : ℝ)..T, entireXiLogDeriv (↑y * I)) := by
    rw [intervalIntegral.integral_symm (0 : ℝ) T, intervalIntegral.integral_const_mul,
      smul_eq_mul]
  have hright :
      (∫ t in (0 : ℝ)..T, I * entireXiLogDeriv (1 + ↑t * I)) =
        Complex.I • ∫ y in (0 : ℝ)..T, entireXiLogDeriv (1 + ↑y * I) := by
    rw [intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [htop, hleft, hright]
  ring

/-- Generic contour logarithmic-derivative integral. -/
noncomputable def contourLogDerivIntegral (f : ℂ → ℂ) (T : ℝ) : ℂ :=
  criticalBoxRectangleIntegral f T

lemma entireXiContourIntegral_eq_contourLogDerivIntegral (T : ℝ) :
    entireXiContourIntegral T = contourLogDerivIntegral entireXiLogDeriv T := by
  dsimp [contourLogDerivIntegral]
  exact entireXiContourIntegral_eq_rectangleIntegral T

end RiemannArgumentPrinciple


/-!
## Source file: `XiArgumentPrinciple/Counting.lean`
-/


/-!
# Argument-principle counting chain

This file packages the critical-box argument-principle chain without adding any
trusted constants.  The genuinely external analytic ingredient is represented
by explicit hypotheses in `ArgumentPrincipleBridge`.
-/


open Complex Topology Filter

namespace RiemannArgumentPrinciple

/-- Cauchy kernel centered at `w`. -/
noncomputable def contourCauchyKernel (w : ℂ) (z : ℂ) : ℂ :=
  1 / (z - w)

/-- Cauchy-index integral over the critical-box boundary. -/
noncomputable def contourCauchyIndexIntegral (w : ℂ) (T : ℝ) : ℂ :=
  criticalBoxRectangleIntegral (contourCauchyKernel w) T

/-- The index of the contour around `w` equals `k`. -/
def ContourWindingIndexEq (T : ℝ) (w : ℂ) (k : ℤ) : Prop :=
  contourCauchyIndexIntegral w T = (k : ℂ) * (2 * Real.pi * I)

/-- The full winding-index statement for a safe critical box. -/
def ContourWindingIndexOne (T : ℝ) : Prop :=
  0 < T ∧
    IsSafeHeight T ∧
      (∀ {w : ℂ}, w ∈ criticalBoxInterior T → ContourWindingIndexEq T w 1) ∧
        (∀ {w : ℂ}, w ∉ criticalBox T → ContourWindingIndexEq T w 0)

/-- Local residue sum over the finite zero set in the critical box. -/
noncomputable def entireXiCriticalBoxResidueSum (T : ℝ) : ℂ :=
  Nat.cast ((zerosUpToImFinset T).sum entireXiZeroMultiplicity)

/-- External analytic bridge for the rectangular argument principle.

In the monolithic research file these statements are supplied by the rectangular
residue theorem infrastructure.  In this standalone package they are explicit
hypotheses, not axioms.
-/
structure ArgumentPrincipleBridge (T : ℝ) : Prop where
  index_one :
    ∀ {w : ℂ}, w ∈ criticalBoxInterior T →
      contourCauchyIndexIntegral w T = 2 * Real.pi * I
  index_zero :
    ∀ {w : ℂ}, w ∉ criticalBox T →
      contourCauchyIndexIntegral w T = 0
  residue_sum :
    entireXiContourIntegral T / (2 * Real.pi * I) = entireXiCriticalBoxResidueSum T

theorem contour_winding_index_one_of_safe {T : ℝ} (hT : 0 < T)
    (hSafe : IsSafeHeight T) (hBridge : ArgumentPrincipleBridge T) :
    ContourWindingIndexOne T := by
  refine ⟨hT, hSafe, ?_, ?_⟩
  · intro w hw
    dsimp [ContourWindingIndexEq]
    simpa [one_mul] using hBridge.index_one hw
  · intro w hw
    dsimp [ContourWindingIndexEq]
    simpa using hBridge.index_zero hw

theorem contour_winding_index_eq_one_iff (T : ℝ) (w : ℂ) :
    ContourWindingIndexEq T w 1 ↔
      contourCauchyIndexIntegral w T = 2 * Real.pi * I := by
  simp [ContourWindingIndexEq, one_mul]

theorem contour_winding_index_eq_zero_iff (T : ℝ) (w : ℂ) :
    ContourWindingIndexEq T w 0 ↔ contourCauchyIndexIntegral w T = 0 := by
  simp [ContourWindingIndexEq, zero_mul]

/-- Every zero counted by `zerosUpToIm T` has winding index `+1`. -/
theorem contour_winding_index_one_on_zerosUpToIm {T : ℝ}
    (hSafe : IsSafeHeight T) (hBridge : ArgumentPrincipleBridge T) :
    ∀ {s : ℂ}, s ∈ zerosUpToIm T → ContourWindingIndexEq T s 1 := by
  intro s hs
  dsimp [ContourWindingIndexEq]
  simpa [one_mul] using hBridge.index_one (zerosUpToIm_subset_criticalBoxInterior hSafe hs)

/-- Residue sum equals multiplicity count under the explicit bridge. -/
def ContourResidueSumEqualsN (T : ℝ) : Prop :=
  ∃ (_hT : 0 < T) (_hSafe : IsSafeHeight T), ∃ (resSum : ℂ),
    resSum = entireXiCriticalBoxResidueSum T ∧
      resSum = entireXiContourIntegral T / (2 * Real.pi * I)

theorem contour_residue_sum_equals_N_of_safe {T : ℝ} (hT : 0 < T)
    (hSafe : IsSafeHeight T) (hBridge : ArgumentPrincipleBridge T) :
    ContourResidueSumEqualsN T := by
  refine ⟨hT, hSafe, entireXiCriticalBoxResidueSum T, rfl, ?_⟩
  exact hBridge.residue_sum.symm

/-- Argument-principle count: the contour integral is `2πi * N(T)`. -/
def ContourWindingEqualsCount (T : ℝ) : Prop :=
  ∃ (_hT : 0 < T) (_hSafe : IsSafeHeight T),
    entireXiContourIntegral T = 2 * Real.pi * I * zeroCountingWithMultiplicity T

theorem contour_winding_equals_count_of_safe {T : ℝ} (hT : 0 < T)
    (hSafe : IsSafeHeight T) (hBridge : ArgumentPrincipleBridge T) :
    ContourWindingEqualsCount T := by
  refine ⟨hT, hSafe, ?_⟩
  have h2pi_ne : (2 * Real.pi * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hdiv :
      entireXiContourIntegral T / (2 * Real.pi * I) =
        (zeroCountingWithMultiplicity T : ℂ) := by
    rw [hBridge.residue_sum]
    simp [entireXiCriticalBoxResidueSum, zeroCountingWithMultiplicity]
  calc
    entireXiContourIntegral T
        = (2 * Real.pi * I) * (entireXiContourIntegral T / (2 * Real.pi * I)) := by
          field_simp [h2pi_ne]
    _ = (2 * Real.pi * I) * (zeroCountingWithMultiplicity T : ℂ) := by rw [hdiv]
    _ = 2 * Real.pi * I * zeroCountingWithMultiplicity T := by ring

/-- Global existence form used by later contour packages. -/
def ContourWindingEqualsCountEventually : Prop :=
  ∀ T > 0, ∃ T' ≥ T, IsSafeHeight T' ∧
    ArgumentPrincipleBridge T' ∧ ContourWindingEqualsCount T'

theorem contour_winding_equals_count_forall
    (h : ∀ T > 0, ∃ T' ≥ T, IsSafeHeight T' ∧ ArgumentPrincipleBridge T') :
    ContourWindingEqualsCountEventually := by
  intro T hT
  obtain ⟨T', hle, hSafe, hBridge⟩ := h T hT
  have hT' : 0 < T' := hT.trans_le hle
  exact ⟨T', hle, hSafe, hBridge, contour_winding_equals_count_of_safe hT' hSafe hBridge⟩

end RiemannArgumentPrinciple
