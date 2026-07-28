/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic

/-!
# DirichletEta.live

Single-file live version of the `DirichletEta` package.

This file is intentionally independent of the local package imports.  It fuses
the source modules in dependency order and can be copied to a Lean web session
as a self-contained inspection file.
-/

@[expose] public section

/-!
## Source file: `DirichletEta/Basic.lean`
-/

/-!
# Basic API for the Dirichlet eta function

This file defines the alternating eta terms, the eta series, the zeta-product
normalisation, and the elementary summability and even/odd splitting lemmas in
the half-plane `1 < re s`.
-/

open Complex Filter Finset

namespace DirichletEta

/-- The `n`-th alternating Dirichlet eta term. -/
noncomputable def etaTerm (n : ℕ) (s : ℂ) : ℂ :=
  (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s

/-- The Dirichlet eta series as a complex infinite sum. -/
noncomputable def dirichletEtaSeries (s : ℂ) : ℂ :=
  ∑' n, etaTerm n s

/-- The zeta-product normalisation of Dirichlet eta. -/
noncomputable def dirichletEta (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- Finite partial sums of the eta series. -/
noncomputable def etaPartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, etaTerm n s

lemma eta_summable_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (1 : ℂ) / ((n + 1 : ℂ) ^ s)) := by
  have h_eq :
      (fun n : ℕ => (1 : ℂ) / ((n + 1 : ℂ) ^ s)) =
        (fun n : ℕ => (1 : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s) := by
    ext n
    congr 2
    push_cast
    rfl
  rw [h_eq]
  have h := @summable_nat_add_iff ℂ _ _ _ (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) 1
  rw [h]
  exact Complex.summable_one_div_nat_cpow.mpr hs

lemma eta_summable_odd_term {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (1 : ℂ) / ((2 * (n : ℂ) + 1) ^ s)) := by
  have h_sum : Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have h_inj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro x y h
    dsimp at h
    omega
  have h_comp := h_sum.comp_injective h_inj
  have h_eq :
      (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) ∘ (fun n => 2 * n + 1) =
        (fun n : ℕ => (1 : ℂ) / ((2 * (n : ℂ) + 1) ^ s)) := by
    ext n
    simp only [Function.comp_apply]
    congr 2
    push_cast
    rfl
  rw [h_eq] at h_comp
  exact h_comp

lemma eta_summable_even_term {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (1 : ℂ) / ((2 * (n : ℂ) + 2) ^ s)) := by
  have h_sum : Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have h_inj : Function.Injective (fun n : ℕ => 2 * n + 2) := by
    intro x y h
    dsimp at h
    omega
  have h_comp := h_sum.comp_injective h_inj
  have h_eq :
      (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) ∘ (fun n => 2 * n + 2) =
        (fun n : ℕ => (1 : ℂ) / ((2 * (n : ℂ) + 2) ^ s)) := by
    ext n
    simp only [Function.comp_apply]
    congr 2
    push_cast
    rfl
  rw [h_eq] at h_comp
  exact h_comp

lemma eta_zeta_odd_even_split {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s =
      ∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 1) ^ s) +
        ∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 2) ^ s) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have h_eq :
      (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ s) =
        (fun n : ℕ => (1 : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s) := by
    ext n
    congr 2
    push_cast
    rfl
  rw [h_eq]
  have h_split := (tsum_even_add_odd
    (f := fun n : ℕ => (1 : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s)
    (he := by
      have he_eq :
          (fun k : ℕ => (1 : ℂ) / ((2 * k + 1 : ℕ) : ℂ) ^ s) =
            (fun k : ℕ => (1 : ℂ) / (2 * (k : ℂ) + 1) ^ s) := by
        ext k
        congr 2
        push_cast
        rfl
      rw [he_eq]
      exact eta_summable_odd_term hs)
    (ho := by
      have ho_eq :
          (fun k : ℕ => (1 : ℂ) / ((2 * k + 1 + 1 : ℕ) : ℂ) ^ s) =
            (fun k : ℕ => (1 : ℂ) / (2 * (k : ℂ) + 2) ^ s) := by
        ext k
        congr 2
        push_cast
        ring
      rw [ho_eq]
      exact eta_summable_even_term hs))
  rw [← h_split]
  have h_eq_odd :
      (fun k : ℕ => (1 : ℂ) / ((2 * k + 1 : ℕ) : ℂ) ^ s) =
        (fun k : ℕ => (1 : ℂ) / (2 * (k : ℂ) + 1) ^ s) := by
    ext k
    congr 2
    push_cast
    rfl
  have h_eq_even :
      (fun k : ℕ => (1 : ℂ) / ((2 * k + 1 + 1 : ℕ) : ℂ) ^ s) =
        (fun k : ℕ => (1 : ℂ) / (2 * (k : ℂ) + 2) ^ s) := by
    ext k
    congr 2
    push_cast
    ring
  rw [h_eq_odd, h_eq_even]

lemma eta_even_zeta_term {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 2) ^ s) =
      (2 : ℂ) ^ (-s) * riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have h1 : (2 * (n : ℂ) + 2) = ((2 * (n + 1) : ℕ) : ℂ) := by
    push_cast
    ring
  have h2 : ((2 * (n + 1) : ℕ) : ℂ) ^ s =
      (2 : ℂ) ^ s * (((n + 1 : ℕ) : ℂ)) ^ s := by
    have h_eq : ((2 * (n + 1) : ℕ) : ℂ) = (2 : ℂ) * (((n + 1 : ℕ) : ℂ)) := by
      push_cast
      rfl
    rw [h_eq]
    exact natCast_mul_natCast_cpow 2 (n + 1) s
  rw [h1, h2]
  rw [div_eq_mul_inv, mul_inv, ← div_eq_mul_inv]
  have h3 : (2 : ℂ) ^ (-s) = ((2 : ℂ) ^ s)⁻¹ := by
    exact cpow_neg 2 s
  have h_cast : (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + 1 := by
    push_cast
    rfl
  rw [h3, h_cast]
  ring

lemma eta_eq_zeta_of_re_gt_one {s : ℂ} (hs : 1 < s.re) :
    dirichletEtaSeries s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hz := eta_zeta_odd_even_split hs
  have he := eta_even_zeta_term hs
  have h_pow : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add 1 (-s) (by norm_num : (2 : ℂ) ≠ 0), cpow_one]
  have h2s :
      (2 : ℂ) ^ (1 - s) * riemannZeta s =
        2 * ∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 2) ^ s) := by
    rw [h_pow, mul_assoc, ← he]
  have hη :
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s =
        ∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 1) ^ s) -
          ∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 2) ^ s) := by
    calc
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s
          = riemannZeta s - (2 : ℂ) ^ (1 - s) * riemannZeta s := by
              rw [sub_mul, one_mul]
      _ = (∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 1) ^ s) +
              ∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 2) ^ s)) -
            (2 : ℂ) ^ (1 - s) * riemannZeta s := by rw [hz]
      _ = (∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 1) ^ s) +
              ∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 2) ^ s)) -
            2 * ∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 2) ^ s) := by rw [h2s]
      _ = ∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 1) ^ s) -
            ∑' n : ℕ, (1 : ℂ) / ((2 * (n : ℂ) + 2) ^ s) := by ring
  have hsum : Summable (fun n : ℕ => ((-1 : ℂ) ^ n) / ((n + 1 : ℂ) ^ s)) := by
    have h_alt := Summable.alternating (eta_summable_one_div_nat_add_one_cpow hs)
    have h_eq :
        (fun n : ℕ => ((-1 : ℂ) ^ n) / ((n + 1 : ℂ) ^ s)) =
          (fun n : ℕ => (-1 : ℂ) ^ n * (1 / (n + 1 : ℂ) ^ s)) := by
      ext n
      rw [mul_one_div]
    rw [h_eq]
    exact h_alt
  rw [dirichletEtaSeries, hη]
  have h_split := (tsum_even_add_odd
    (f := fun n : ℕ => ((-1 : ℂ) ^ n) / ((n + 1 : ℂ) ^ s))
    (he := by
      have he_eq :
          (fun k : ℕ => ((-1 : ℂ) ^ (2 * k)) / ((↑(2 * k) + 1 : ℂ) ^ s)) =
            (fun k : ℕ => (1 : ℂ) / (2 * (k : ℂ) + 1) ^ s) := by
        ext k
        congr 2
        · have h_pow_even : (-1 : ℂ) ^ (2 * k) = 1 := by
            rw [pow_mul, neg_one_sq, one_pow]
          exact h_pow_even
        · push_cast
          rfl
      rw [he_eq]
      exact eta_summable_odd_term hs)
    (ho := by
      have ho_eq :
          (fun k : ℕ => ((-1 : ℂ) ^ (2 * k + 1)) / ((↑(2 * k + 1) + 1 : ℂ) ^ s)) =
            (fun k : ℕ => - ((1 : ℂ) / (2 * (k : ℂ) + 2) ^ s)) := by
        ext k
        have h_pow_odd : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
          rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
        rw [h_pow_odd]
        rw [neg_div]
        congr 2
        push_cast
        ring_nf
      rw [ho_eq]
      exact Summable.neg (eta_summable_even_term hs)))
  have h_eta_term :
      (fun n : ℕ => etaTerm n s) =
        (fun n : ℕ => ((-1 : ℂ) ^ n) / ((n + 1 : ℂ) ^ s)) := by
    ext n
    rfl
  rw [h_eta_term, ← h_split]
  have h_odd_tsum :
      (∑' (k : ℕ), ((-1 : ℂ) ^ (2 * k + 1)) /
          ((↑(2 * k + 1) + 1 : ℂ) ^ s)) =
        -∑' (k : ℕ), (1 : ℂ) / (2 * (k : ℂ) + 2) ^ s := by
    have ho_eq :
        (fun k : ℕ => ((-1 : ℂ) ^ (2 * k + 1)) /
            ((↑(2 * k + 1) + 1 : ℂ) ^ s)) =
          (fun k : ℕ => - ((1 : ℂ) / (2 * (k : ℂ) + 2) ^ s)) := by
      ext k
      have h_pow_odd : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
        rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
      rw [h_pow_odd]
      rw [neg_div]
      congr 2
      push_cast
      ring_nf
    rw [ho_eq, tsum_neg]
  have h_even_tsum :
      (∑' (k : ℕ), ((-1 : ℂ) ^ (2 * k)) / ((↑(2 * k) + 1 : ℂ) ^ s)) =
        ∑' (k : ℕ), (1 : ℂ) / (2 * (k : ℂ) + 1) ^ s := by
    have he_eq :
        (fun k : ℕ => ((-1 : ℂ) ^ (2 * k)) / ((↑(2 * k) + 1 : ℂ) ^ s)) =
          (fun k : ℕ => (1 : ℂ) / (2 * (k : ℂ) + 1) ^ s) := by
      ext k
      congr 2
      · have h_pow_even : (-1 : ℂ) ^ (2 * k) = 1 := by
          rw [pow_mul, neg_one_sq, one_pow]
        exact h_pow_even
      · push_cast
        rfl
    rw [he_eq]
  rw [h_odd_tsum, h_even_tsum]
  simp only [sub_eq_add_neg]

lemma etaTerm_ofReal {x : ℝ} (n : ℕ) (_hx : 0 < x) :
    etaTerm n (x : ℂ) = ((((-1 : ℝ) ^ n / (n + 1 : ℝ) ^ x : ℝ) : ℂ)) := by
  simp only [etaTerm]
  have h1 : (n + 1 : ℂ) ^ (x : ℂ) = ((((n + 1 : ℝ) ^ x : ℝ) : ℂ)) := by
    have h_eq : (n + 1 : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [h_eq]
    exact (@ofReal_cpow ((n : ℝ) + 1) (by positivity) x).symm
  rw [h1]
  push_cast
  rfl

end DirichletEta

/-!
## Source file: `DirichletEta/Analytic.lean`
-/

/-!
# Analytic API for the Dirichlet eta product

This file records the differentiability of eta terms and the analyticity of
the zeta-product normalisation on the punctured right half-plane.
-/

open Complex Set

namespace DirichletEta

lemma etaTerm_differentiable (n : ℕ) : Differentiable ℂ (etaTerm n) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  unfold etaTerm
  refine Differentiable.div (differentiable_const _) ?_ ?_
  · refine Differentiable.const_cpow differentiable_id ?_
    exact Or.inl hn
  · simp [hn]

lemma etaPartialSum_differentiable (N : ℕ) : Differentiable ℂ (etaPartialSum N) := by
  unfold etaPartialSum
  have h_eq : (fun s => ∑ n ∈ Finset.range N, etaTerm n s) =
      (∑ n ∈ Finset.range N, etaTerm n) := by
    ext s
    simp only [Finset.sum_apply]
  rw [h_eq]
  exact Differentiable.sum fun n _ => etaTerm_differentiable n

lemma etaTerm_norm_eq {s : ℂ} (n : ℕ) (_hs : 0 < s.re) :
    ‖etaTerm n s‖ = (n + 1 : ℝ) ^ (-s.re) := by
  have hn : 0 < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  unfold etaTerm
  simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow]
  have h_eq : (n + 1 : ℂ) = (((n + 1 : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [h_eq]
  rw [norm_cpow_eq_rpow_re_of_pos hn]
  rw [one_div, Real.rpow_neg (by linarith)]

lemma analyticOn_etaZetaProduct :
    AnalyticOn ℂ (fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
      {s | 0 < s.re ∧ s ≠ 1} := by
  have hU : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
  rw [analyticOn_iff_differentiableOn hU]
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.mul ?_ (differentiableAt_riemannZeta hs.2)
  refine (differentiableAt_const 1).sub ?_
  refine DifferentiableAt.const_cpow ((differentiableAt_const 1).sub differentiableAt_id) ?_
  exact Or.inl (by norm_num : (2 : ℂ) ≠ 0)

lemma analyticOn_dirichletEta :
    AnalyticOn ℂ dirichletEta {s | 0 < s.re ∧ s ≠ 1} := by
  dsimp [dirichletEta]
  exact analyticOn_etaZetaProduct

lemma dirichletEta_eq_zeta_of_re_pos {s : ℂ} (_hs : 0 < s.re) (_hs1 : s ≠ 1) :
    dirichletEta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s :=
  rfl

end DirichletEta

/-!
## Source file: `DirichletEta/Nonvanishing.lean`
-/

/-!
# Real positivity and conditional non-vanishing of zeta on `(0, 1)`

The alternating real series is proved positive.  The bridge from the real
alternating limit to the zeta-product identity is exposed as a named
hypothesis `RiemannZetaAlternatingLimitIdentity`, so the package contains no
local trusted declaration.
-/

open Complex Filter Finset Topology

namespace DirichletEta

/-- Positivity of the alternating real eta series for every real `x > 0`. -/
lemma alternating_zeta_real_pos (x : ℝ) (hx0 : 0 < x) :
    ∃ l,
      Tendsto
        (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (i + 1 : ℝ) ^ x)
        atTop (𝓝 l) ∧
        0 < l := by
  let f : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ) ^ x
  have hfa : Antitone f := by
    intro n m hnm
    dsimp [f]
    gcongr
  have hf0 : Tendsto f atTop (𝓝 0) := by
    dsimp [f]
    have h_pow : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ x) atTop atTop := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      exact (tendsto_rpow_atTop hx0).comp h1
    have h_inv : Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) atTop (𝓝 0) :=
      h_pow.inv_tendsto_atTop
    have h_eq :
        (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ x) =
          (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) := by
      ext n
      rw [one_div, inv_eq_one_div]
    rw [h_eq]
    exact h_inv
  obtain ⟨l, hl⟩ := Antitone.tendsto_alternating_series_of_tendsto_zero hfa hf0
  refine ⟨l, ?_, ?_⟩
  · have h_eq :
        (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i / (i + 1 : ℝ) ^ x) =
          (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * f i) := by
      ext n
      congr 1 with i
      dsimp [f]
      ring
    rwa [h_eq]
  · have h_bound := Antitone.alternating_series_le_tendsto hl hfa 1
    have h_range_2 : (∑ i ∈ range (2 * 1), (-1 : ℝ) ^ i * f i) = f 0 - f 1 := by
      have : 2 * 1 = 2 := by ring
      rw [this, sum_range_succ, sum_range_one]
      dsimp [f]
      ring
    rw [h_range_2] at h_bound
    have hf0_val : f 0 = 1 := by
      dsimp [f]
      simp
    have hf1_val : f 1 = 1 / 2 ^ x := by
      dsimp [f]
      congr 2
      norm_num
    rw [hf0_val, hf1_val] at h_bound
    have h2x : 1 < (2 : ℝ) ^ x := by
      have h_one : (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by simp
      rw [h_one]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hx0
    have h_inv : 1 / (2 : ℝ) ^ x < 1 := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    have h_pos : 0 < 1 - 1 / (2 : ℝ) ^ x := by
      linarith
    exact h_pos.trans_le h_bound

/-- Typed frontier for the continuation identity used on the real interval `0 < x < 1`. -/
def RiemannZetaAlternatingLimitIdentity : Prop :=
  ∀ (x : ℝ), 0 < x → x ≠ 1 → ∀ l : ℝ,
    Tendsto
      (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (i + 1 : ℝ) ^ x)
      atTop (𝓝 l) →
    riemannZeta x * (1 - (2 : ℂ) ^ (1 - (x : ℂ))) = l

/-- Conditional non-vanishing of `ζ(x)` on the real open interval `(0, 1)`. -/
theorem riemannZeta_ne_zero_on_real_open_interval
    (hη : RiemannZetaAlternatingLimitIdentity) (x : ℝ) (hx0 : 0 < x) (hx1lt : x < 1) :
    riemannZeta x ≠ 0 := by
  obtain ⟨l, hl, h_pos⟩ := alternating_zeta_real_pos x hx0
  have hx1 : x ≠ 1 := by linarith
  have h_eq := hη x hx0 hx1 l hl
  intro hz
  have h_mul : riemannZeta x * (1 - (2 : ℂ) ^ (1 - (x : ℂ))) = 0 := by
    rw [hz, zero_mul]
  rw [h_mul] at h_eq
  have : l = 0 := by
    exact_mod_cast h_eq.symm
  linarith

/-- Package-level theorem: eta continuation implies the real non-vanishing API. -/
theorem zeta_real_open_interval_nonvanishing_from_eta
    (hη : RiemannZetaAlternatingLimitIdentity) :
    ∀ x : ℝ, 0 < x → x < 1 → riemannZeta x ≠ 0 :=
  riemannZeta_ne_zero_on_real_open_interval hη

end DirichletEta
