/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import DirichletEta.Analytic

/-!
# Real positivity and conditional non-vanishing of zeta on `(0, 1)`

The alternating real series is proved positive.  The bridge from the real
alternating limit to the zeta-product identity is exposed as a named
hypothesis `RiemannZetaAlternatingLimitIdentity`, so the package contains no
local trusted declaration.
-/

@[expose] public section

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
