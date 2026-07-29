/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# Basic API for the Dirichlet eta function

This file defines the alternating eta terms, the eta series, the zeta-product
normalisation, and the elementary summability and even/odd splitting lemmas in
the half-plane `1 < re s`.
-/

@[expose] public section

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

