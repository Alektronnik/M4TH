/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import MertensPNT.ErdosBlocks

set_option linter.style.setOption false
set_option maxHeartbeats 800000

/-!
# Unconditional Mertens product bridge

This file proves the finite identity between Euler products, reciprocal-prime
sums and Mertens corrections, and derives the unconditional compensated
convergence of the product.
-/

/-! ### From `ErdosReciprocals/MertensBridge.lean` -/

/-!
# Puente producto–suma–constante de Mertens

Identidad finita:
`log(∏(1-1/p)) + ∑(1/p) = ∑(log(1-1/p)+1/p)`.
-/

@[expose] public section

namespace ErdosReciprocals

open scoped BigOperators Topology
open Filter Real

/-- Suma parcial de correcciones de Mertens: `∑_{p≤n}(log(1-1/p)+1/p)`. -/
noncomputable def partialMertensCorrection (n : ℕ) : ℝ :=
  ((n + 1).primesBelow).sum fun (p : ℕ) => log (1 - (1 : ℝ) / p) + (1 : ℝ) / p

/-- Identidad de Mertens en sumas parciales. -/
theorem log_partialProduct_add_partialSum_eq_partialMertensCorrection (n : ℕ) :
    log (partialProduct n) + partialSum n = partialMertensCorrection n := by
  unfold partialMertensCorrection
  rw [log_partialProduct_eq_sum, partialSum_eq_primesBelow_sum, ← Finset.sum_add_distrib]

theorem partialProduct_eq_exp_partialMertensCorrection_sub_partialSum {n : ℕ} (hn : 2 ≤ n) :
    partialProduct n = exp (partialMertensCorrection n - partialSum n) := by
  have hpos := partialProduct_pos hn
  have hlog : log (partialProduct n) = partialMertensCorrection n - partialSum n := by
    linarith [log_partialProduct_add_partialSum_eq_partialMertensCorrection n]
  calc
    partialProduct n = exp (log (partialProduct n)) := (exp_log hpos).symm
    _ = exp (partialMertensCorrection n - partialSum n) := by rw [hlog]

theorem partialProduct_eq_exp_mertensConstant_approx_sub_partialSum {n : ℕ} (hn : 2 ≤ n)
    (hM : partialMertensCorrection n = mertensPrimeCorrectionSum) :
    partialProduct n = exp (mertensPrimeCorrectionSum - partialSum n) := by
  rw [partialProduct_eq_exp_partialMertensCorrection_sub_partialSum hn, hM]

lemma partialMertensCorrection_term_le {n : ℕ} {p : ℕ} (hp : p ∈ (n + 1).primesBelow) :
    log (1 - (1 : ℝ) / p) + (1 : ℝ) / p ≤ 2 / (p : ℝ) ^ 2 := by
  have hprime := Nat.prime_of_mem_primesBelow hp
  have h := mertensPrimeCorrection_abs_le ⟨p, hprime⟩
  have heq : mertensPrimeCorrection ⟨p, hprime⟩ = log (1 - (1 : ℝ) / p) + (1 : ℝ) / p := by
    simp [mertensPrimeCorrection, primeR_eq_cast]
  rw [← heq]
  exact (abs_le.mp h).2

theorem partialMertensCorrection_le_two_mul_sum_inv_sq (n : ℕ) :
    partialMertensCorrection n ≤
      2 * ∑ p ∈ (n + 1).primesBelow, (1 : ℝ) / (p : ℝ) ^ 2 := by
  unfold partialMertensCorrection
  calc
    ∑ p ∈ (n + 1).primesBelow, (log (1 - (1 : ℝ) / p) + (1 : ℝ) / p)
        ≤ ∑ p ∈ (n + 1).primesBelow, (2 / (p : ℝ) ^ 2) :=
      Finset.sum_le_sum fun p hp => partialMertensCorrection_term_le hp
    _ = 2 * ∑ p ∈ (n + 1).primesBelow, (1 : ℝ) / (p : ℝ) ^ 2 := by
      simp [div_eq_mul_inv, Finset.mul_sum, mul_comm]

/-- La constante `M` es γ más la serie convergente de correcciones. -/
theorem mertensConstant_eq_gamma_add_correctionSeries :
    mertensConstant = eulerMascheroniConstant + ∑' p : Nat.Primes, mertensPrimeCorrection p := by
  rw [mertensConstant_eq_gamma_add_correctionSum, mertensPrimeCorrectionSum_eq_tsum]

lemma partialMertensCorrection_eq_sum_range (n : ℕ) :
    partialMertensCorrection n =
      ∑ k ∈ Finset.range (Nat.primeCounting n), mertensCorrectionIndexed k := by
  unfold partialMertensCorrection
  have hcard :
      Nat.primeCounting n = (n + 1).primesBelow.card := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.primesBelow_card_eq_primeCounting']
  symm
  have hrange :
      Finset.range (Nat.primeCounting n) = Finset.range ((n + 1).primesBelow.card) := by
    rw [hcard]
  rw [hrange]
  apply Finset.sum_bij (fun k _ => Nat.nth Nat.Prime k)
  · intro k hk
    have hk' : k < Nat.count Nat.Prime (n + 1) := by
      have h1 : k < (n + 1).primesBelow.card := Finset.mem_range.mp hk
      have h2 : (n + 1).primesBelow.card = Nat.count Nat.Prime (n + 1) := by
        simpa [Nat.primeCounting'] using Nat.primesBelow_card_eq_primeCounting' (n + 1)
      exact h2 ▸ h1
    exact Nat.mem_primesBelow.mpr
      ⟨Nat.nth_lt_of_lt_count (p := Nat.Prime) hk',
        Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k⟩
  · intro a ha b hb hab
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hab
  · intro p hp
    refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
    · simp only [Finset.mem_range]
      have hp' := Nat.prime_of_mem_primesBelow hp
      have hlt := Nat.lt_of_mem_primesBelow hp
      have hcount : Nat.count Nat.Prime p < Nat.count Nat.Prime (n + 1) := by
        calc
          Nat.count Nat.Prime p < Nat.count Nat.Prime (p + 1) :=
            Nat.count_lt_count_succ_iff.mpr hp'
          _ ≤ Nat.count Nat.Prime (n + 1) :=
            Nat.count_monotone Nat.Prime (Nat.succ_le_succ (Nat.le_of_lt_succ hlt))
      have hcard' : Nat.count Nat.Prime (n + 1) = (n + 1).primesBelow.card := by
        simpa [Nat.primeCounting'] using (Nat.primesBelow_card_eq_primeCounting' (n + 1)).symm
      exact Nat.lt_of_lt_of_eq hcount hcard'
    · exact Nat.nth_count (Nat.prime_of_mem_primesBelow hp)
  · intro k hk
    simp [mertensCorrectionIndexed, mertensPrimeCorrection, primeR_eq_cast]

/-- Las sumas parciales de correcciones convergen a la serie de Mertens. -/
theorem partialMertensCorrection_tendsto_atTop :
    Tendsto partialMertensCorrection atTop (𝓝 mertensPrimeCorrectionSum) := by
  rw [mertensPrimeCorrectionSum_eq_tsum_indexed, funext partialMertensCorrection_eq_sum_range]
  exact (summable_mertensCorrectionIndexed.hasSum.tendsto_sum_nat).comp
    Nat.tendsto_primeCounting

lemma partialProduct_mul_exp_partialSum_eq_exp_partialMertensCorrection {n : ℕ} (hn : 2 ≤ n) :
    partialProduct n * exp (partialSum n) = exp (partialMertensCorrection n) := by
  rw [partialProduct_eq_exp_partialMertensCorrection_sub_partialSum hn, ← exp_add,
    sub_add_cancel]

/-- `∏(1-1/p) · exp(∑1/p) → exp(∑' corrections)` por continuidad de `exp`. -/
theorem tendsto_partialProduct_mul_exp_partialSum :
    Tendsto (fun n => partialProduct n * exp (partialSum n)) atTop
      (𝓝 (exp mertensPrimeCorrectionSum)) := by
  have h_ev :
      ∀ᶠ n in atTop, partialProduct n * exp (partialSum n) = exp (partialMertensCorrection n) :=
    (eventually_ge_atTop 2).mono fun n hn =>
      partialProduct_mul_exp_partialSum_eq_exp_partialMertensCorrection hn
  exact Tendsto.congr' (EventuallyEq.symm h_ev)
    (Filter.Tendsto.rexp partialMertensCorrection_tendsto_atTop)

lemma partialMertensCorrection_bddAbove : BddAbove (Set.range partialMertensCorrection) :=
  partialMertensCorrection_tendsto_atTop.bddAbove_range

/-- La corrección menos la suma armónica prima diverge a `-∞`. -/
theorem partialMertensCorrection_sub_partialSum_tendsto_atBot :
    Tendsto (fun n => partialMertensCorrection n - partialSum n) atTop atBot := by
  rw [tendsto_atTop_atBot]
  intro M
  rcases partialMertensCorrection_bddAbove with ⟨B, hB⟩
  rcases (tendsto_atTop_atTop.mp tendsto_partialSum_atTop (B - M)) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hSn : B - M ≤ partialSum n := hN n hn
  have hCn : partialMertensCorrection n ≤ B := hB ⟨n, rfl⟩
  linarith

/-- El producto parcial `∏_{p≤n}(1-1/p)` tiende a `0`. -/
theorem partialProduct_tendsto_zero : Tendsto partialProduct atTop (𝓝 0) := by
  have h_ev : ∀ᶠ n in atTop, partialProduct n = exp (partialMertensCorrection n - partialSum n) :=
    (eventually_ge_atTop 2).mono fun n hn =>
      partialProduct_eq_exp_partialMertensCorrection_sub_partialSum hn
  exact Tendsto.congr' (EventuallyEq.symm h_ev)
    (tendsto_exp_atBot.comp partialMertensCorrection_sub_partialSum_tendsto_atBot)

/-!
### Demostración compuesta (sin PNT)

Cadena:
`log ∏ + S = C`  →  `∏ = exp(C - S)`  →  `C → M` acotado, `S → ∞`  →  `∏ → 0`, `∏·exp(S) → exp(M)`.
-/

/-- Convergencia del producto de Euler: correcciones, renormalización y producto crudo. -/
theorem mertens_product_convergence :
    Tendsto partialMertensCorrection atTop (𝓝 mertensPrimeCorrectionSum) ∧
      Tendsto (fun n => partialProduct n * exp (partialSum n)) atTop
        (𝓝 (exp mertensPrimeCorrectionSum)) ∧
      Tendsto partialProduct atTop (𝓝 0) :=
  ⟨partialMertensCorrection_tendsto_atTop, tendsto_partialProduct_mul_exp_partialSum,
    partialProduct_tendsto_zero⟩

lemma partialProduct_mul_exp_partialSum_add_gamma_eq_exp_partialMertensCorrection_add_gamma
    {n : ℕ} (hn : 2 ≤ n) :
    partialProduct n * exp (partialSum n + eulerMascheroniConstant) =
      exp (partialMertensCorrection n + eulerMascheroniConstant) := by
  rw [exp_add, ← mul_assoc, partialProduct_mul_exp_partialSum_eq_exp_partialMertensCorrection hn,
    ← exp_add]

/-- `∏ · exp(S + γ) → exp(M)` con `M = γ + ∑' corrections`. -/
theorem tendsto_partialProduct_mul_exp_partialSum_add_gamma :
    Tendsto (fun n => partialProduct n * exp (partialSum n + eulerMascheroniConstant)) atTop
      (𝓝 (exp mertensConstant)) := by
  have h_ev :
      ∀ᶠ n in atTop,
        partialProduct n * exp (partialSum n + eulerMascheroniConstant) =
          exp (partialMertensCorrection n + eulerMascheroniConstant) :=
    (eventually_ge_atTop 2).mono fun n hn =>
      partialProduct_mul_exp_partialSum_add_gamma_eq_exp_partialMertensCorrection_add_gamma hn
  have hlim :
      Tendsto (fun n => exp (partialMertensCorrection n + eulerMascheroniConstant)) atTop
        (𝓝 (exp (mertensPrimeCorrectionSum + eulerMascheroniConstant))) :=
    Filter.Tendsto.rexp
      (Tendsto.add partialMertensCorrection_tendsto_atTop
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => eulerMascheroniConstant) atTop
          (𝓝 eulerMascheroniConstant)))
  have htarget : exp mertensConstant =
      exp (mertensPrimeCorrectionSum + eulerMascheroniConstant) := by
    congr 1
    rw [mertensConstant_eq_gamma_add_correctionSum, add_comm]
  simpa [htarget] using Tendsto.congr' (EventuallyEq.symm h_ev) hlim

end ErdosReciprocals

/-! ### From `ErdosReciprocals/PrimeZeta.lean` -/

/-!
# Serie prima `∑_p p^r` (criterio de convergencia)

Reexporta el resultado exacto de Mathlib: converge iff `r < -1`.
En particular, `∑ 1/p` diverge y `∑ 1/p²` converge.
-/

namespace ErdosReciprocals

open Real

/-- Criterio de convergencia para potencias primas (Mathlib). -/
theorem primes_summable_rpow_iff {r : ℝ} :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ r) ↔ r < -1 :=
  Nat.Primes.summable_rpow

/-- La serie `∑_p p^{-2}` converge; base de la summability de Mertens. -/
theorem summable_primes_rpow_neg_two :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) :=
  (Nat.Primes.summable_rpow (r := (-2 : ℝ))).mpr (by norm_num : (-2 : ℝ) < -1)

/-- Versión con `primeR`. -/
theorem summable_primes_primeR_rpow {r : ℝ} (hr : r < -1) :
    Summable (fun p : Nat.Primes => primeR p ^ r) := by
  simpa [primeR_eq_cast] using
    (Nat.Primes.summable_rpow (r := r)).mpr hr

end ErdosReciprocals

end
