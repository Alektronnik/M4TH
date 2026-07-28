/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import MertensPNT.Basic

set_option linter.style.setOption false
set_option maxHeartbeats 800000

/-!
# The Meissel-Mertens constant

This file defines the prime correction series and the Meissel-Mertens constant
`mertensConstant = gamma + tsum corrections`, with summability certificates and
the elementary one-sided asymptotic boundary.
-/

/-! ### From `ErdosReciprocals/MertensConstant.lean` -/

/-!
# Constante de Mertens (definición analítica)

`M = γ + ∑'_p (log(1 - 1/p) + 1/p)`, con serie de corrección summable por `O(1/p²)`.
-/

@[expose] public section

namespace ErdosReciprocals

open scoped BigOperators Topology
open Filter Real

lemma primeR_eq_cast (p : Nat.Primes) : primeR p = (p : ℝ) := by
  unfold primeR
  rfl

/-- Corrección de Mertens en un primo: `log(1 - 1/p) + 1/p`. -/
noncomputable def mertensPrimeCorrection (p : Nat.Primes) : ℝ :=
  log (1 - 1 / primeR p) + 1 / primeR p

lemma inv_primeR_pos (p : Nat.Primes) : 0 < 1 / primeR p :=
  one_div_pos.mpr (primeR_pos p)

lemma inv_primeR_lt_one (p : Nat.Primes) : |1 / primeR p| < 1 := by
  rw [abs_of_pos (inv_primeR_pos p)]
  have hp1 := one_lt_primeR p
  rwa [one_div_lt (by positivity) zero_lt_one, one_div_one]

lemma inv_primeR_lt_one' (p : Nat.Primes) : 1 / primeR p < 1 := by
  have hp1 := one_lt_primeR p
  rwa [one_div_lt (by positivity) zero_lt_one, one_div_one]

lemma inv_primeR_le_half (p : Nat.Primes) : 1 / primeR p ≤ 1 / 2 := by
  gcongr
  exact two_le_primeR p

lemma mertensPrimeCorrection_eq_neg_tsum (p : Nat.Primes) :
    mertensPrimeCorrection p =
      -∑' n : ℕ, (1 / primeR p) ^ (n + 2) / (n + 2) := by
  have hx := inv_primeR_lt_one p
  have hf := (hasSum_pow_div_log_of_abs_lt_one hx).summable
  have hsum := (hasSum_pow_div_log_of_abs_lt_one hx).tsum_eq
  have hsplit := hf.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at hsplit
  have hindex (n : ℕ) :
      (1 / primeR p) ^ (n + 1 + 1) / (↑(n + 1) + 1) =
        (1 / primeR p) ^ (n + 2) / (↑n + 2) := by
    rw [show n + 1 + 1 = n + 2 by ring,
      show (↑(n + 1) + 1 : ℝ) = ↑(n + 2) by norm_cast,
      show (↑n + 2 : ℝ) = ↑(n + 2) by norm_cast]
  have htail_eq :
      ∑' i : ℕ, (1 / primeR p) ^ (i + 1 + 1) / (↑(i + 1) + 1) =
        ∑' i : ℕ, (1 / primeR p) ^ (i + 2) / (↑i + 2) :=
    tsum_congr fun i => hindex i
  have hmain :
      (1 / primeR p) + ∑' n : ℕ, (1 / primeR p) ^ (n + 2) / (n + 2) =
        -log (1 - 1 / primeR p) := by
    have hsplit' := hsplit.trans hsum
    convert hsplit' using 2
    · simp [pow_one, div_one]
    · simp_rw [htail_eq]
  dsimp [mertensPrimeCorrection]
  linarith

lemma tsum_inv_primeR_pow_add_geometric (p : Nat.Primes) :
    ∑' n : ℕ, (1 / primeR p) ^ (n + 2) = (1 / primeR p) ^ 2 / (1 - 1 / primeR p) := by
  set r := 1 / primeR p
  have hx := inv_primeR_lt_one p
  have hr : |r| < 1 := by simpa [r] using hx
  have hr1 : r < 1 := by simpa [r] using inv_primeR_lt_one' p
  have hpos : 0 < 1 - r := sub_pos.mpr hr1
  have hsum : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ := by simpa [r] using tsum_geometric_of_abs_lt_one hr
  have hsplit := (summable_geometric_of_abs_lt_one hr).sum_add_tsum_nat_add 2
  rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one] at hsplit
  rw [hsum] at hsplit
  have htail : ∑' n : ℕ, r ^ (n + 2) = (1 - r)⁻¹ - 1 - r := by linarith
  have halgebra : (1 - r)⁻¹ - 1 - r = r ^ 2 / (1 - r) := by
    field_simp [hpos.ne']
    ring
  calc
    ∑' n : ℕ, (1 / primeR p) ^ (n + 2) = ∑' n : ℕ, r ^ (n + 2) := by simp only [r]
    _ = (1 - r)⁻¹ - 1 - r := htail
    _ = r ^ 2 / (1 - r) := halgebra
    _ = (1 / primeR p) ^ 2 / (1 - 1 / primeR p) := by simp only [r, div_eq_mul_inv, pow_two]

lemma mertensPrimeCorrection_abs_le (p : Nat.Primes) :
    |mertensPrimeCorrection p| ≤ 2 / primeR p ^ 2 := by
  have hxpos := inv_primeR_pos p
  have hx := inv_primeR_lt_one p
  have hx1 := inv_primeR_lt_one' p
  have hxle := inv_primeR_le_half p
  rw [mertensPrimeCorrection_eq_neg_tsum]
  have hnonneg : 0 ≤ ∑' n : ℕ, (1 / primeR p) ^ (n + 2) / (n + 2) := by
    refine tsum_nonneg fun n => ?_
    positivity
  rw [abs_neg, abs_of_nonneg hnonneg]
  have hterm (n : ℕ) :
      (1 / primeR p) ^ (n + 2) / (n + 2) ≤ (1 / primeR p) ^ (n + 2) := by
    have hn : 0 < (n + 2 : ℝ) := by norm_cast; omega
    have hpow := pow_nonneg (inv_primeR_pos p).le (n + 2)
    rw [div_le_iff₀ hn]
    apply le_mul_of_one_le_right hpow
    norm_cast
    omega
  have hg : Summable fun (n : ℕ) => (1 / primeR p) ^ (n + 2) :=
    (summable_nat_add_iff 2).mpr (summable_geometric_of_abs_lt_one hx)
  have hf_tail : Summable fun (n : ℕ) => (1 / primeR p) ^ (n + 2) / (n + 2) := by
    refine Summable.of_norm_bounded hg ?_
    intro n
    rw [norm_eq_abs, abs_div, abs_of_pos (pow_pos hxpos _)]
    have hn : 0 < (n + 2 : ℝ) := by norm_cast; omega
    rw [abs_of_pos hn]
    exact hterm n
  have hle :
      ∑' n : ℕ, (1 / primeR p) ^ (n + 2) / (n + 2) ≤ ∑' n : ℕ, (1 / primeR p) ^ (n + 2) :=
    Summable.tsum_mono hf_tail hg fun n => hterm n
  have hgeo :=
    tsum_inv_primeR_pow_add_geometric p
  have hbound :
      (1 / primeR p) ^ 2 / (1 - 1 / primeR p) ≤ 2 * (1 / primeR p) ^ 2 := by
    rw [div_le_iff₀ (sub_pos.mpr hx1)]
    nlinarith [hxle]
  calc
    ∑' n : ℕ, (1 / primeR p) ^ (n + 2) / (n + 2) ≤ ∑' n : ℕ, (1 / primeR p) ^ (n + 2) := hle
    _ = (1 / primeR p) ^ 2 / (1 - 1 / primeR p) := hgeo
    _ ≤ 2 * (1 / primeR p) ^ 2 := hbound
    _ = 2 / primeR p ^ 2 := by field_simp [pow_two]

/-- Corrección de Mertens indexada por `k` ↦ `k`-ésimo primo. -/
noncomputable def mertensCorrectionIndexed (k : ℕ) : ℝ :=
  mertensPrimeCorrection ⟨Nat.nth Nat.Prime k, Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k⟩

noncomputable def natPrimesEquiv : ℕ ≃ Nat.Primes where
  toFun k := ⟨Nat.nth Nat.Prime k, Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k⟩
  invFun p := Nat.count Nat.Prime p
  left_inv k := Nat.count_nth_of_infinite Nat.infinite_setOf_prime k
  right_inv p := Subtype.ext (Nat.nth_count (p := Nat.Prime) p.property)

/-- La serie de corrección sobre primos converge. -/
theorem summable_mertensPrimeCorrection :
    Summable mertensPrimeCorrection := by
  have hcomp := (Nat.Primes.summable_rpow (r := (-2 : ℝ))).mpr (by norm_num : (-2 : ℝ) < -1)
  refine Summable.of_norm_bounded (Summable.mul_left 2 hcomp) fun p => ?_
  rw [Real.norm_eq_abs]
  have heq : (2 : ℝ) / primeR p ^ 2 = 2 * (p : ℝ) ^ (-2 : ℝ) := by
    have h : (1 : ℝ) / primeR p ^ 2 = (primeR p : ℝ) ^ (-2 : ℝ) := by
      have hmid : (1 / primeR p) ^ 2 = (primeR p ^ 2)⁻¹ := by
        rw [← one_div, one_div_pow]
      have hrpow : (primeR p ^ 2)⁻¹ = (primeR p : ℝ) ^ (-2 : ℝ) := by
        symm
        simp [Real.rpow_neg (primeR_pos p).le]
      simpa [← one_div_pow] using hmid.trans hrpow
    calc
      (2 : ℝ) / primeR p ^ 2 = 2 * (1 / primeR p ^ 2) := by ring
      _ = 2 * (primeR p : ℝ) ^ (-2 : ℝ) := by rw [h]
      _ = 2 * (p : ℝ) ^ (-2 : ℝ) := by rw [primeR_eq_cast]
  calc
    |mertensPrimeCorrection p| ≤ 2 / primeR p ^ 2 := mertensPrimeCorrection_abs_le p
    _ = 2 * (p : ℝ) ^ (-2 : ℝ) := heq

/-- Suma de las correcciones primas (serie convergente). -/
noncomputable def mertensPrimeCorrectionSum : ℝ :=
  ∑' p : Nat.Primes, mertensPrimeCorrection p

theorem mertensPrimeCorrectionSum_eq_tsum :
    mertensPrimeCorrectionSum = ∑' p : Nat.Primes, mertensPrimeCorrection p := rfl

theorem summable_mertensCorrectionIndexed : Summable mertensCorrectionIndexed := by
  have h := (natPrimesEquiv.summable_iff (f := mertensPrimeCorrection)).mpr
    summable_mertensPrimeCorrection
  have heq : mertensCorrectionIndexed = mertensPrimeCorrection ∘ ⇑natPrimesEquiv := by
    funext k
    simp [mertensCorrectionIndexed, natPrimesEquiv]
  rw [heq]
  exact h

theorem mertensPrimeCorrectionSum_eq_tsum_indexed :
    mertensPrimeCorrectionSum = ∑' k : ℕ, mertensCorrectionIndexed k := by
  rw [mertensPrimeCorrectionSum_eq_tsum, ← natPrimesEquiv.tsum_eq]
  simp [mertensCorrectionIndexed, natPrimesEquiv]

/-- Constante de Mertens: `γ + ∑'_p (log(1 - 1/p) + 1/p)`. -/
noncomputable def mertensConstant : ℝ :=
  eulerMascheroniConstant + mertensPrimeCorrectionSum

theorem mertensConstant_eq_gamma_add_correctionSum :
    mertensConstant = eulerMascheroniConstant + mertensPrimeCorrectionSum := rfl

/-- Valor numérico de referencia (tabla `../data/`). -/
noncomputable def mertensConstantApprox : ℝ := 0.26149721284478386

theorem mertensConstantApprox_pos : 0 < mertensConstantApprox := by
  unfold mertensConstantApprox
  norm_num

end ErdosReciprocals

/-! ### From `ErdosReciprocals/Asymptotics.lean` -/

/-!
# Asintótica unilateral disponible (sin PNT)

De `S(n) ≤ H_n` y `H_n - log n → γ` (Mathlib) se deduce una cota superior
asintótica para `S(n) - log n`. Esto es estrictamente más débil que Mertens
(`S(n) ~ log log n + M`), pero es completamente riguroso con la infraestructura actual.
-/

namespace ErdosReciprocals

open scoped Topology
open Filter Real

/-- `S(n) - log n` está acotado superiormente por `H_n - log n`. -/
theorem partialSum_sub_log_le_harmonic_sub_log (n : ℕ) :
    partialSum n - log n ≤ harmonic n - log n := by
  have := partialSum_le_harmonic n
  linarith

/-- Existe `N` tal que `S(n) - log n < γ + ε` para todo `n ≥ N`. -/
theorem partialSum_sub_log_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, partialSum n - log n < eulerMascheroniConstant + ε := by
  set U := Set.Ioo (eulerMascheroniConstant - 1) (eulerMascheroniConstant + ε)
  have hmem : eulerMascheroniConstant ∈ U :=
    ⟨by linarith [Real.one_half_lt_eulerMascheroniConstant], lt_add_of_pos_right _ hε⟩
  rcases ((tendsto_atTop_nhds (α := ℕ)).1 Real.tendsto_harmonic_sub_log U hmem isOpen_Ioo) with
    ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hn' := hN n hn
  simp only [U, Set.mem_Ioo] at hn'
  linarith [partialSum_sub_log_le_harmonic_sub_log n, hn'.2]

/-- `S(n) - log n` no puede tender a `+∞`. -/
theorem not_tendsto_partialSum_sub_log_atTop :
    ¬ Tendsto (fun n : ℕ => partialSum n - log n) atTop atTop := by
  intro h
  rcases partialSum_sub_log_eventually_lt 1 one_pos with ⟨S, hS⟩
  rcases (tendsto_atTop_atTop.mp h (eulerMascheroniConstant + 2)) with ⟨N, hN⟩
  have := hN (max N S) (le_max_left N S)
  have := hS _ (le_max_right N S)
  linarith [Real.one_half_lt_eulerMascheroniConstant]

end ErdosReciprocals

end
