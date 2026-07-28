/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import MertensPNT.MertensConstant

set_option linter.style.setOption false
set_option maxHeartbeats 800000

/-!
# Erdos block construction

This file contains the explicit block endpoints, the iterated Erdos subsequence,
growth certificates, and logarithmic sum bounds.
-/

/-! ### From `ErdosReciprocals/ErdosBlocks.lean` -/

/-!
# Bloques cuantitativos de Erdős

Conectamos el lema de Mathlib con incrementos de `partialSum` y una iteración
que produce crecimiento lineal `S(erdosIter t) ≥ t/2`.
-/

@[expose] public section

namespace ErdosReciprocals

open scoped BigOperators Nat.Prime

/-- Umbral del bloque Erdős: `4^(π(k-1)+1)`. -/
noncomputable def erdosBlockEnd (k : ℕ) : ℕ :=
  4 ^ (k.primesBelow.card + 1)

lemma primesBelow_card_mono {m k : ℕ} (h : m ≤ k) :
    (m.primesBelow).card ≤ (k.primesBelow).card :=
  Finset.card_le_card (Nat.primesBelow_mono h)

/-- Masa mínima del bloque Erdős (forma Finset de Mathlib). -/
theorem erdos_block_mass (k : ℕ) :
    1 / 2 ≤ ∑ p ∈ ((4 ^ (k.primesBelow.card + 1)).succ).primesBelow \ k.primesBelow,
      (1 : ℝ) / p :=
  erdos_half_block_lemma k

/-- Cada bloque Erdős incrementa `partialSum` en al menos `1/2`. -/
theorem partialSum_erdos_block_increment {k : ℕ} (hk : k ≤ erdosBlockEnd k + 1) :
    1 / 2 ≤ partialSum (erdosBlockEnd k) - partialSum (k - 1) := by
  have hsubset :
      k.primesBelow ⊆ (erdosBlockEnd k + 1).primesBelow :=
    primesBelow_subset_primesBelow_succ hk
  rw [partialSum_sdiff hsubset]
  have hfin :
      (erdosBlockEnd k + 1).primesBelow \ k.primesBelow =
        ((4 ^ (k.primesBelow.card + 1)).succ).primesBelow \ k.primesBelow := by
    simp [erdosBlockEnd]
  rw [hfin]
  exact erdos_block_mass k

/-- Primer bloque: `S(4) ≥ 1/2`. -/
theorem partialSum_four_ge_half : 1 / 2 ≤ partialSum 4 := by
  have h := partialSum_erdos_block_increment (k := 0) (by simp [erdosBlockEnd])
  simpa [erdosBlockEnd, partialSum_zero] using h

/-- Iteración Erdős: `0, 4, 4^(π(4)+1), …` -/
noncomputable def erdosIter : ℕ → ℕ
  | 0 => 0
  | t + 1 => erdosBlockEnd (erdosIter t)

lemma erdosIter_succ (t : ℕ) : erdosIter (t + 1) = erdosBlockEnd (erdosIter t) := rfl

lemma four_dvd_erdosBlockEnd (k : ℕ) : 4 ∣ erdosBlockEnd k := by
  unfold erdosBlockEnd
  exact ⟨4 ^ k.primesBelow.card, pow_succ' 4 k.primesBelow.card⟩

lemma erdosIter_le_blockEnd (t : ℕ) : erdosIter t ≤ erdosBlockEnd (erdosIter t) := by
  induction t with
  | zero => simp [erdosIter, erdosBlockEnd]
  | succ t ih =>
    rw [erdosIter_succ]
    unfold erdosBlockEnd
    apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 4)
    exact Nat.succ_le_succ (primesBelow_card_mono ih)

lemma erdosIter_le_blockEnd_succ (t : ℕ) : erdosIter t ≤ erdosBlockEnd (erdosIter t) + 1 :=
  Nat.le_succ_of_le (erdosIter_le_blockEnd t)

lemma erdosIter_mono {m n : ℕ} (hmn : m ≤ n) : erdosIter m ≤ erdosIter n := by
  induction n with
  | zero =>
    rcases Nat.le_zero.mp hmn
    rfl
  | succ n ih =>
    rcases Nat.le_succ_iff.mp hmn with hmn' | rfl
    · exact (ih hmn').trans (erdosIter_le_blockEnd n)
    · rfl

lemma erdosIter_ne_zero {t : ℕ} (ht : t ≠ 0) : erdosIter t ≠ 0 := by
  rcases t with _ | t
  · exact absurd rfl ht
  · simp only [erdosIter, erdosBlockEnd]
    exact ne_of_gt (pow_pos (by norm_num) _)

lemma four_pow_ne_prime {n : ℕ} (hn : 2 ≤ n) : ¬ Nat.Prime (4 ^ n) := by
  intro hp
  have hpos : 0 < n := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have h4 : 4 ∣ 4 ^ n := dvd_pow (dvd_refl 4) (Nat.ne_of_gt hpos)
  have hne : (4 : ℕ) ≠ 1 := by norm_num
  have heq := (Nat.Prime.dvd_iff_eq hp hne).mp h4
  have hinj := Nat.pow_right_injective (by norm_num : 2 ≤ 4)
  have hn1 : n = 1 := hinj (by simpa [pow_one] using heq)
  omega

lemma erdosBlockEnd_not_prime (k : ℕ) : ¬ Nat.Prime (erdosBlockEnd k) := by
  unfold erdosBlockEnd
  rcases k.primesBelow.card + 1 with _ | n
  · simpa [pow_zero] using Nat.not_prime_one
  · rcases n with _ | n
    · decide
    · exact four_pow_ne_prime (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))

lemma erdos_block_primes_sdiff_nonempty (k : ℕ) :
    ((erdosBlockEnd k + 1).primesBelow \ k.primesBelow).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hmass := erdos_block_mass k
  unfold erdosBlockEnd at h hmass
  rw [h, Finset.sum_empty] at hmass
  linarith

lemma primesBelow_ssubset_erdosBlockEnd (k : ℕ) :
    k.primesBelow ⊂ (erdosBlockEnd k).primesBelow := by
  obtain ⟨p, hp⟩ := erdos_block_primes_sdiff_nonempty k
  have ⟨hp_mem, hp_not_low⟩ := Finset.mem_sdiff.mp hp
  have hp_prime := Nat.prime_of_mem_primesBelow hp_mem
  have hk_le_p : k ≤ p :=
    Nat.le_of_not_lt fun hlt => hp_not_low (Nat.mem_primesBelow.mpr ⟨hlt, hp_prime⟩)
  have hp_lt_block : p < erdosBlockEnd k := by
    by_contra hnot
    have hp_ge : erdosBlockEnd k ≤ p := Nat.le_of_not_lt hnot
    have hp_eq : p = erdosBlockEnd k :=
      Nat.eq_of_le_of_lt_succ hp_ge (Nat.lt_of_mem_primesBelow hp_mem)
    exact erdosBlockEnd_not_prime k (hp_eq ▸ hp_prime)
  have hklt : k < erdosBlockEnd k := hk_le_p.trans_lt hp_lt_block
  have hsub : k.primesBelow ⊆ (erdosBlockEnd k).primesBelow := by
    intro x hx
    exact Nat.mem_primesBelow.mpr ⟨(Nat.lt_of_mem_primesBelow hx).trans hklt,
      Nat.prime_of_mem_primesBelow hx⟩
  have hnotsub : ¬ (erdosBlockEnd k).primesBelow ⊆ k.primesBelow := by
    intro h
    exact hp_not_low (h (Nat.mem_primesBelow.mpr ⟨hp_lt_block, hp_prime⟩))
  exact (Finset.ssubset_def).mpr ⟨hsub, hnotsub⟩

lemma primesBelow_card_lt_erdosBlockEnd (k : ℕ) :
    (k.primesBelow).card < (erdosBlockEnd k).primesBelow.card :=
  Finset.card_lt_card (primesBelow_ssubset_erdosBlockEnd k)

lemma primeCounting'_lt_erdosBlockEnd (k : ℕ) :
    Nat.primeCounting' k < Nat.primeCounting' (erdosBlockEnd k) := by
  simpa [Nat.primesBelow_card_eq_primeCounting'] using primesBelow_card_lt_erdosBlockEnd k

lemma erdosIter_not_prime {t : ℕ} (ht : t ≠ 0) : ¬ Nat.Prime (erdosIter t) := by
  rcases t with _ | t
  · exact absurd rfl ht
  · simpa [erdosIter] using erdosBlockEnd_not_prime (erdosIter t)

/-- Tras `t` bloques Erdős, `S(erdosIter t) ≥ t/2`. -/
theorem partialSum_erdosIter_ge_half_mul (t : ℕ) :
    (t : ℝ) / 2 ≤ partialSum (erdosIter t) := by
  induction t with
  | zero => simp [erdosIter, partialSum_zero]
  | succ t ih =>
    by_cases ht : t = 0
    · subst ht
      simpa [erdosIter, erdosBlockEnd] using partialSum_four_ge_half
    · set k := erdosIter t with hkdef
      have hinc := partialSum_erdos_block_increment (erdosIter_le_blockEnd_succ t)
      have hk₀ : k ≠ 0 := erdosIter_ne_zero ht
      have heq : partialSum k = partialSum (k - 1) := by
        by_cases hkp : Nat.Prime k
        · exact (erdosIter_not_prime ht hkp).elim
        · exact (partialSum_pred_eq_of_not_prime hk₀ hkp).symm
      rw [← hkdef] at hinc
      rw [heq] at ih
      rw [erdosIter_succ, ← hkdef]
      calc
        (↑(t + 1) : ℝ) / 2 = (↑t : ℝ) / 2 + 1 / 2 := by
          simp [Nat.cast_add, div_eq_mul_inv]
          ring
        _ ≤ partialSum (k - 1) + 1 / 2 := add_le_add ih (le_refl _)
        _ ≤ partialSum (erdosBlockEnd k) := by linarith

end ErdosReciprocals

/-! ### From `ErdosReciprocals/LogSumBounds.lean` -/

/-!
# Cotas entre `partialLogSum` y `partialSum`

Para `p ≥ 2` se tiene `log 2 ≤ log p ≤ log n` cuando `p ≤ n`.
-/

namespace ErdosReciprocals

open Real

lemma partialLogSum_ge_log_two_mul_partialSum (n : ℕ) :
    log 2 * partialSum n ≤ partialLogSum n := by
  rw [partialSum_eq_primesBelow_sum,
    show log 2 * (∑ p ∈ (n + 1).primesBelow, (1 : ℝ) / p) =
        ∑ p ∈ (n + 1).primesBelow, log 2 * ((1 : ℝ) / p) from Finset.mul_sum _ _ _]
  simp only [partialLogSum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp' := Nat.prime_of_mem_primesBelow hp
  have hlog : log 2 ≤ log (p : ℝ) :=
    (log_le_log_iff (by norm_num) (mod_cast hp'.pos)).mpr (mod_cast hp'.two_le)
  have hpos : 0 ≤ (1 : ℝ) / p := by positivity
  calc log 2 * ((1 : ℝ) / p)
      ≤ log (p : ℝ) * ((1 : ℝ) / p) := mul_le_mul_of_nonneg_right hlog hpos
    _ = log (p : ℝ) / (p : ℝ) := by ring

lemma partialLogSum_le_log_mul_partialSum {n : ℕ} (hn : 1 < n) :
    partialLogSum n ≤ log n * partialSum n := by
  have hterm :
      ∀ p ∈ (n + 1).primesBelow, log (p : ℝ) / (p : ℝ) ≤ log n * ((1 : ℝ) / p) := fun p hp => by
    have hp' := Nat.prime_of_mem_primesBelow hp
    have hpn : p ≤ n := Nat.le_of_lt_succ (Nat.lt_of_mem_primesBelow hp)
    have hnpos : (0 : ℝ) < n := mod_cast (Nat.zero_lt_of_lt hn)
    have hlog : log (p : ℝ) ≤ log n :=
      (log_le_log_iff (mod_cast hp'.pos) hnpos).mpr (mod_cast hpn)
    have hpos : 0 ≤ (1 : ℝ) / p := by positivity
    calc log (p : ℝ) / (p : ℝ)
        ≤ log n / (p : ℝ) := by gcongr
      _ = log n * ((1 : ℝ) / p) := by ring
  calc
    partialLogSum n
        = ∑ p ∈ (n + 1).primesBelow, log (p : ℝ) / (p : ℝ) := by simp [partialLogSum]
    _ ≤ ∑ p ∈ (n + 1).primesBelow, log n * ((1 : ℝ) / p) := Finset.sum_le_sum hterm
    _ = log n * partialSum n := by
      rw [← Finset.mul_sum, partialSum_eq_primesBelow_sum]

/-- Versión explícita de la cota superior de Chebyshev en términos de `S(n)`. -/
theorem partialLogSum_le_log4_mul_n (n : ℕ) :
    partialLogSum n ≤ log 4 / 2 * n := by
  calc
    partialLogSum n ≤ log 4 * n / 2 := partialLogSum_le_log4_mul_div_two n
    _ = log 4 / 2 * n := by ring

end ErdosReciprocals

/-! ### From `ErdosReciprocals/ErdosGrowth.lean` -/

/-!
# Crecimiento de `erdosIter` y contraste asintótico

* `erdosIter t → ∞`
* `log (erdosIter t)`, `log log (erdosIter t) → ∞`
* `S(erdosIter t) - log(erdosIter t)` permanece acotado arriba (vía armónicos)
* `S(erdosIter t) ≥ t/2` crece linealmente en el índice
-/

namespace ErdosReciprocals

open scoped Topology Nat.Prime
open Filter Real

lemma succ_le_quart_pow (n : ℕ) : n + 1 ≤ 4 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih => omega

lemma le_primesBelow_card_erdosIter (t : ℕ) : t ≤ (erdosIter t).primesBelow.card := by
  induction t with
  | zero => simp [erdosIter]
  | succ t ih =>
    rw [erdosIter_succ]
    have hlt := primeCounting'_lt_erdosBlockEnd (erdosIter t)
    have hih : t ≤ Nat.primeCounting' (erdosIter t) := by
      simpa [Nat.primesBelow_card_eq_primeCounting'] using ih
    have hle : t + 1 ≤ Nat.primeCounting' (erdosBlockEnd (erdosIter t)) :=
      (Nat.succ_le_succ hih).trans (Nat.succ_le_of_lt hlt)
    simpa [Nat.primesBelow_card_eq_primeCounting'] using hle

lemma le_primeCounting_erdosIter (t : ℕ) : t ≤ Nat.primeCounting (erdosIter t) := by
  have hcard : t ≤ Nat.primeCounting' (erdosIter t) := by
    simpa [Nat.primesBelow_card_eq_primeCounting'] using le_primesBelow_card_erdosIter t
  simpa [Nat.primeCounting_eq_primeCounting'_succ] using
    hcard.trans (Nat.monotone_primeCounting' (Nat.le_succ (erdosIter t)))

theorem exists_erdosIter_ge (M : ℕ) : ∃ t, M ≤ erdosIter t := by
  refine ⟨M, ?_⟩
  induction M with
  | zero => simp [erdosIter]
  | succ M ih =>
    rw [erdosIter_succ, erdosBlockEnd]
    have hk : M + 1 ≤ (erdosIter M).primesBelow.card + 1 :=
      Nat.succ_le_succ (le_primesBelow_card_erdosIter M)
    exact hk.trans (succ_le_quart_pow (erdosIter M).primesBelow.card)

theorem tendsto_erdosIter_atTop : Tendsto erdosIter atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  rcases exists_erdosIter_ge M with ⟨t, ht⟩
  refine ⟨t, fun s hs => ht.trans (erdosIter_mono hs)⟩

theorem tendsto_natCast_erdosIter_atTop :
    Tendsto (fun t : ℕ => (erdosIter t : ℝ)) atTop atTop := by
  exact tendsto_natCast_atTop_atTop.comp tendsto_erdosIter_atTop

theorem tendsto_log_erdosIter_atTop :
    Tendsto (fun t : ℕ => log (erdosIter t)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_erdosIter_atTop

theorem tendsto_log_log_comp_erdosIter_atTop :
    Tendsto (fun t : ℕ => log (log (erdosIter t))) atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_erdosIter_atTop

theorem partialSum_erdosIter_sub_log_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ t ≥ T, partialSum (erdosIter t) - log (erdosIter t) < eulerMascheroniConstant + ε := by
  rcases partialSum_sub_log_eventually_lt ε hε with ⟨N, hN⟩
  rcases (tendsto_atTop_atTop.mp tendsto_erdosIter_atTop N) with ⟨T, hT⟩
  refine ⟨T, fun t ht => hN _ (hT t ht)⟩

theorem not_tendsto_partialSum_sub_log_comp_erdosIter_atTop :
    ¬ Tendsto (fun t : ℕ => partialSum (erdosIter t) - log (erdosIter t)) atTop atTop := by
  intro h
  rcases partialSum_erdosIter_sub_log_eventually_lt 1 one_pos with ⟨T, hT⟩
  rcases (tendsto_atTop_atTop.mp h (eulerMascheroniConstant + 2)) with ⟨S, hS⟩
  have := hS (max S T) (le_max_left S T)
  have := hT (max S T) (le_max_right S T)
  linarith [Real.one_half_lt_eulerMascheroniConstant]

end ErdosReciprocals

end
