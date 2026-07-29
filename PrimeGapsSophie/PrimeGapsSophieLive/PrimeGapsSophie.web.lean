/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Tactic

/-!
# PrimeGapsSophie.live

Single-file live version of the `PrimeGapsSophie` package.
-/

@[expose] public section

/-!
## Source file: `PrimeGapsSophie/SophieGermain.lean`
-/

namespace PrimeGapsSophie

/-- A natural number `p` is a Sophie Germain prime if both `p` and `2p + 1`
are prime. -/
def IsSophieGermainPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (2 * p + 1)

/-- If `P = 2p + 1` is a prime at least `5`, then `p` cannot be `1 mod 3`. -/
theorem prime_index_mod3_exclusion
    (P : ℕ) (hP : Nat.Prime P) (hP5 : P ≥ 5) (p : ℕ) (hp : P = 2 * p + 1) :
    p % 3 ≠ 1 := by
  intro h_mod
  have hP_mod3 : P % 3 ≠ 0 := by
    intro hc
    have h_div : 3 ∣ P := Nat.dvd_of_mod_eq_zero hc
    have h_eq_3 : P = 3 := by
      cases hP.eq_one_or_self_of_dvd 3 h_div with
      | inl h1 => contradiction
      | inr h2 => exact h2.symm
    omega
  rw [hp] at hP_mod3
  have h_contra : (2 * p + 1) % 3 = 0 := by
    omega
  exact hP_mod3 h_contra

/-- A Sophie Germain prime `p ≥ 5` is congruent to `2 mod 3`. -/
theorem sophie_germain_mod3_eq_2
    (p : ℕ) (hSG : IsSophieGermainPrime p) (hp5 : p ≥ 5) :
    p % 3 = 2 := by
  have hP_prime := hSG.2
  have hp_prime := hSG.1
  have h_not_1 := prime_index_mod3_exclusion (2 * p + 1) hP_prime (by omega) p rfl
  have h_not_0 : p % 3 ≠ 0 := by
    intro hc
    have h_div : 3 ∣ p := Nat.dvd_of_mod_eq_zero hc
    have hp_eq_3 : p = 3 := by
      cases hp_prime.eq_one_or_self_of_dvd 3 h_div with
      | inl h1 => contradiction
      | inr h2 => exact h2.symm
    omega
  omega

/-- Every prime greater than `2` is odd, in modular form. -/
lemma prime_odd_of_gt_two (p : ℕ) (hp : Nat.Prime p) (hp2 : p > 2) :
    p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h2 | hodd
  · omega
  · exact hodd

/-- A Sophie Germain prime `p ≥ 5` is congruent to `5 mod 6`. -/
theorem sophie_germain_mod6_eq_5
    (p : ℕ) (hSG : IsSophieGermainPrime p) (hp5 : p ≥ 5) :
    p % 6 = 5 := by
  have hmod3 := sophie_germain_mod3_eq_2 p hSG hp5
  have hodd := prime_odd_of_gt_two p hSG.1 (by omega)
  omega

end PrimeGapsSophie

/-!
## Source file: `PrimeGapsSophie/PrimeGap.lean`
-/

namespace PrimeGapsSophie

/-- The `n`-th prime, using Mathlib's `Nat.nth Nat.Prime`. -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

lemma nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n

lemma two_le_nthPrime (n : ℕ) : 2 ≤ nthPrime n :=
  Nat.Prime.two_le (nthPrime_prime n)

lemma nthPrime_ne_zero (n : ℕ) : nthPrime n ≠ 0 := by
  have := two_le_nthPrime n
  omega

/-- Minimal linear lower bound for the `n`-th prime. -/
lemma two_add_le_nthPrime (n : ℕ) : 2 + n ≤ nthPrime n := by
  induction n with
  | zero => simp [nthPrime, Nat.nth_prime_zero_eq_two]
  | succ n ih =>
      have hlt := nthPrime_strictMono (Nat.lt_succ_self n)
      have hstep : nthPrime n + 1 ≤ nthPrime (n + 1) := Nat.succ_le_iff.mpr hlt
      omega

lemma le_nthPrime_self (n : ℕ) : n ≤ nthPrime n :=
  Nat.le_trans (by omega) (two_add_le_nthPrime n)

lemma nthPrime_lt_succ (n : ℕ) : nthPrime n < nthPrime (n + 1) := by
  simpa [nthPrime] using
    (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).2 (Nat.lt_succ_self n)

/-- Gap between consecutive primes. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  nthPrime (n + 1) - nthPrime n

lemma one_le_primeGap (n : ℕ) : 1 ≤ primeGap n := by
  dsimp [primeGap]
  have := nthPrime_lt_succ n
  omega

lemma three_le_nthPrime {n : ℕ} (hn : 1 ≤ n) : 3 ≤ nthPrime n := by
  calc
    3 = nthPrime 1 := by simp [nthPrime, Nat.nth_prime_one_eq_three]
    _ ≤ nthPrime n := nthPrime_strictMono.monotone hn

/-- A prime at least `3` is odd. -/
lemma prime_odd_of_ge_three (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h2 | hodd
  · omega
  · exact hodd

/-- For `n ≥ 1`, the consecutive prime gap `p_{n+1} - p_n` is even. -/
theorem primeGap_even {n : ℕ} (hn : 1 ≤ n) :
    ∃ k : ℤ, (primeGap n : ℤ) = 2 * k := by
  have h0 := prime_odd_of_ge_three (nthPrime n) (nthPrime_prime n) (three_le_nthPrime hn)
  have h1 :=
    prime_odd_of_ge_three (nthPrime (n + 1)) (nthPrime_prime (n + 1))
      (three_le_nthPrime (by omega))
  dsimp [primeGap]
  refine ⟨(nthPrime (n + 1) - nthPrime n) / 2, ?_⟩
  have hlt := nthPrime_lt_succ n
  have heven : ((nthPrime (n + 1) : ℤ) - (nthPrime n : ℤ)) % 2 = 0 := by
    omega
  omega

/-- For `n ≥ 1`, the consecutive prime gap is at least `2`. -/
lemma primeGap_ge_two_of_pos_index (n : ℕ) (hn : 1 ≤ n) :
    2 ≤ primeGap n := by
  have h_odd1 :=
    prime_odd_of_ge_three (nthPrime n) (nthPrime_prime n) (three_le_nthPrime hn)
  have h_odd2 :=
    prime_odd_of_ge_three (nthPrime (n + 1)) (nthPrime_prime (n + 1))
      (three_le_nthPrime (by omega))
  have h_lt := nthPrime_lt_succ n
  dsimp [primeGap]
  omega

end PrimeGapsSophie

/-!
## Source file: `PrimeGapsSophie/HigherOrder.lean`
-/

open Finset

namespace PrimeGapsSophie

/-- Second finite difference of three natural numbers, viewed in `ℤ`. -/
def secondOrderGap (p0 p1 p2 : ℕ) : ℤ :=
  (p2 : ℤ) - 2 * (p1 : ℤ) + (p0 : ℤ)

theorem secondOrderGap_zero_iff_arithmetic_progression (p0 p1 p2 : ℕ) :
    secondOrderGap p0 p1 p2 = 0 ↔ (p1 : ℤ) - (p0 : ℤ) = (p2 : ℤ) - (p1 : ℤ) := by
  dsimp [secondOrderGap]
  omega

/-- The second finite difference of three odd primes is even. -/
theorem secondOrderGap_even_of_odd_primes
    (p0 p1 p2 : ℕ)
    (hp0 : Nat.Prime p0) (hp0_gt : p0 > 2)
    (hp1 : Nat.Prime p1) (hp1_gt : p1 > 2)
    (hp2 : Nat.Prime p2) (hp2_gt : p2 > 2) :
    ∃ k : ℤ, secondOrderGap p0 p1 p2 = 2 * k := by
  have h0 := prime_odd_of_gt_two p0 hp0 hp0_gt
  have h1 := prime_odd_of_gt_two p1 hp1 hp1_gt
  have h2 := prime_odd_of_gt_two p2 hp2 hp2_gt
  dsimp [secondOrderGap]
  use ((p2 : ℤ) - 2 * (p1 : ℤ) + (p0 : ℤ)) / 2
  omega

/-- Third finite difference of four natural numbers, viewed in `ℤ`. -/
def thirdOrderGap (p0 p1 p2 p3 : ℕ) : ℤ :=
  (p3 : ℤ) - 3 * (p2 : ℤ) + 3 * (p1 : ℤ) - (p0 : ℤ)

/-- The third finite difference of four odd primes is even. -/
theorem thirdOrderGap_even_of_odd_primes
    (p0 p1 p2 p3 : ℕ)
    (hp0 : Nat.Prime p0) (hp0_gt : p0 > 2)
    (hp1 : Nat.Prime p1) (hp1_gt : p1 > 2)
    (hp2 : Nat.Prime p2) (hp2_gt : p2 > 2)
    (hp3 : Nat.Prime p3) (hp3_gt : p3 > 2) :
    ∃ k : ℤ, thirdOrderGap p0 p1 p2 p3 = 2 * k := by
  have h0 := prime_odd_of_gt_two p0 hp0 hp0_gt
  have h1 := prime_odd_of_gt_two p1 hp1 hp1_gt
  have h2 := prime_odd_of_gt_two p2 hp2 hp2_gt
  have h3 := prime_odd_of_gt_two p3 hp3 hp3_gt
  dsimp [thirdOrderGap]
  use ((p3 : ℤ) - 3 * (p2 : ℤ) + 3 * (p1 : ℤ) - (p0 : ℤ)) / 2
  omega

/-- Fourth finite difference of five natural numbers, viewed in `ℤ`. -/
def fourthOrderGap (p0 p1 p2 p3 p4 : ℕ) : ℤ :=
  (p4 : ℤ) - 4 * (p3 : ℤ) + 6 * (p2 : ℤ) - 4 * (p1 : ℤ) + (p0 : ℤ)

/-- The fourth finite difference of five odd primes is even. -/
theorem fourthOrderGap_even_of_odd_primes
    (p0 p1 p2 p3 p4 : ℕ)
    (hp0 : Nat.Prime p0) (hp0_gt : p0 > 2)
    (hp1 : Nat.Prime p1) (hp1_gt : p1 > 2)
    (hp2 : Nat.Prime p2) (hp2_gt : p2 > 2)
    (hp3 : Nat.Prime p3) (hp3_gt : p3 > 2)
    (hp4 : Nat.Prime p4) (hp4_gt : p4 > 2) :
    ∃ k : ℤ, fourthOrderGap p0 p1 p2 p3 p4 = 2 * k := by
  have h0 := prime_odd_of_gt_two p0 hp0 hp0_gt
  have h1 := prime_odd_of_gt_two p1 hp1 hp1_gt
  have h2 := prime_odd_of_gt_two p2 hp2 hp2_gt
  have h3 := prime_odd_of_gt_two p3 hp3 hp3_gt
  have h4 := prime_odd_of_gt_two p4 hp4 hp4_gt
  dsimp [fourthOrderGap]
  use ((p4 : ℤ) - 4 * (p3 : ℤ) + 6 * (p2 : ℤ) - 4 * (p1 : ℤ) + (p0 : ℤ)) / 2
  omega

/-- Finite difference of order `N` over an integer-valued sequence. -/
def nthOrderGap (N : ℕ) (p : ℕ → ℤ) : ℤ :=
  ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * p (N - k)

/-- Alternating binomial sum over `ℤ`. -/
lemma sum_alternate_choose_eq_zero (N : ℕ) (hN : N > 0) :
    ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) = 0 := by
  have h_binom := add_pow (-1 : ℤ) (1 : ℤ) N
  have h_zero : (-1 : ℤ) + 1 = 0 := by ring
  rw [h_zero] at h_binom
  have h_zero_pow : (0 : ℤ) ^ N = 0 := zero_pow (ne_of_gt hN)
  rw [h_zero_pow] at h_binom
  calc
    ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * ↑(Nat.choose N k)
        = ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * 1 ^ (N - k) * ↑(Nat.choose N k) := by
            apply sum_congr rfl
            intro x _
            simp only [one_pow, mul_one]
    _ = 0 := h_binom.symm

/-- Any positive-order finite difference of odd primes is even. -/
theorem nthOrderGap_even_of_odd_primes
    (N : ℕ) (hN : N > 0) (p : ℕ → ℕ)
    (h_prime : ∀ i, i ≤ N → Nat.Prime (p i))
    (h_gt_2 : ∀ i, i ≤ N → p i > 2) :
    ∃ k : ℤ, nthOrderGap N (fun i => (p i : ℤ)) = 2 * k := by
  use ∑ k ∈ range (N + 1),
    (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * ((p (N - k) : ℤ) / 2)
  dsimp [nthOrderGap]
  have h_mul :
      2 * ∑ k ∈ range (N + 1),
          (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * ((p (N - k) : ℤ) / 2) =
        ∑ k ∈ range (N + 1),
          (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * (2 * ((p (N - k) : ℤ) / 2)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    ring
  rw [h_mul]
  have h_sum_split :
      ∑ k ∈ range (N + 1),
          (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * (p (N - k) : ℤ) =
        ∑ k ∈ range (N + 1),
            (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * (2 * ((p (N - k) : ℤ) / 2)) +
          ∑ k ∈ range (N + 1),
            (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * 1 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    have hk_le : N - k ≤ N := Nat.sub_le N k
    have h_odd := prime_odd_of_gt_two (p (N - k)) (h_prime _ hk_le) (h_gt_2 _ hk_le)
    have h_div_mod : (p (N - k) : ℤ) = 2 * ((p (N - k) : ℤ) / 2) + 1 := by
      omega
    calc
      (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * (p (N - k) : ℤ)
          = (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) *
              (2 * ((p (N - k) : ℤ) / 2) + 1) :=
                congrArg (HMul.hMul ((-1 : ℤ) ^ k * (Nat.choose N k : ℤ))) h_div_mod
      _ = (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) *
            (2 * ((p (N - k) : ℤ) / 2)) +
          (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * 1 := by ring
  have h_zero_term :
      ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * 1 = 0 := by
    calc
      ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * 1
          = ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) := by simp
      _ = 0 := sum_alternate_choose_eq_zero N hN
  rw [h_zero_term, add_zero] at h_sum_split
  exact h_sum_split

end PrimeGapsSophie

