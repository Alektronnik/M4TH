/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import PrimeGapsSophie.SophieGermain

/-!
# Prime gaps

This file packages the `n`-th prime API used by the prime-gap parity lemmas.
-/

@[expose] public section

namespace PrimeGapsSophie

/-- The `n`-th prime, using Mathlib's `Nat.nth Nat.Prime`. -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

lemma nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

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
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 (Nat.lt_succ_self n)

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
