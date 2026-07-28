/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import PrimeGapsSophie.PrimeGap

/-!
# Higher-order prime gaps

This file proves parity for finite differences of any positive order over
odd primes, using the alternating binomial sum.
-/

@[expose] public section

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
