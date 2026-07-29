/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic

/-!
# Sophie Germain primes

This file contains a small Mathlib-oriented API for Sophie Germain primes and
the elementary congruence restrictions forced by the safe prime `2p + 1`.
-/

@[expose] public section

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

