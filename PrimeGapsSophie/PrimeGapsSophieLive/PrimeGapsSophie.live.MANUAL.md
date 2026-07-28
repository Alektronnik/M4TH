# PrimeGapsSophie.live

**Author:** Bezalel Izquierdo Pérez  
**License:** Apache 2.0  
**Live file:** `PrimeGapsSophie.live.lean`

---

## I. Mathematical Aim

`PrimeGapsSophie.live.lean` is the single-file reading version of the
`PrimeGapsSophie` package.

The package isolates two elementary but useful arithmetic layers:

- congruence restrictions for Sophie Germain primes;
- parity of consecutive and higher-order finite differences of odd primes.

The package is Mathlib-oriented.  It does not include the larger research
framework based on affine transforms of prime gaps.  Its public content is the
small reusable API around `Nat.Prime`, `Nat.nth Nat.Prime`, prime gaps, and
binomial finite differences.

---

## II. Source Architecture

The live file is a faithful fusion of the public package modules:

```text
PrimeGapsSophie/SophieGermain.lean
PrimeGapsSophie/PrimeGap.lean
PrimeGapsSophie/HigherOrder.lean
```

The namespace is:

```lean
namespace PrimeGapsSophie
```

The live file imports only Mathlib modules.  It does not import the local
package modules, because the source content is present directly in the file.

---

## III. Sophie Germain Primes

> **Definition 1. Sophie Germain prime.**
>
> A natural number `p` is Sophie Germain when both `p` and `2p + 1` are prime.
>
> **In Lean:**
>
> ```lean
> def IsSophieGermainPrime (p : ℕ) : Prop :=
>   Nat.Prime p ∧ Nat.Prime (2 * p + 1)
> ```

> **Theorem 1. Prime-index exclusion modulo 3.**
>
> If `P = 2p + 1` is prime and `P ≥ 5`, then `p` is not congruent to `1`
> modulo `3`.
>
> **In Lean:**
>
> ```lean
> theorem prime_index_mod3_exclusion
>     (P : ℕ) (hP : Nat.Prime P) (hP5 : P ≥ 5)
>     (p : ℕ) (hp : P = 2 * p + 1) :
>     p % 3 ≠ 1
> ```

> **Theorem 2. Sophie Germain congruence modulo 3.**
>
> **In Lean:**
>
> ```lean
> theorem sophie_germain_mod3_eq_2
>     (p : ℕ) (hSG : IsSophieGermainPrime p) (hp5 : p ≥ 5) :
>     p % 3 = 2
> ```

> **Theorem 3. Prime greater than two is odd.**
>
> **In Lean:**
>
> ```lean
> lemma prime_odd_of_gt_two
>     (p : ℕ) (hp : Nat.Prime p) (hp2 : p > 2) :
>     p % 2 = 1
> ```

> **Theorem 4. Sophie Germain congruence modulo 6.**
>
> Combining the modulo `3` restriction with oddness gives the familiar
> congruence class.
>
> **In Lean:**
>
> ```lean
> theorem sophie_germain_mod6_eq_5
>     (p : ℕ) (hSG : IsSophieGermainPrime p) (hp5 : p ≥ 5) :
>     p % 6 = 5
> ```

---

## IV. The N-th Prime and Consecutive Prime Gaps

> **Definition 2. The n-th prime.**
>
> The package uses Mathlib's `Nat.nth Nat.Prime`.
>
> **In Lean:**
>
> ```lean
> noncomputable def nthPrime (n : ℕ) : ℕ :=
>   Nat.nth Nat.Prime n
> ```

> **Theorem 5. Strict monotonicity of `nthPrime`.**
>
> **In Lean:**
>
> ```lean
> lemma nthPrime_strictMono : StrictMono nthPrime
> ```

> **Theorem 6. The n-th prime is prime.**
>
> **In Lean:**
>
> ```lean
> lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n)
> ```

> **Theorem 7. Lower bound by two.**
>
> **In Lean:**
>
> ```lean
> lemma two_le_nthPrime (n : ℕ) : 2 ≤ nthPrime n
> ```

> **Theorem 8. Minimal linear lower bound.**
>
> **In Lean:**
>
> ```lean
> lemma two_add_le_nthPrime (n : ℕ) :
>     2 + n ≤ nthPrime n
> ```

> **Theorem 9. Strict increase at successors.**
>
> **In Lean:**
>
> ```lean
> lemma nthPrime_lt_succ (n : ℕ) :
>     nthPrime n < nthPrime (n + 1)
> ```

> **Definition 3. Consecutive prime gap.**
>
> **In Lean:**
>
> ```lean
> noncomputable def primeGap (n : ℕ) : ℕ :=
>   nthPrime (n + 1) - nthPrime n
> ```

> **Theorem 10. Prime gaps are positive.**
>
> **In Lean:**
>
> ```lean
> lemma one_le_primeGap (n : ℕ) :
>     1 ≤ primeGap n
> ```

> **Theorem 11. The n-th prime is at least three for `n ≥ 1`.**
>
> **In Lean:**
>
> ```lean
> lemma three_le_nthPrime {n : ℕ} (hn : 1 ≤ n) :
>     3 ≤ nthPrime n
> ```

> **Theorem 12. Consecutive prime gaps are even from index one onward.**
>
> **In Lean:**
>
> ```lean
> theorem primeGap_even {n : ℕ} (hn : 1 ≤ n) :
>     ∃ k : ℤ, (primeGap n : ℤ) = 2 * k
> ```

> **Theorem 13. Consecutive prime gaps are at least two from index one onward.**
>
> **In Lean:**
>
> ```lean
> lemma primeGap_ge_two_of_pos_index
>     (n : ℕ) (hn : 1 ≤ n) :
>     2 ≤ primeGap n
> ```

---

## V. Higher-Order Prime Gaps

> **Definition 4. Second-order gap.**
>
> **In Lean:**
>
> ```lean
> def secondOrderGap (p0 p1 p2 : ℕ) : ℤ :=
>   (p2 : ℤ) - 2 * (p1 : ℤ) + (p0 : ℤ)
> ```

> **Theorem 14. Zero second-order gap and arithmetic progression.**
>
> **In Lean:**
>
> ```lean
> theorem secondOrderGap_zero_iff_arithmetic_progression
>     (p0 p1 p2 : ℕ) :
>     secondOrderGap p0 p1 p2 = 0 ↔
>       (p1 : ℤ) - (p0 : ℤ) = (p2 : ℤ) - (p1 : ℤ)
> ```

> **Theorem 15. Evenness of second-order gaps for odd primes.**
>
> **In Lean:**
>
> ```lean
> theorem secondOrderGap_even_of_odd_primes
>     (p0 p1 p2 : ℕ)
>     (hp0 : Nat.Prime p0) (hp0_gt : p0 > 2)
>     (hp1 : Nat.Prime p1) (hp1_gt : p1 > 2)
>     (hp2 : Nat.Prime p2) (hp2_gt : p2 > 2) :
>     ∃ k : ℤ, secondOrderGap p0 p1 p2 = 2 * k
> ```

> **Definition 5. Third-order gap.**
>
> **In Lean:**
>
> ```lean
> def thirdOrderGap (p0 p1 p2 p3 : ℕ) : ℤ :=
>   (p3 : ℤ) - 3 * (p2 : ℤ) + 3 * (p1 : ℤ) - (p0 : ℤ)
> ```

> **Theorem 16. Evenness of third-order gaps for odd primes.**
>
> **In Lean:**
>
> ```lean
> theorem thirdOrderGap_even_of_odd_primes
>     (p0 p1 p2 p3 : ℕ)
>     (hp0 : Nat.Prime p0) (hp0_gt : p0 > 2)
>     (hp1 : Nat.Prime p1) (hp1_gt : p1 > 2)
>     (hp2 : Nat.Prime p2) (hp2_gt : p2 > 2)
>     (hp3 : Nat.Prime p3) (hp3_gt : p3 > 2) :
>     ∃ k : ℤ, thirdOrderGap p0 p1 p2 p3 = 2 * k
> ```

> **Definition 6. Fourth-order gap.**
>
> **In Lean:**
>
> ```lean
> def fourthOrderGap (p0 p1 p2 p3 p4 : ℕ) : ℤ :=
>   (p4 : ℤ) - 4 * (p3 : ℤ) +
>     6 * (p2 : ℤ) - 4 * (p1 : ℤ) + (p0 : ℤ)
> ```

> **Theorem 17. Evenness of fourth-order gaps for odd primes.**
>
> **In Lean:**
>
> ```lean
> theorem fourthOrderGap_even_of_odd_primes
>     (p0 p1 p2 p3 p4 : ℕ)
>     (hp0 : Nat.Prime p0) (hp0_gt : p0 > 2)
>     (hp1 : Nat.Prime p1) (hp1_gt : p1 > 2)
>     (hp2 : Nat.Prime p2) (hp2_gt : p2 > 2)
>     (hp3 : Nat.Prime p3) (hp3_gt : p3 > 2)
>     (hp4 : Nat.Prime p4) (hp4_gt : p4 > 2) :
>     ∃ k : ℤ, fourthOrderGap p0 p1 p2 p3 p4 = 2 * k
> ```

---

## VI. N-th Order Finite Difference

> **Definition 7. N-th order gap.**
>
> **In Lean:**
>
> ```lean
> def nthOrderGap (N : ℕ) (p : ℕ → ℤ) : ℤ :=
>   ∑ k ∈ range (N + 1),
>     (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) * p (N - k)
> ```

> **Theorem 18. Alternating binomial sum.**
>
> **In Lean:**
>
> ```lean
> lemma sum_alternate_choose_eq_zero (N : ℕ) (hN : N > 0) :
>     ∑ k ∈ range (N + 1),
>       (-1 : ℤ) ^ k * (Nat.choose N k : ℤ) = 0
> ```

> **Theorem 19. Universal evenness of positive-order finite differences.**
>
> Any positive-order finite difference of odd primes is even.
>
> **In Lean:**
>
> ```lean
> theorem nthOrderGap_even_of_odd_primes
>     (N : ℕ) (hN : N > 0) (p : ℕ → ℕ)
>     (h_prime : ∀ i, i ≤ N → Nat.Prime (p i))
>     (h_gt_2 : ∀ i, i ≤ N → p i > 2) :
>     ∃ k : ℤ,
>       nthOrderGap N (fun i => (p i : ℤ)) = 2 * k
> ```

---

## VII. Verification

From the repository root:

```text
lake env lean M4TH/PrimeGapsSophie/PrimeGapsSophieLive/PrimeGapsSophie.live.lean
```

For the package library:

```text
lake build PrimeGapsSophie
```

---

## VIII. Axiom Certificate

Run:

```text
echo 'import PrimeGapsSophie
#print axioms PrimeGapsSophie.sophie_germain_mod6_eq_5
#print axioms PrimeGapsSophie.primeGap_even
#print axioms PrimeGapsSophie.secondOrderGap_even_of_odd_primes
#print axioms PrimeGapsSophie.nthOrderGap_even_of_odd_primes' \
  | lake env lean --stdin
```

Expected output:

```text
'PrimeGapsSophie.sophie_germain_mod6_eq_5' depends on axioms: [propext, Quot.sound]
'PrimeGapsSophie.primeGap_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeGapsSophie.secondOrderGap_even_of_odd_primes' depends on axioms: [propext, Quot.sound]
'PrimeGapsSophie.nthOrderGap_even_of_odd_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard foundational dependencies from Mathlib.  The live file
contains no incomplete proof placeholder, no package-local trusted declaration,
and no trusted compiled decision procedure.

