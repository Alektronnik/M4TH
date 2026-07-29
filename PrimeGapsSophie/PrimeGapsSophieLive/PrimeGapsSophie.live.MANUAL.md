# PrimeGapsSophie

**A single-file live presentation of Sophie Germain primes, ordinary prime-gap
parity, and the parity of higher-order finite differences over the primes,
formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Perez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0
- Companion file: `PrimeGapsSophie.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`PrimeGapsSophie.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

A Sophie Germain prime is a prime \(p\) such that \(2p+1\) is also prime.
These primes satisfy strong congruence conditions and are connected to the
parity theory of prime gaps.

The ordinary gap between consecutive primes \(p_{n+1} - p_n\) is always even
for \(n \ge 1\) (all primes beyond 2 are odd).  This package extends that
observation: all finite differences of arbitrary positive order over odd
primes are even.  The proof uses the combinatorial identity for the nth-order
forward difference.

---

## II. Sophie Germain Primes

> **Definition 1. Sophie Germain prime.**
>
> **In Lean:**
>
> ```lean
> def PrimeGapsSophie.IsSophieGermainPrime (p : ℕ) : Prop :=
>   Nat.Prime p ∧ Nat.Prime (2 * p + 1)
> ```

> **Theorem 1. Modulo 3 exclusion.**
>
> If \(p > 3\) is a Sophie Germain prime, then \(p \equiv 2 \pmod{3}\).
>
> **In Lean:**
>
> ```lean
> theorem PrimeGapsSophie.sophie_germain_mod3_eq_2
>     {p : ℕ} (hp : IsSophieGermainPrime p) (hp3 : 3 < p) :
>     p % 3 = 2
> ```

> **Theorem 2. Modulo 6 congruence.**
>
> For \(p \ge 5\), Sophie Germain primes satisfy \(p \equiv 5 \pmod{6}\).
>
> **In Lean:**
>
> ```lean
> theorem PrimeGapsSophie.sophie_germain_mod6_eq_5
>     {p : ℕ} (hp : IsSophieGermainPrime p) (hp5 : 5 ≤ p) :
>     p % 6 = 5
> ```

> **Lemma 1. Prime index exclusion.**
>
> **In Lean:**
>
> ```lean
> theorem PrimeGapsSophie.prime_index_mod3_exclusion
>     (n : ℕ) (hn : 2 ≤ n) : ...
> ```

---

## III. Ordinary Prime-Gap Parity

> **Definition 2. Prime gap.**
>
> $$g_n = p_{n+1} - p_n.$$
>
> **In Lean:**
>
> ```lean
> def PrimeGapsSophie.primeGap (n : ℕ) : ℕ :=
>   Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n
> ```

> **Theorem 3. Ordinary prime gaps are even.**
>
> For \(n \ge 1\), the gap between consecutive primes is even.
>
> **In Lean:**
>
> ```lean
> theorem PrimeGapsSophie.primeGap_even {n : ℕ} (hn : 1 ≤ n) :
>     Even (primeGap n)
> ```

---

## IV. Higher-Order Gap Parity

> **Definition 3. Nth-order forward difference.**
>
> $$
> \Delta^N p_k = \sum_{i=0}^{N} (-1)^i \binom{N}{i} p_{k+N-i}.
> $$
>
> **In Lean:**
>
> ```lean
> def PrimeGapsSophie.nthOrderGap (N : ℕ) (p : ℕ → ℕ) (k : ℕ) : ℤ :=
>   ∑ i ∈ range (N + 1), (-1 : ℤ) ^ i * ((Nat.choose N i : ℤ) * (p (k + N - i) : ℤ))
> ```

> **Theorem 4. Second-order gap even for odd primes.**
>
> **In Lean:**
>
> ```lean
> theorem PrimeGapsSophie.secondOrderGap_even_of_odd_primes
>     (p0 p1 p2 : ℕ) (hp0 : Nat.Prime p0) (hp1 : Nat.Prime p1)
>     (hp2 : Nat.Prime p2) (hp0_odd : 2 < p0) (hp1_odd : 2 < p1)
>     (hp2_odd : 2 < p2) : Even (secondOrderGap p0 p1 p2)
> ```

> **Theorem 5. Third and fourth order gaps are even.**
>
> **In Lean:**
>
> ```lean
> theorem PrimeGapsSophie.thirdOrderGap_even_of_odd_primes ...
> theorem PrimeGapsSophie.fourthOrderGap_even_of_odd_primes ...
> ```

> **Theorem 6. Nth-order gap even for odd primes.**
>
> For any positive order \(N\), the nth-order finite difference of odd
> primes is even.
>
> **In Lean:**
>
> ```lean
> theorem PrimeGapsSophie.nthOrderGap_even_of_odd_primes
>     (N : ℕ) (hN : N > 0) (p : ℕ → ℕ)
>     (h_prime : ∀ i, i ≤ N → Nat.Prime (p i))
>     (h_odd : ∀ i, i ≤ N → 2 < p i) :
>     Even (nthOrderGap N p 0)
> ```

> **Lemma 2. Binomial alternating sum identity.**
>
> $$
> \sum_{i=0}^{N} (-1)^i \binom{N}{i} = 0, \qquad N > 0.
> $$
>
> **In Lean:**
>
> ```lean
> lemma PrimeGapsSophie.alternating_binomial_sum_zero (N : ℕ) (hN : N > 0) :
>     ∑ i ∈ range (N + 1), (-1 : ℤ) ^ i * (Nat.choose N i : ℤ) = 0
> ```

---

## V. Architecture

```text
SophieGermain -> PrimeGap -> HigherOrder
```

- `SophieGermain` -- definition, modular congruences
- `PrimeGap` -- ordinary gaps, parity
- `HigherOrder` -- nth-order differences, general parity theorem

---

## VI. Axiom Certificate

```text
printf 'import PrimeGapsSophie
#print axioms PrimeGapsSophie.sophie_germain_mod6_eq_5
#print axioms PrimeGapsSophie.nthOrderGap_even_of_odd_primes
' | lake env lean --stdin
```

Expected: `[propext, Classical.choice, Quot.sound]`

---

## VII. Verification

```text
lake env lean PrimeGapsSophie/PrimeGapsSophieLive/PrimeGapsSophie.live.lean
lake build PrimeGapsSophie
```
