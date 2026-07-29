# PrimeGapsSophie.live

**A single-file live presentation of Sophie Germain primes, ordinary prime-gap
parity, and the parity of higher-order finite differences over the primes,
formalised in Lean 4 over Mathlib.**

\*\*Author:\*\* Bezalel Izquierdo Pérez
\*\*License:\*\* Apache 2.0
\*\*Live file:\*\* `PrimeGapsSophie.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`PrimeGapsSophie.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

A Sophie Germain prime is a prime \(p\) such that \(2p+1\) is also prime.
All primes beyond 2 are odd, so ordinary gaps \(p_{n+1} - p_n\) are even for
\(n \ge 1\).  This package extends the parity observation to finite differences
of arbitrary positive order over odd primes, using the combinatorial identity
for the alternating sum of binomial coefficients.

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

---

## III. Ordinary Prime-Gap Parity

> **Definition 2. Prime gap.**
>
> **In Lean:**
>
> ```lean
> def PrimeGapsSophie.primeGap (n : ℕ) : ℕ :=
>   Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n
> ```

> **Theorem 3. Ordinary prime gaps are even.**
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
>   ∑ i ∈ range (N + 1),
>     (-1 : ℤ) ^ i * ((Nat.choose N i : ℤ) * (p (k + N - i) : ℤ))
> ```

> **Lemma 1. Binomial alternating sum identity.**
>
> $$
> \sum_{i=0}^{N} (-1)^i \binom{N}{i} = 0, \qquad N > 0.
> $$
>
> **In Lean:**
>
> ```lean
> lemma PrimeGapsSophie.sum_alternate_choose_eq_zero
>     (N : ℕ) (hN : N > 0) :
>     ∑ i ∈ range (N + 1), (-1 : ℤ) ^ i * (Nat.choose N i : ℤ) = 0
> ```

> **Theorem 4. Second, third, and fourth order gaps are even.**
>
> **In Lean:**
>
> ```lean
> theorem PrimeGapsSophie.secondOrderGap_even_of_odd_primes ...
> theorem PrimeGapsSophie.thirdOrderGap_even_of_odd_primes ...
> theorem PrimeGapsSophie.fourthOrderGap_even_of_odd_primes ...
> ```

> **Theorem 5. Nth-order gap even for odd primes.**
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

'PrimeGapsSophie.sophie_germain_mod6_eq_5' depends on axioms: [propext, Classical.choice, Quot.sound]

---

## VII. Verification

```text
lake env lean PrimeGapsSophie/PrimeGapsSophieLive/PrimeGapsSophie.live.lean
lake build PrimeGapsSophie
```
