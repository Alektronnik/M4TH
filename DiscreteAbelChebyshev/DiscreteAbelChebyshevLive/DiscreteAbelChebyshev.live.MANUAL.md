# DiscreteAbelChebyshev

**A single-file live presentation of discrete Abel summation and the typed
Chebyshev-to-prime-counting bridge, formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Perez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0
- Companion file: `DiscreteAbelChebyshev.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`DiscreteAbelChebyshev.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

Summation by parts (Abel summation) is the discrete analogue of integration by
parts.  For sequences \(a_n, f_n\),

$$
\sum_{n=1}^{N} a_n f_n = A_N f_N - \sum_{n=1}^{N-1} A_n (f_{n+1} - f_n),
\qquad A_n = \sum_{k=1}^{n} a_k.
$$

The package proves this identity and applies it to the Chebyshev-to-prime
bridge: with \(a_n = \Lambda(n)\) (the von Mangoldt weight) and
\(f_n = 1/\log n\), the weighted prime sum decomposes into a main term,
a boundary term, and a residual error term.  The residual estimate is exposed
as the typed hypothesis `ChebyshevErrorSumBound`.

---

## II. Discrete Abel Summation

> **Definition 1. Partial sums.**
>
> **In Lean:**
>
> ```lean
> noncomputable def DiscreteAbelChebyshev.sumSeq (a : ℕ → ℝ) (n : ℕ) : ℝ :=
>   ∑ i ∈ range n, a i
> ```

> **Theorem 1. Finite Abel summation identity.**
>
> $$
> \sum_{n \in [0,N)} a_n f_n = A_N f_N - \sum_{n \in [0,N)} A_{n+1} (f_{n+1} - f_n).
> $$
>
> **In Lean:**
>
> ```lean
> lemma DiscreteAbelChebyshev.abel_summation (a f : ℕ → ℝ) (N : ℕ) :
>     ∑ n ∈ range N, a n * f n =
>       sumSeq a N * f N -
>         ∑ n ∈ range N, sumSeq a (n + 1) * (f (n + 1) - f n)
> ```

> **Definition 2. Mangoldt weight and Chebyshev psi.**
>
> **In Lean:**
>
> ```lean
> noncomputable def DiscreteAbelChebyshev.mangoldt (n : ℕ) : ℝ :=
>   if IsPrimePow n then Real.log (Nat.minFac n) else 0
>
> noncomputable def DiscreteAbelChebyshev.psi (N : ℕ) : ℝ :=
>   sumSeq mangoldt N
> ```

> **Definition 3. Reciprocal logarithm weight.**
>
> **In Lean:**
>
> ```lean
> noncomputable def DiscreteAbelChebyshev.invLog (n : ℕ) : ℝ :=
>   if n ≥ 2 then 1 / Real.log (n : ℝ) else 0
> ```

---

## III. Exact Decomposition

> **Theorem 2. Exact Abel decomposition of the weighted Mangoldt sum.**
>
> **In Lean:**
>
> ```lean
> lemma DiscreteAbelChebyshev.pi_approx_final (N : ℕ) :
>     ∑ n ∈ range N, mangoldt n * invLog n =
>       (∑ n ∈ range N, invLog n) +
>         psi_error N * invLog N -
>           ∑ n ∈ range N, psi_error (n + 1) * (invLog (n + 1) - invLog n)
> ```

> **Lemma 1. Reciprocal-logarithm difference bound.**
>
> $$
> \left|\frac{1}{\log(n+1)} - \frac{1}{\log n}\right|
>   \le \frac{1}{n (\log n)^2}, \qquad n \ge 2.
> $$
>
> **In Lean:**
>
> ```lean
> lemma DiscreteAbelChebyshev.invLog_diff_bound (n : ℕ) (hn : n ≥ 2) :
>     |invLog (n + 1) - invLog n| ≤
>       (1 : ℝ) / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)
> ```

---

## IV. The Typed Chebyshev Frontier

> **Definition 4. Chebyshev error bound and residual sum hypotheses.**
>
> **In Lean:**
>
> ```lean
> def DiscreteAbelChebyshev.IsChebyshevBounded (C : ℝ) (N₀ : ℕ) : Prop :=
>   ∀ N ≥ N₀, |psi_error N| ≤ C * Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2
>
> def DiscreteAbelChebyshev.ChebyshevErrorSumBound (C : ℝ) (N₀ : ℕ) : Prop :=
>   ∀ N, N ≥ max N₀ 2 →
>     |∑ n ∈ range N, psi_error (n + 1) * (invLog (n + 1) - invLog n)| ≤
>       C * 2 * Real.sqrt (N : ℝ)
> ```

> **Theorem 3. Chebyshev implies prime error.**
>
> Under the two typed hypotheses, the weighted prime sum is close to the
> harmonic sum of reciprocal logarithms.
>
> **In Lean:**
>
> ```lean
> theorem DiscreteAbelChebyshev.chebyshev_implies_prime_error
>     (C : ℝ) (N₀ : ℕ) (hC : 0 ≤ C)
>     (h_bound : IsChebyshevBounded C N₀)
>     (h_sum : ChebyshevErrorSumBound C N₀)
>     (N : ℕ) (hN : N ≥ max N₀ 2) :
>     |∑ n ∈ range N, mangoldt n * invLog n - ∑ n ∈ range N, invLog n| ≤ ...
> ```

---

## V. Architecture

```text
Basic -> ChebyshevBridge
```

- `Basic` -- partial sums, Abel identity, Mangoldt/psi/invLog definitions
- `ChebyshevBridge` -- exact decomposition, reciprocal-log bound, conditional theorem

---

## VI. Axiom Certificate

```text
printf 'import DiscreteAbelChebyshev
#print axioms DiscreteAbelChebyshev.abel_summation
#print axioms DiscreteAbelChebyshev.chebyshev_implies_prime_error
' | lake env lean --stdin
```

Expected: `[propext, Classical.choice, Quot.sound]`

---

## VII. Verification

```text
lake env lean DiscreteAbelChebyshev/DiscreteAbelChebyshevLive/DiscreteAbelChebyshev.live.lean
lake build DiscreteAbelChebyshev
```
