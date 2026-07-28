# DiscreteAbelChebyshev.live

**Author:** Bezalel Izquierdo Pérez  
**License:** Apache 2.0  
**Live file:** `DiscreteAbelChebyshev.live.lean`

---

## I. Mathematical Aim

`DiscreteAbelChebyshev.live.lean` is the single-file reading version of the
`DiscreteAbelChebyshev` package.

The package formalizes a finite Abel summation identity and applies it to a
discrete Chebyshev bridge.  The goal is to transform a weighted von
Mangoldt-type sum into a discrete logarithmic integral term plus explicitly
named error terms.

The central algebraic identity is:

```lean
∑ n ∈ range N, mangoldt n * invLog n =
  (∑ n ∈ range N, invLog n) +
    psi_error N * invLog N -
      ∑ n ∈ range N,
        psi_error (n + 1) * (invLog (n + 1) - invLog n)
```

The final error-transfer theorem is conditional.  The residual sum estimate is
not hidden as a trusted declaration; it is exposed as:

```lean
def ChebyshevErrorSumBound (C : ℝ) (N₀ : ℕ) : Prop
```

Thus the package proves the discrete bridge from explicit hypotheses, without
claiming an unconditional prime number theorem.

---

## II. Source Architecture

The live file is a faithful fusion of the public package modules:

```text
DiscreteAbelChebyshev/Basic.lean
DiscreteAbelChebyshev/ChebyshevBridge.lean
```

The namespace is:

```lean
namespace DiscreteAbelChebyshev
```

The live file imports only Mathlib modules.  It does not import the local
package modules, because the source content is present directly in the file.

---

## III. Partial Sums and Abel Summation

> **Definition 1. Partial sums.**
>
> For a real sequence `a`, `sumSeq a n` is the finite sum over `range n`.
>
> **In Lean:**
>
> ```lean
> noncomputable def sumSeq (a : ℕ → ℝ) (n : ℕ) : ℝ :=
>   ∑ i ∈ range n, a i
> ```

> **Theorem 1. Zero partial sum.**
>
> **In Lean:**
>
> ```lean
> @[simp] lemma sumSeq_zero (a : ℕ → ℝ) : sumSeq a 0 = 0
> ```

> **Theorem 2. Successor partial sum.**
>
> **In Lean:**
>
> ```lean
> lemma sumSeq_succ (a : ℕ → ℝ) (n : ℕ) :
>     sumSeq a (n + 1) = sumSeq a n + a n
> ```

> **Theorem 3. Difference recovery.**
>
> **In Lean:**
>
> ```lean
> lemma sumSeq_sub_succ (a : ℕ → ℝ) (n : ℕ) :
>     sumSeq a (n + 1) - sumSeq a n = a n
> ```

> **Theorem 4. Shift over `range N`.**
>
> **In Lean:**
>
> ```lean
> lemma sum_range_add_one (g : ℕ → ℝ) (N : ℕ) :
>     ∑ n ∈ range N, g (n + 1) =
>       ((∑ k ∈ range (N + 1), g k) - g 0)
> ```

> **Theorem 5. Shifted partial-sum telescoping.**
>
> **In Lean:**
>
> ```lean
> lemma sum_sumSeq_mul_shift (a f : ℕ → ℝ) (N : ℕ) :
>     ∑ n ∈ range N, sumSeq a (n + 1) * f (n + 1) =
>       sumSeq a N * f N + ∑ n ∈ range N, sumSeq a n * f n
> ```

> **Theorem 6. Finite Abel summation.**
>
> This is the core exact identity of the package.
>
> **In Lean:**
>
> ```lean
> lemma abel_summation (a f : ℕ → ℝ) (N : ℕ) :
>     ∑ n ∈ range N, a n * f n =
>       sumSeq a N * f N -
>         ∑ n ∈ range N,
>           sumSeq a (n + 1) * (f (n + 1) - f n)
> ```

---

## IV. Chebyshev Objects and Reciprocal Log Weight

> **Definition 2. Von Mangoldt-type sequence.**
>
> **In Lean:**
>
> ```lean
> noncomputable def mangoldt (n : ℕ) : ℝ :=
>   if IsPrimePow n then Real.log (Nat.minFac n) else 0
> ```

> **Definition 3. Discrete Chebyshev function.**
>
> **In Lean:**
>
> ```lean
> noncomputable def psi (N : ℕ) : ℝ :=
>   sumSeq mangoldt N
> ```

> **Definition 4. Safe reciprocal logarithm.**
>
> The cases `0` and `1` are sent to zero to avoid the singularity of
> `1 / log n`.
>
> **In Lean:**
>
> ```lean
> noncomputable def invLog (n : ℕ) : ℝ :=
>   if n ≥ 2 then 1 / Real.log (n : ℝ) else 0
> ```

> **Definition 5. Constant one sequence.**
>
> **In Lean:**
>
> ```lean
> noncomputable def seqOne (_n : ℕ) : ℝ :=
>   1
> ```

> **Theorem 7. Partial sum of the one sequence.**
>
> **In Lean:**
>
> ```lean
> @[simp] lemma sumSeq_one (N : ℕ) :
>     sumSeq seqOne N = (N : ℝ)
> ```

---

## V. Exact Chebyshev Bridge

> **Theorem 8. Abel identity for the weighted Mangoldt sum.**
>
> **In Lean:**
>
> ```lean
> lemma pi_approx_eq_abel (N : ℕ) :
>     ∑ n ∈ range N, mangoldt n * invLog n =
>       psi N * invLog N -
>         ∑ n ∈ range N,
>           psi (n + 1) * (invLog (n + 1) - invLog n)
> ```

> **Definition 6. Chebyshev error.**
>
> **In Lean:**
>
> ```lean
> noncomputable def psi_error (n : ℕ) : ℝ :=
>   psi n - n
> ```

> **Theorem 9. Splitting the Abel correction.**
>
> **In Lean:**
>
> ```lean
> lemma abel_psi_split (N : ℕ) :
>     ∑ n ∈ range N,
>       psi (n + 1) * (invLog (n + 1) - invLog n) =
>       (∑ n ∈ range N,
>         (n + 1 : ℝ) * (invLog (n + 1) - invLog n)) +
>       (∑ n ∈ range N,
>         psi_error (n + 1) * (invLog (n + 1) - invLog n))
> ```

> **Theorem 10. Main-term collapse.**
>
> Applying Abel summation to the constant sequence gives the discrete
> logarithmic integral term.
>
> **In Lean:**
>
> ```lean
> lemma main_term_collapse (N : ℕ) :
>     ∑ n ∈ range N,
>       (n + 1 : ℝ) * (invLog (n + 1) - invLog n) =
>       (N : ℝ) * invLog N - ∑ n ∈ range N, invLog n
> ```

> **Theorem 11. Final exact approximation identity.**
>
> **In Lean:**
>
> ```lean
> lemma pi_approx_final (N : ℕ) :
>     ∑ n ∈ range N, mangoldt n * invLog n =
>       (∑ n ∈ range N, invLog n) +
>         psi_error N * invLog N -
>           ∑ n ∈ range N,
>             psi_error (n + 1) *
>               (invLog (n + 1) - invLog n)
> ```

---

## VI. Conditional Error Frontier

> **Definition 7. Chebyshev error bound.**
>
> **In Lean:**
>
> ```lean
> def IsChebyshevBounded (C : ℝ) (N₀ : ℕ) : Prop :=
>   ∀ N ≥ N₀,
>     |psi_error N| ≤
>       C * Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2
> ```

> **Definition 8. Residual error-sum frontier.**
>
> This is the remaining discrete analytic estimate.  It is a named hypothesis,
> not a hidden trusted declaration.
>
> **In Lean:**
>
> ```lean
> def ChebyshevErrorSumBound (C : ℝ) (N₀ : ℕ) : Prop :=
>   ∀ N, N ≥ max N₀ 2 →
>     |∑ n ∈ range N,
>       psi_error (n + 1) *
>         (invLog (n + 1) - invLog n)| ≤
>       C * 2 * Real.sqrt (N : ℝ)
> ```

> **Theorem 12. Endpoint error bound.**
>
> **In Lean:**
>
> ```lean
> lemma bound_error_eval
>     (C : ℝ) (N₀ : ℕ) (_hC : 0 ≤ C)
>     (h_bound : IsChebyshevBounded C N₀)
>     (N : ℕ) (hN : N ≥ max N₀ 2) :
>     |psi_error N * invLog N| ≤
>       C * Real.sqrt (N : ℝ) * Real.log (N : ℝ)
> ```

---

## VII. Reciprocal-Log Calculus

> **Theorem 13. Derivative of reciprocal logarithm.**
>
> **In Lean:**
>
> ```lean
> lemma deriv_invLog (x : ℝ) (hx : 1 < x) :
>     deriv (fun t => (Real.log t)⁻¹) x =
>       - (x * (Real.log x) ^ 2)⁻¹
> ```

> **Theorem 14. Continuity on each interval `[n,n+1]`.**
>
> **In Lean:**
>
> ```lean
> lemma invLog_continuousOn (n : ℕ) (hn : n ≥ 2) :
>     ContinuousOn (fun t => (Real.log t)⁻¹)
>       (Set.Icc (n : ℝ) (n + 1 : ℝ))
> ```

> **Theorem 15. Differentiability on each interval `(n,n+1)`.**
>
> **In Lean:**
>
> ```lean
> lemma invLog_differentiableOn (n : ℕ) (hn : n ≥ 2) :
>     DifferentiableOn ℝ (fun t => (Real.log t)⁻¹)
>       (Set.Ioo (n : ℝ) (n + 1 : ℝ))
> ```

> **Theorem 16. Discrete reciprocal-log difference bound.**
>
> **In Lean:**
>
> ```lean
> lemma invLog_diff_bound (n : ℕ) (hn : n ≥ 2) :
>     |invLog (n + 1) - invLog n| ≤
>       (1 : ℝ) / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)
> ```

---

## VIII. Final Transfer Theorem

> **Theorem 17. Conditional Chebyshev-to-prime error transfer.**
>
> Under the Chebyshev bound and the residual error-sum frontier, the weighted
> prime-counting error is controlled by the expected endpoint and residual
> terms.
>
> **In Lean:**
>
> ```lean
> theorem chebyshev_implies_prime_error
>     (C : ℝ) (N₀ : ℕ) (hC : 0 ≤ C)
>     (h_bound : IsChebyshevBounded C N₀)
>     (h_sum : ChebyshevErrorSumBound C N₀)
>     (N : ℕ) (hN : N ≥ max N₀ 2) :
>     |∑ n ∈ range N, mangoldt n * invLog n -
>       ∑ n ∈ range N, invLog n| ≤
>       C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) +
>         C * 2 * Real.sqrt (N : ℝ)
> ```

This theorem is the final statement of the live file.  It is deliberately
conditional: the file proves the discrete algebraic bridge and exposes the
analytic frontier needed to close the estimate.

---

## IX. Verification

From the repository root:

```text
lake env lean DiscreteAbelChebyshev/DiscreteAbelChebyshevLive/DiscreteAbelChebyshev.live.lean
```

For the package library:

```text
lake build DiscreteAbelChebyshev
```

---

## X. Axiom Certificate

Run:

```text
echo 'import DiscreteAbelChebyshev
#print axioms DiscreteAbelChebyshev.abel_summation
#print axioms DiscreteAbelChebyshev.pi_approx_final
#print axioms DiscreteAbelChebyshev.invLog_diff_bound
#print axioms DiscreteAbelChebyshev.chebyshev_implies_prime_error' \
  | lake env lean --stdin
```

Expected output:

```text
'DiscreteAbelChebyshev.abel_summation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DiscreteAbelChebyshev.pi_approx_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'DiscreteAbelChebyshev.invLog_diff_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DiscreteAbelChebyshev.chebyshev_implies_prime_error' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard foundational dependencies from Mathlib.  The live file
contains no incomplete proof placeholder, no package-local trusted declaration,
and no trusted compiled decision procedure.

