# MertensPNT.live

**A single-file live presentation of Mertens reciprocal-prime infrastructure,
Euler products, certified finite data, and a conditional PNT+ frontier,
formalised in Lean 4 over Mathlib.**

**Author:** Bezalel Izquierdo Pérez
**License:** Apache 2.0
**Live file:** `MertensPNT.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`MertensPNT.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

Mertens' theorems connect three fundamental objects:

$$
\sum_{p \leq n} \frac{1}{p},
\qquad
\prod_{p \leq n}\left(1-\frac{1}{p}\right),
\qquad
\log\log n.
$$

The package formalizes a certified layer around these objects:

- reciprocal-prime partial sums;
- Euler products over primes;
- elementary Erdős divergence infrastructure;
- the Meissel-Mertens correction series;
- compensated Euler-product convergence;
- explicit Erdős block subsequences;
- kernel-checked numerical tables;
- residual functions measuring the PNT+ boundary;
- a conditional closure theorem from Mertens' second theorem to the Euler
  product asymptotic.

The central analytic picture is:

```text
partialSum n
    |
    |        log log n + M
    |       /
    |______/____________________ n

partialProduct n * exp(partialSum n)
    |
    |-----> exp(M)
```

The package does not claim an unconditional Prime Number Theorem beyond the
formal hypotheses explicitly stated in the Lean file.

---

## II. Reciprocal-Prime Core

> **Definition 1. Coercion of primes to real numbers.**
>
> **In Lean:**
>
> ```lean
> def ErdosReciprocals.primeR (p : Nat.Primes) : ℝ :=
>   (p.val : ℝ)
> ```

> **Definition 2. Prime reciprocal term.**
>
> The function is \(1/n\) on primes and \(0\) on composites.
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.primeReciprocalTerm :
>     ℕ → ℝ :=
>   Set.indicator {p | Nat.Prime p} (fun p => (1 : ℝ) / p)
> ```

> **Definition 3. Partial sum of reciprocal primes.**
>
> $$
> S(n)=\sum_{p \leq n}\frac{1}{p}.
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.partialSum
>     (n : ℕ) : ℝ :=
>   ∑ k ∈ Finset.range (n + 1), primeReciprocalTerm k
> ```

> **Definition 4. Log-weighted reciprocal-prime sum.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.partialLogSum
>     (n : ℕ) : ℝ :=
>   ((n + 1).primesBelow).sum (fun p => Real.log p / p)
> ```

> **Definition 5. Euler product over primes.**
>
> $$
> P(n)=\prod_{p\leq n}\left(1-\frac{1}{p}\right).
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.partialProduct
>     (n : ℕ) : ℝ :=
>   ((n + 1).primesBelow).prod
>     (fun p => (1 - (1 : ℝ) / p))
> ```

> **Theorem 1. Prime-sum form of `partialSum`.**
>
> **In Lean:**
>
> ```lean
> lemma ErdosReciprocals.partialSum_eq_primesBelow_sum
>     (n : ℕ) :
>     partialSum n =
>       ((n + 1).primesBelow).sum (fun p => (1 : ℝ) / p)
> ```

> **Theorem 2. Monotonicity of the reciprocal-prime sum.**
>
> **In Lean:**
>
> ```lean
> lemma ErdosReciprocals.partialSum_mono
>     {m n : ℕ} (hmn : m ≤ n) :
>     partialSum m ≤ partialSum n
> ```

> **Theorem 3. Positivity of the Euler product.**
>
> **In Lean:**
>
> ```lean
> lemma ErdosReciprocals.partialProduct_pos
>     {n : ℕ} (hn : 2 ≤ n) :
>     0 < partialProduct n
> ```

> **Theorem 4. Logarithm of the Euler product.**
>
> **In Lean:**
>
> ```lean
> lemma ErdosReciprocals.log_partialProduct_eq_sum
>     (n : ℕ) :
>     Real.log (partialProduct n) =
>       ((n + 1).primesBelow).sum
>         (fun p => Real.log (1 - (1 : ℝ) / p))
> ```

---

## III. Elementary Erdős Layer

> **Theorem 5. Divergence of reciprocal primes.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.erdos_not_summable_primes :
>     ¬ Summable (fun p : Nat.Primes => (1 / p : ℝ))
> ```

> **Theorem 6. The partial sums tend to infinity.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.tendsto_partialSum_atTop :
>     Tendsto partialSum atTop atTop
> ```

> **Theorem 7. Arbitrarily large reciprocal-prime sums.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.exists_partialSum_gt
>     (M : ℝ) :
>     ∃ n, partialSum n > M
> ```

> **Theorem 8. Infinitely many primes.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.infinite_primes_of_divergent_reciprocals :
>     Set.Infinite {p : ℕ | Nat.Prime p}
> ```

> **Theorem 9. Existence of primes beyond any bound.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.exists_prime_gt
>     (n : ℕ) :
>     ∃ p, Nat.Prime p ∧ n < p
> ```

The package also contains Chebyshev bridges linking `partialLogSum`,
prime-counting, and reciprocal-prime sums.

---

## IV. Meissel-Mertens Constant Layer

> **Definition 6. The prime correction term.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.mertensPrimeCorrection
>     (p : Nat.Primes) : ℝ :=
>   Real.log (1 - 1 / primeR p) + 1 / primeR p
> ```

> **Theorem 10. Summability of the correction series.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.summable_mertensPrimeCorrection :
>     Summable mertensPrimeCorrection
> ```

> **Definition 7. The correction sum.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.mertensPrimeCorrectionSum : ℝ
> ```

> **Definition 8. The Mertens constant.**
>
> The package defines
>
> $$
> M = \gamma + \sum_p
> \left(\log(1-\frac1p)+\frac1p\right).
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.mertensConstant : ℝ :=
>   eulerMascheroniConstant + mertensPrimeCorrectionSum
> ```

> **Theorem 11. Constant decomposition.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.mertensConstant_eq_gamma_add_correctionSum :
>     mertensConstant =
>       eulerMascheroniConstant + mertensPrimeCorrectionSum
> ```

> **Definition 9. Numerical approximation used by the certified data layer.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.mertensConstantApprox : ℝ :=
>   0.26149721284478386
> ```

---

## V. Erdős Blocks

> **Definition 10. Erdős block endpoint.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.erdosBlockEnd
>     (k : ℕ) : ℕ :=
>   4 ^ (k + 1)
> ```

> **Theorem 12. Mass of an Erdős block.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.erdos_block_mass
>     (k : ℕ) :
>     1 / 2 ≤
>       partialSum (erdosBlockEnd k) - partialSum k
> ```

> **Definition 11. Iterated Erdős subsequence.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.erdosIter : ℕ → ℕ
> ```

> **Theorem 13. Linear lower bound along the Erdős subsequence.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.partialSum_erdosIter_ge_half_mul
>     (t : ℕ) :
>     (t : ℝ) / 2 ≤ partialSum (erdosIter t)
> ```

> **Theorem 14. The Erdős subsequence tends to infinity.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.tendsto_erdosIter_atTop :
>     Tendsto erdosIter atTop atTop
> ```

This layer is the elementary-growth spine used later to organize subsequence
and product convergence statements.

---

## VI. Euler Product Bridge

> **Definition 12. Partial Mertens correction.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.partialMertensCorrection
>     (n : ℕ) : ℝ :=
>   ((n + 1).primesBelow).sum
>     (fun p => Real.log (1 - (1 : ℝ) / p) + 1 / p)
> ```

> **Theorem 15. Finite correction identity.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.log_partialProduct_add_partialSum_eq_partialMertensCorrection
>     (n : ℕ) :
>     Real.log (partialProduct n) + partialSum n =
>       partialMertensCorrection n
> ```

> **Theorem 16. Convergence of the correction.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.partialMertensCorrection_tendsto_atTop :
>     Tendsto partialMertensCorrection atTop
>       (𝓝 mertensPrimeCorrectionSum)
> ```

> **Theorem 17. Compensated product convergence.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.tendsto_partialProduct_mul_exp_partialSum :
>     Tendsto
>       (fun n => partialProduct n * Real.exp (partialSum n))
>       atTop
>       (𝓝 (Real.exp mertensPrimeCorrectionSum))
> ```

> **Theorem 18. The Euler product tends to zero.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.partialProduct_tendsto_zero :
>     Tendsto partialProduct atTop (𝓝 0)
> ```

> **Theorem 19. Mertens product convergence.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.mertens_product_convergence :
>     Tendsto
>       (fun n => partialProduct n * Real.exp (partialSum n))
>       atTop
>       (𝓝 (Real.exp (mertensConstant - eulerMascheroniConstant)))
> ```

> **Theorem 20. Gamma-normalized compensated limit.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.tendsto_partialProduct_mul_exp_partialSum_add_gamma :
>     Tendsto
>       (fun n =>
>         partialProduct n *
>           Real.exp (partialSum n + eulerMascheroniConstant))
>       atTop
>       (𝓝 (Real.exp mertensConstant))
> ```

---

## VII. Certified Computational Data

The package includes a finite certified data layer.  These constants do not
replace the analytic theorems.  They provide kernel-checked numerical data
points for primorial products, wheel sieves, and sieve checkpoints.

> **Definition 13. Residual proxy.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.taoResidualProxy
>     (sumMinusLogLog : ℝ) : ℝ :=
>   sumMinusLogLog - mertensConstantApprox
> ```

> **Theorem 21. Primorial product certificates.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.primorial_euler_product_30 :
>     (1 - (1 : ℝ) / 2) *
>       (1 - (1 : ℝ) / 3) *
>       (1 - (1 : ℝ) / 5) =
>       (4 : ℝ) / 15
> ```

> **Definition 14. Wheel data.**
>
> **In Lean:**
>
> ```lean
> def ErdosReciprocals.taoWheel30_modulus : ℕ := 30
> def ErdosReciprocals.taoWheel30_phi : ℕ := 8
> def ErdosReciprocals.taoWheel30_coprimeResidues : List ℕ
> ```

> **Theorem 22. Wheel residue count.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.taoWheel30_residue_count_eq_phi :
>     taoWheel30_coprimeResidues.length = taoWheel30_phi
> ```

> **Definition 15. Sieve checkpoint data.**
>
> The data layer stores values such as:
>
> **In Lean:**
>
> ```lean
> def ErdosReciprocals.cribaCp100000000000_n : ℕ :=
>   100000000000
> noncomputable def ErdosReciprocals.cribaCp100000000000_S : ℝ :=
>   3.4934250719082645
> noncomputable def ErdosReciprocals.cribaCp100000000000_delta : ℝ :=
>   1.4101715395398173e-07
> ```

> **Theorem 23. Empirical tightening of the checkpoint delta.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.criba_delta_tightens_1e3_to_1e11 :
>     cribaCp100000000000_delta < cribaCp1000_delta
> ```

The finite data layer is deliberately separated from the general analytic
claims.  Its role is certification, not theorem substitution.

---

## VIII. Connections and Residuals

> **Theorem 24. Partial sums along the Erdős subsequence.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.tendsto_partialSum_comp_erdosIter :
>     Tendsto (fun t => partialSum (erdosIter t)) atTop atTop
> ```

> **Theorem 25. Product convergence along the Erdős subsequence.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.tendsto_partialProduct_mul_exp_partialSum_comp_erdosIter :
>     Tendsto
>       (fun t =>
>         partialProduct (erdosIter t) *
>           Real.exp (partialSum (erdosIter t)))
>       atTop
>       (𝓝 (Real.exp mertensPrimeCorrectionSum))
> ```

> **Definition 16. Mertens approximation.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.mertensApprox
>     (n : ℕ) : ℝ :=
>   Real.log (Real.log n) + mertensConstant
> ```

> **Definition 17. Mertens residual.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.mertensResidual
>     (n : ℕ) : ℝ :=
>   partialSum n - mertensApprox n
> ```

> **Definition 18. Scaled residual.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.mertensScaledResidual
>     (n : ℕ) : ℝ :=
>   Real.log n * mertensResidual n
> ```

> **Definition 19. Scaled Euler product.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ErdosReciprocals.partialEulerProductScaled
>     (n : ℕ) : ℝ :=
>   partialProduct n * Real.log n
> ```

> **Theorem 26. Residual identity.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.mertensResidual_eq_partialSum_sub_loglog_sub_mertensConstant
>     (n : ℕ) :
>     mertensResidual n =
>       partialSum n - Real.log (Real.log n) - mertensConstant
> ```

This layer prepares the conditional statements in the PNT+ frontier.

---

## IX. Conditional PNT+ Frontier

> **Definition 20. Mertens' second theorem as a proposition.**
>
> **In Lean:**
>
> ```lean
> def ErdosReciprocals.MertensSecondTheorem : Prop :=
>   Tendsto
>     (fun n => partialSum n - Real.log (Real.log n))
>     atTop
>     (𝓝 mertensConstant)
> ```

> **Definition 21. Vanishing residual.**
>
> **In Lean:**
>
> ```lean
> def ErdosReciprocals.MertensResidualVanishes : Prop :=
>   Tendsto mertensResidual atTop (𝓝 0)
> ```

> **Definition 22. \(O(1/\log n)\) residual control.**
>
> **In Lean:**
>
> ```lean
> def ErdosReciprocals.MertensResidualBigOInvLog
>     (C : ℝ) : Prop :=
>   ∀ᶠ n in atTop, |mertensResidual n| ≤ C / Real.log n
> ```

> **Theorem 27. Mertens' second theorem is equivalent to residual vanishing.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.mertens_second_theorem_iff_residual_vanishes :
>     MertensSecondTheorem ↔ MertensResidualVanishes
> ```

> **Theorem 28. Residual vanishing gives the scaled Euler-product limit.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.tendsto_partialEulerProductScaled_exp_neg_gamma_of_residual_vanishes
>     (h : MertensResidualVanishes) :
>     Tendsto partialEulerProductScaled atTop
>       (𝓝 (Real.exp (-eulerMascheroniConstant)))
> ```

> **Theorem 29. Conditional Euler-product closure.**
>
> **In Lean:**
>
> ```lean
> theorem ErdosReciprocals.mertens_euler_closure_conditional
>     (h : MertensSecondTheorem) :
>     Tendsto partialEulerProductScaled atTop
>       (𝓝 (Real.exp (-eulerMascheroniConstant)))
> ```

This final theorem is explicitly conditional.  The package does not hide the
PNT+ hypothesis.

---

## X. Architecture

The live file is fused in dependency order:

```text
Basic
  -> MertensConstant
    -> ErdosBlocks
      -> MertensBridge
        -> TTAOData
          -> Connections
            -> PNTFrontier
```

The package separates seven layers:

- reciprocal-prime definitions and elementary inequalities;
- Meissel-Mertens correction series;
- Erdős block growth infrastructure;
- Euler-product compensation;
- certified computational tables;
- residual and subsequence connections;
- conditional PNT+ closure.

The shortest mathematical spine is:

```text
partialSum n = sum_{p <= n} 1/p
partialProduct n = product_{p <= n} (1 - 1/p)
partialSum n -> infinity
partialMertensCorrection n -> correctionSum
partialProduct n * exp(partialSum n) -> exp(correctionSum)
M = gamma + correctionSum
MertensSecondTheorem <-> mertensResidual -> 0
MertensSecondTheorem -> partialProduct n * log n -> exp(-gamma)
```

---

## XI. Axiom Certificate

The representative certificate command is:

```text
echo 'import MertensPNT
#print axioms ErdosReciprocals.mertens_product_convergence
#print axioms ErdosReciprocals.tendsto_partialProduct_mul_exp_partialSum_add_gamma
#print axioms ErdosReciprocals.mertens_second_theorem_iff_residual_vanishes
#print axioms ErdosReciprocals.mertens_euler_closure_conditional
#print axioms ErdosReciprocals.partialSum_erdosIter_ge_half_mul' \
  | lake env lean --stdin
```

The current certificate is:

```text
'ErdosReciprocals.mertens_product_convergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosReciprocals.tendsto_partialProduct_mul_exp_partialSum_add_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosReciprocals.mertens_second_theorem_iff_residual_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosReciprocals.mertens_euler_closure_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosReciprocals.partialSum_erdosIter_ge_half_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There are no package-local axioms in these certificates.

---

## XII. Reading Guide

For a first pass, read the file in this order:

1. `partialSum`, `partialLogSum`, and `partialProduct`.
2. `tendsto_partialSum_atTop` and the elementary Erdős divergence layer.
3. `mertensPrimeCorrection`, `mertensPrimeCorrectionSum`, and
   `mertensConstant`.
4. `erdosBlockEnd`, `erdosIter`, and
   `partialSum_erdosIter_ge_half_mul`.
5. `partialMertensCorrection` and
   `tendsto_partialProduct_mul_exp_partialSum_add_gamma`.
6. The certified data layer only after the analytic spine is clear.
7. `mertensResidual`, `MertensSecondTheorem`, and
   `mertens_euler_closure_conditional`.

The package is best understood as an infrastructure layer: it certifies
unconditional Mertens/Euler-product material and records the PNT+ step only as a
conditional frontier.

---

## XIII. Verification

The live file was checked with:

```text
lake env lean M4TH/MertensPNT/MertensPNTLive/MertensPNT.live.lean
```

The package build command is:

```text
lake build MertensPNT
```

Both checks are intended to be rerun before publication or Zulip discussion.
