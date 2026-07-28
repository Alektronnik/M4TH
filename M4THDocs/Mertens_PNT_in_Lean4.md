# Mertens' Theorems in Lean 4

## Reciprocal-Prime Divergence, the Meissel–Mertens Constant, and the Conditional PNT+ Closure

**Author.** Bezalel Izquierdo Pérez — ORCID [0009-0001-5993-4057](https://orcid.org/0009-0001-5993-4057)
**Code.** <https://github.com/Alektronnik/M4TH> — package `MertensPNT`
**License.** Apache 2.0 (software), CC-BY 4.0 (text)
**Verification.** Lean 4 over Mathlib. Zero `axiom`, zero `sorry`. Every displayed theorem carries a clean axiom certificate (`[propext, Classical.choice, Quot.sound]`).

---

## Abstract

We report a self-contained formalisation, in the Lean 4 proof assistant on top of
Mathlib, of the elementary theory of Mertens surrounding the sum of prime
reciprocals. A single package, `MertensPNT`, organises the material as a
reusable `ErdosReciprocals` layer. The development establishes, **unconditionally**,
the divergence of `∑_{p≤n} 1/p` through an explicit and quantitative Erdős block
construction, the summability of the Meissel–Mertens correction series
`∑_p (log(1 - 1/p) + 1/p)`, the existence of the Mertens constant
`M = γ + ∑_p (log(1 - 1/p) + 1/p)`, and the compensated convergence of the Euler
product `∏_{p≤n}(1 - 1/p) · exp(∑_{p≤n} 1/p + γ) → exp(M)`, together with the
companion fact `∏_{p≤n}(1 - 1/p) → 0`. Mertens' second theorem
`∑_{p≤n} 1/p = log log n + M + o(1)` and the third-theorem product asymptotic
`∏_{p≤n}(1 - 1/p) · log n → e^{-γ}` are the PNT+ boundary of the theory; they are
recorded as **typed propositions** and never assumed, and the one closure result
that uses them takes them as an explicit hypothesis. The package also ships a
kernel-checked table of primorial and wheel-sieve data. To our knowledge this is
the first formalisation of the quantitative Erdős block proof, of the
Meissel–Mertens correction constant, and of the compensated Euler-product limit
as a single certified chain in a proof assistant.

---

## 1. Introduction

The formalisation of analytic number theory has reached impressive milestones:
the Prime Number Theorem in Isabelle/HOL (Avigad et al., 2007) and in Lean 4
(Han, 2026), and the elementary Chebyshev and Mertens bounds already present in
Mathlib. The M4TH library approaches this territory from the side of *verified
vocabulary*: definitions and first theorems chosen to be the ones a subsequent
Mathlib or PNT+ development would want to build on, each accompanied by a
concrete instance in which the phenomenon is exhibited in full.

This paper treats Mertens' theorems on the reciprocals of the primes. The
mathematics is classical and elementary, but the formalisation makes a clean
separation that the informal literature usually blurs: what is *unconditional*
(the divergence, the correction constant, the compensated product limit) is kept
strictly apart from what is the *PNT+ boundary* (the second theorem with its
`o(1)` term and the third-theorem `e^{-γ}/log n` asymptotic). The boundary is
not proved here; it is stated as a typed hypothesis so that a later development
supplying the `O(1/log n)` error term can discharge it.

Four movements organise the development.

1. **Divergence of `∑ 1/p`, made quantitative** (Section 3). The Euler/Erdős
   fact that the prime reciprocals diverge is reproved constructively through an
   explicit block construction, yielding not merely divergence but the rate
   `∑_{p ≤ erdosIter t} 1/p ≥ t/2`.

2. **The Meissel–Mertens constant** (Section 4). The correction series
   `∑_p (log(1 - 1/p) + 1/p)` is proved summable, and the Mertens constant
   `M = γ + ∑_p (log(1 - 1/p) + 1/p)` is defined and characterised.

3. **The compensated Euler product** (Section 5). The finite Mertens identity
   `log ∏_{p≤n}(1 - 1/p) + ∑_{p≤n} 1/p = ∑_{p≤n}(log(1 - 1/p) + 1/p)` drives the
   unconditional limits `∏ · exp(∑ + γ) → exp(M)` and `∏ → 0`.

4. **The conditional PNT+ closure** (Section 7). Mertens' second theorem is a
   typed proposition `MertensSecondTheorem`; it is shown equivalent to the
   vanishing of the residual `Δ(n) = ∑_{p≤n} 1/p − (log log n + M)`, and it
   implies the scaled-product limit `∏_{p≤n}(1 - 1/p) · log n → e^{-γ}`.

All results are verified with no axioms beyond the foundations of Lean and
Mathlib and with no incomplete proofs. The package depends only on Mathlib and
carries its own `lakefile.toml`, so it can be reviewed, built, and upstreamed
independently.

### 1.1 Contributions

- The first formalisation of the **quantitative Erdős block proof** of the
  divergence of `∑ 1/p`, with explicit block endpoints
  `erdosBlockEnd k = 4^{π(k)+1}`, the iterated subsequence `erdosIter`, and the
  certified rate `partialSum (erdosIter t) ≥ t/2`.
- The first formalisation of the **Meissel–Mertens correction constant**
  `M = γ + ∑_p (log(1 - 1/p) + 1/p)`, together with the summability of the
  correction series.
- The **compensated Euler-product limit** `∏ · exp(∑ + γ) → exp(M)` and the
  companion `∏ → 0`, packaged as a single unconditional theorem
  `mertens_product_convergence`.
- A **typed treatment of the PNT+ boundary**: Mertens' second theorem and the
  third-theorem `e^{-γ}` asymptotic as propositions that are never assumed, with
  an equivalence to residual vanishing and a conditional closure theorem.
- A **kernel-checked data layer**: primorial survival ratios and wheel-sieve
  Euler products proved by `norm_num`, with no trusted compiled evaluation.

### 1.2 Non-goals

We do not prove Mertens' second theorem unconditionally: that requires the
`O(1/log n)` error term of the Chebyshev/PNT+ theory, which is outside this
package. We do not prove the third theorem `∏(1 - 1/p) ~ e^{-γ}/log n`
unconditionally, do not establish the Prime Number Theorem, and do not treat
zero-free regions or explicit error terms. These are the natural next steps; the
present work supplies the definitions, the unconditional core, and the typed
hypotheses on which they would rest.

### 1.3 Relation to earlier releases

The M4TH library was inaugurated with v1.0.0, "Hyperbolic and Dispersive 1D PDE
in Lean 4" (conservation laws, Burgers blow-up, KdV soliton), and continued with
v2.0.0, "Riemann–von Mangoldt in Lean 4" (Dirichlet eta, zero counting,
logarithmic residues, the digamma identity). The present release shifts to the
elementary distribution of primes. As with the earlier releases, it shares no
code with them and depends only on Mathlib, so that either stream may be
upstreamed without cross dependencies.

---

## 2. Setting and Mathlib background

The package is stated over the real numbers and uses only core Mathlib: the
prime infrastructure `Nat.Primes`, `Nat.primesBelow`, `Nat.primeCounting`, and
`Nat.primorial`; the harmonic numbers and `Real.log`, `Real.exp`; the
Euler–Mascheroni constant `eulerMascheroniConstant`; the summability and
`Tendsto`/`atTop` filter API of `Mathlib.Analysis`; and the Chebyshev bound on
the weighted prime sum already in Mathlib. No new axiomatic content is
introduced. Erdős's non-summability of the prime reciprocals is available in
Mathlib and is re-exported here as `erdos_not_summable_primes`; the package's
own contribution is the *quantitative*, block-based reproof that yields an
explicit divergence rate.

All public declarations live in the `ErdosReciprocals` namespace. The reciprocal
partial sum, the weighted sum, and the Euler product are

```lean
noncomputable def ErdosReciprocals.partialSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), primeReciprocalTerm k        -- ∑_{p ≤ n} 1/p

noncomputable def ErdosReciprocals.partialLogSum (n : ℕ) : ℝ  -- ∑_{p ≤ n} (log p)/p

noncomputable def ErdosReciprocals.partialProduct (n : ℕ) : ℝ :=
  ((n + 1).primesBelow).prod (fun p => (1 - (1 : ℝ) / p))    -- ∏_{p ≤ n} (1 - 1/p)
```

---

## 3. Divergence of `∑ 1/p`, made quantitative

The foundational layer collects the elementary bounds — `partialSum 2 = 1/2`,
monotonicity, and the harmonic/Chebyshev comparisons `partialSum n ≤ 1 + log n`
(`partialSum_le_one_add_log`) — and then the divergence itself:

```lean
theorem ErdosReciprocals.tendsto_partialSum_atTop :
    Tendsto partialSum atTop atTop
```

What distinguishes the formalisation is that divergence is obtained
*constructively and with a rate*. Following Erdős, one groups the primes into
blocks whose reciprocal mass is at least `1/2`. The block endpoints are explicit,

```lean
noncomputable def ErdosReciprocals.erdosBlockEnd (k : ℕ) : ℕ :=
  4 ^ (k.primesBelow.card + 1)
```

and iterating the endpoint gives a subsequence `erdosIter : ℕ → ℕ` along which
the partial sums grow at least linearly:

```lean
theorem ErdosReciprocals.partialSum_erdosIter_ge_half_mul (t : ℕ) :
    (t : ℝ) / 2 ≤ partialSum (erdosIter t)
```

Because `erdosIter t → ∞` (`tendsto_erdosIter_atTop`), this single inequality
delivers divergence with an effective rate, independently of the abstract
summability route through `erdos_half_block_lemma`. The package records both,
and derives the classical corollaries — the infinitude of primes and the
existence of arbitrarily large primes — from the divergence.

---

## 4. The Meissel–Mertens constant

Writing `log(1 - 1/p) = -1/p - 1/(2p²) - …`, the per-prime correction
`log(1 - 1/p) + 1/p` is `O(1/p²)`, hence summable over the primes:

```lean
noncomputable def ErdosReciprocals.mertensPrimeCorrection (p : Nat.Primes) : ℝ :=
  log (1 - 1 / primeR p) + 1 / primeR p

theorem ErdosReciprocals.summable_mertensPrimeCorrection :
    Summable mertensPrimeCorrection
```

The Mertens (Meissel–Mertens) constant is defined as the Euler–Mascheroni
constant plus the total correction, and characterised by the definitional
identity:

```lean
noncomputable def ErdosReciprocals.mertensConstant : ℝ :=
  eulerMascheroniConstant + mertensPrimeCorrectionSum

theorem ErdosReciprocals.mertensConstant_eq_gamma_add_correctionSum :
    mertensConstant = eulerMascheroniConstant + mertensPrimeCorrectionSum
```

A reference numerical value `mertensConstantApprox ≈ 0.2614972128` is recorded
separately and proved positive; it is used only in the data layer and is never
substituted into the analytic statements.

---

## 5. The compensated Euler product

The bridge between the additive and multiplicative worlds is the finite Mertens
identity, which holds for every `n`:

```lean
theorem ErdosReciprocals.log_partialProduct_add_partialSum_eq_partialMertensCorrection
    (n : ℕ) :
    log (partialProduct n) + partialSum n = partialMertensCorrection n
```

Since the right-hand side converges to `mertensPrimeCorrectionSum`, exponentiating
and compensating by `∑_{p≤n} 1/p` (which itself diverges) yields a finite limit.
The package packages the three consequences as one theorem:

```lean
theorem ErdosReciprocals.mertens_product_convergence :
    Tendsto partialMertensCorrection atTop (𝓝 mertensPrimeCorrectionSum) ∧
      Tendsto (fun n => partialProduct n * exp (partialSum n)) atTop
        (𝓝 (exp mertensPrimeCorrectionSum)) ∧
      Tendsto partialProduct atTop (𝓝 0)
```

Reintroducing the Euler–Mascheroni constant into the compensation gives the limit
in the normalisation that anticipates Mertens' third theorem:

```lean
theorem ErdosReciprocals.tendsto_partialProduct_mul_exp_partialSum_add_gamma :
    Tendsto (fun n => partialProduct n * exp (partialSum n + eulerMascheroniConstant))
      atTop (𝓝 (exp mertensConstant))
```

All of Section 5 is unconditional. The vanishing of `∏_{p≤n}(1 - 1/p)`
(`partialProduct_tendsto_zero`) is the multiplicative face of the divergence of
`∑ 1/p`, and the compensated limits isolate exactly the constant that the
second and third theorems will name.

---

## 6. A kernel-checked data layer

To keep the empirical side of the theory honest, the package includes a table of
finite facts proved without any trusted compiled evaluation. Primorial survival
ratios and wheel-sieve Euler products are established by `norm_num`, for example

```lean
theorem ErdosReciprocals.primorial_euler_product_30 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) = (4 : ℝ) / 15
```

with the analogous checkpoints up to the primorial of `510510`. These serve as
sanity anchors for the asymptotics and as certified inputs for downstream
heuristics; because they are proved by kernel-level `norm_num` rather than
`native_decide`, they do not enlarge the axiom certificate.

---

## 7. The conditional PNT+ closure

Mertens' second theorem is the statement that the residual

```lean
noncomputable def ErdosReciprocals.mertensResidual (n : ℕ) : ℝ :=
  partialSum n - mertensApprox n            -- ∑_{p≤n} 1/p − (log log n + M)
```

tends to zero. Rather than assume it, the package records it as a typed
proposition and proves the equivalence with residual vanishing:

```lean
def ErdosReciprocals.MertensSecondTheorem : Prop :=
  Tendsto (fun n : ℕ => partialSum n - log (log n)) atTop (𝓝 mertensConstant)

theorem ErdosReciprocals.mertens_second_theorem_iff_residual_vanishes :
    MertensSecondTheorem ↔ MertensResidualVanishes
```

Under this hypothesis, the scaled Euler product `∏_{p≤n}(1 - 1/p) · log n` — whose
limit `e^{-γ}` is Mertens' third theorem — is reached as a corollary:

```lean
theorem ErdosReciprocals.mertens_euler_closure_conditional
    (hMertens : MertensSecondTheorem) :
    MertensResidualVanishes ∧
      Tendsto (fun n : ℕ => log (partialEulerProductScaled n)) atTop
        (𝓝 (-eulerMascheroniConstant)) ∧ …
```

where `partialEulerProductScaled n = partialProduct n * log n`. The hypothesis is
never discharged inside the package; the boundary is left explicit so that a
future development providing the `O(1/log n)` error term of Mertens' second
theorem can close the chain unconditionally. The package also lays out the
graded error hypotheses (`MertensResidualBigOInvLog`, `…Squared`, `…Cubed`) that
such a development would target.

---

## 8. Formalisation notes

**Unconditional versus conditional.** Sections 3–6 are entirely unconditional:
divergence with a rate, the correction constant, the compensated product limits,
and the finite data. Only Section 7 is conditional, and its single hypothesis is
a named `Prop` that appears explicitly in every statement that uses it. The
package makes no claim to an unconditional Prime Number Theorem or Mertens
second/third theorem.

**Quantitative Erdős proof.** The divergence of `∑ 1/p` is obtained from the
explicit block endpoints `erdosBlockEnd` and the linear rate
`partialSum (erdosIter t) ≥ t/2`, not merely from the abstract non-summability
lemma. Both routes are formalised, and the classical corollaries are derived from
the constructive one.

**No axioms, no `sorry`, no `native_decide`.** Every result is kernel-checked.
The numerical witnesses in the data layer are proved by `norm_num` and explicit
finite reductions rather than by trusted compiled evaluation, so the axiom
certificate of each headline theorem is exactly
`[propext, Classical.choice, Quot.sound]`.

**Packaging.** The package is internally layered as
`Basic → MertensConstant → ErdosBlocks → MertensBridge → TTAOData → Connections
→ PNTFrontier`, each file compiling on the previous ones only, so that a Mathlib
or PNT+ PR series can be opened in that order, each self-contained and useful on
its own. Public names use the `ErdosReciprocals` namespace and are flagged for
renaming in coordination with Mathlib's prime-number-theorem reviewers.

---

## 9. Related work

The Prime Number Theorem was formalised in Isabelle/HOL by Avigad et al. (2007)
and recently in Lean 4 (Han, 2026); both provide the unconditional PNT and the
elementary Chebyshev/Mertens bounds now in Mathlib. Mathlib itself contains the
non-summability of the prime reciprocals and Chebyshev's weighted-sum bound. The
present work is complementary: it supplies the *quantitative* Erdős block proof,
the Meissel–Mertens correction constant, and the compensated Euler-product limit
as a single certified chain, and it isolates the second and third theorems as
typed hypotheses so that the PNT+ boundary is explicit rather than assumed.

Classical references for the mathematics formalised here are Hardy and Wright's
introduction [3], Tenenbaum's treatise [5], Mertens' original memoir [4], and the
expositions of Apostol [1] and Davenport [2]; we formalise only the elementary,
self-contained fragments.

---

## 10. Availability

The package is available at <https://github.com/Alektronnik/M4TH> under the
Apache 2.0 license, with its own `lakefile.toml` (pinned to Mathlib `fabf563a`,
Lean 4 v4.31.0) and a native Lean-generated SVG cover figure. It also includes a
`Live` single-file study version and a mathematical manual. After a successful
build the axiom certificate of each headline theorem may be reproduced with

```
#print axioms ErdosReciprocals.mertens_product_convergence
#print axioms ErdosReciprocals.tendsto_partialProduct_mul_exp_partialSum_add_gamma
#print axioms ErdosReciprocals.mertens_second_theorem_iff_residual_vanishes
#print axioms ErdosReciprocals.mertens_euler_closure_conditional
#print axioms ErdosReciprocals.partialSum_erdosIter_ge_half_mul
```

each returning `[propext, Classical.choice, Quot.sound]`.

---

## References

1. T. M. Apostol, *Introduction to Analytic Number Theory*, Springer, 1976.
2. H. Davenport, *Multiplicative Number Theory*, Springer, 3rd ed., 2000.
3. G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*,
   Oxford, 6th ed., 2008.
4. F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine angew.
   Math. **78** (1874), 46–62.
5. G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*,
   AMS, 3rd ed., 2015.
6. The mathlib Community, *The Lean Mathematical Library*, CPP 2020;
   <https://github.com/leanprover-community/mathlib4>.
