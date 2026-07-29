# XiLogResidue

**A single-file live presentation of the logarithmic residue = multiplicity
theorem for the Riemann Xi function and the dictionary with
`MeromorphicOn.divisor`, formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Perez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0
- Companion file: `XiLogResidue.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`XiLogResidue.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

For a meromorphic function \(f\), the logarithmic derivative \(f'/f\) has a
simple pole at each zero or pole of \(f\), and the residue at a zero equals the
multiplicity of that zero.  The package proves this theorem for the entire
Xi variant and builds the dictionary between the analytic multiplicity and
Mathlib's `MeromorphicOn.divisor`.

The core identity is:

$$
\operatorname{Res}_{s = \rho}\frac{\Xi'}{\Xi}(s) = \operatorname{mult}_{\rho}(\Xi).
$$

This connects the complex-analytic residue calculus to the finite-set divisor
formalism, enabling the zero-counting apparatus of the Riemann-von Mangoldt
series.

---

## II. Xi Function and Critical Box

> **Definition 1. Entire Xi variant.**
>
> $$
> \Xi(s) = s(s-1)\Xi_0(s) + 1
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def RiemannLogResidue.entireXi (s : ℂ) : ℂ :=
>   s * (s - 1) * completedRiemannZeta₀ s + 1
> ```

> **Definition 2. Critical box and edge parametrisations.**
>
> **In Lean:**
>
> ```lean
> def RiemannLogResidue.criticalBox (T : ℝ) : Set ℂ :=
>   {s | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}
> ```

---

## III. Local Residue Theorem

> **Theorem 1. Residue equals multiplicity.**
>
> At each zero \(z\) of \(\Xi\), the residue of \(\Xi'/\Xi\) at \(z\) equals
> the analytic order of \(\Xi\) at \(z\) (i.e., the multiplicity of the zero).
>
> **In Lean:**
>
> ```lean
> theorem RiemannLogResidue.entireXi_logDeriv_residue_eq_multiplicity
>     (z : ℂ) (hz : entireXi z = 0) :
>     residue (logDeriv entireXi) z = analyticOrderAt entireXi z
> ```

> **Lemma 1. Xi is meromorphic on the critical box.**
>
> **In Lean:**
>
> ```lean
> lemma RiemannLogResidue.entireXi_meromorphicOn_criticalBox (T : ℝ) :
>     MeromorphicOn entireXi (criticalBox T)
> ```

---

## IV. Divisor Dictionary

> **Definition 3. Divisor of Xi.**
>
> The finite formal sum of zeros with multiplicities, expressed as a
> `MeromorphicOn.divisor`.
>
> **In Lean:**
>
> ```lean
> noncomputable def RiemannLogResidue.entireXi_divisor (T : ℝ) :
>     MeromorphicOn.divisor ℂ
> ```

> **Theorem 2. Divisor support equals the zero set.**
>
> The support of the divisor coincides with the explicit finite set of
> nontrivial zeros counted up to height \(T\).
>
> **In Lean:**
>
> ```lean
> theorem RiemannLogResidue.entireXi_divisor_finset_eq_zerosUpToImFinset
>     (T : ℝ) (hT : IsSafeHeight T) :
>     (entireXi_divisor T).support = zerosUpToImFinset T
> ```

This is the concrete instance of the "Theorem on Logarithmic Differentials"
that bridges the residue calculus with the combinatorial divisor formalism.

---

## V. Architecture

```text
Basic -> LocalResidue -> Divisor
```

- `Basic` -- entire Xi, log-derivative, critical box, meromorphy
- `LocalResidue` -- residue = multiplicity at each zero
- `Divisor` -- divisor construction, dictionary with zero-counting

---

## VI. Axiom Certificate

```text
printf 'import XiLogResidue
#print axioms RiemannLogResidue.entireXi_logDeriv_residue_eq_multiplicity
#print axioms RiemannLogResidue.entireXi_divisor_finset_eq_zerosUpToImFinset
' | lake env lean --stdin
```

Expected: `[propext, Classical.choice, Quot.sound]`

---

## VII. Verification

```text
lake env lean XiLogResidue/XiLogResidueLive/XiLogResidue.live.lean
lake build XiLogResidue
```
