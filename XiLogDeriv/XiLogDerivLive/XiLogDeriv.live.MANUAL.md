# XiLogDeriv.live

**A single-file live presentation of the log-derivative expansion of the
Riemann Xi function and the digamma identity for the real gamma factor,
formalised in Lean 4 over Mathlib.**

\*\*Author:\*\* Bezalel Izquierdo Pérez
\*\*License:\*\* Apache 2.0
\*\*Live file:\*\* `XiLogDeriv.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`XiLogDeriv.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

The Riemann Xi function decomposes as \(\Xi(s) = \tfrac{1}{2} s (s-1) \pi^{-s/2} \Gamma(s/2) \zeta(s)\).
Its logarithmic derivative splits into three summands: polynomial, gamma, and zeta.
The package proves the closed-form expansion and establishes the continuity of the
digamma function away from its poles.

---

## II. The Polynomial Factor

> **Theorem 1. Log-derivative of the polynomial factor.**
>
> **In Lean:**
>
> ```lean
> theorem RiemannLogDeriv.logDeriv_entireXiPolynomialFactor_eq
>     (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
>     logDeriv entireXiPolynomialFactor s = 1/s + 1/(s-1)
> ```

---

## III. The Gamma Factor and Digamma Identity

> **Definition 1. Real gamma factor.**
>
> The gamma factor uses Mathlib's `Complex.Gammaℝ`.
>
> **In Lean:**
>
> ```lean
> noncomputable def RiemannLogDeriv.gammaRFactorLogDeriv (s : ℂ) : ℂ :=
>   logDeriv (fun z => Complex.Gammaℝ z) s
> ```

> **Theorem 2. Digamma identity.**
>
> $$
> \frac{\Gamma_{\mathbb{R}}'}{\Gamma_{\mathbb{R}}}(s) =
> -\frac{1}{2}\log\pi + \frac{1}{2}\psi\Bigl(\frac{s}{2}\Bigr).
> $$
>
> **In Lean:**
>
> ```lean
> theorem RiemannLogDeriv.gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma
>     (s : ℂ) (hs : s / 2 ∉ Set.range (fun n : ℤ => (n : ℂ))) :
>     gammaRFactorLogDeriv s =
>       -((Real.log Real.pi) / 2) + (1/2) * digamma (s/2)
> ```

> **Lemma 1. Continuity of digamma.**
>
> **In Lean:**
>
> ```lean
> lemma RiemannLogDeriv.digamma_continuousOn_of_forall_im_ne_zero
>     {S : Set ℂ} (hS : ∀ z ∈ S, z.im ≠ 0) :
>     ContinuousOn digamma S
> ```

---

## IV. The Three-Component Expansion

> **Theorem 3. Full log-derivative expansion.**
>
> **In Lean:**
>
> ```lean
> theorem RiemannLogDeriv.entireXiLogDeriv_expansion_of_ne_zero_ne_one
>     {s : ℂ} (hs_poly : s ≠ 0 ∧ s ≠ 1)
>     (hs_gamma : s / 2 ∉ Set.range (fun n : ℤ => (n : ℂ))) :
>     entireXiLogDeriv s = ...
> ```

---

## V. Architecture

```text
Basic -> GammaR -> DigammaContinuity -> Expansion
```

- `Basic` -- Xi functions, polynomial factor, log-derivative API
- `GammaR` -- real gamma factor, non-vanishing, differentiability
- `DigammaContinuity` -- continuity of digamma away from poles
- `Expansion` -- closed identity for the three-component decomposition

---

## VI. Axiom Certificate

```text
printf 'import XiLogDeriv
#print axioms RiemannLogDeriv.logDeriv_entireXiPolynomialFactor_eq
#print axioms RiemannLogDeriv.gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma
' | lake env lean --stdin
```

'RiemannLogDeriv.logDeriv_entireXiPolynomialFactor_eq' depends on axioms: [propext, Classical.choice, Quot.sound]

---

## VII. Verification

```text
lake env lean XiLogDeriv/XiLogDerivLive/XiLogDeriv.live.lean
lake build XiLogDeriv
```
