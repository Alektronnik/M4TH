# XiLogDeriv

**A single-file live presentation of the log-derivative expansion of the
Riemann Xi function and the digamma identity for the real gamma factor,
formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Perez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0
- Companion file: `XiLogDeriv.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`XiLogDeriv.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

The Riemann Xi function is defined as

$$
\Xi(s) = \tfrac{1}{2} s (s-1) \pi^{-s/2} \Gamma(\tfrac{s}{2}) \zeta(s).
$$

Its logarithmic derivative decomposes into three summands:

$$
\frac{\Xi'}{\Xi}(s) = P(s) + G(s) + Z(s)
$$

where \(P\) is the polynomial factor, \(G\) is the gamma factor, and \(Z\) is
the zeta factor.  The package proves the closed-form expansion of each summand
and establishes the continuity of the digamma function away from its poles.

---

## II. The Polynomial Factor

> **Definition 1. Entire Xi polynomial factor.**
>
> **In Lean:**
>
> ```lean
> noncomputable def RiemannLogDeriv.entireXiPolynomialFactor (s : ℂ) : ℂ :=
>   s * (s - 1) * completedRiemannZeta₀ s + 1
> ```

> **Theorem 1. Log-derivative of the polynomial factor.**
>
> $$
> \frac{P'}{P}(s) = \frac{1}{s} + \frac{1}{s-1}.
> $$
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

> **Definition 2. Real gamma factor.**
>
> $$
> \Gamma_{\mathbb{R}}(s) = \pi^{-s/2} \Gamma(s/2).
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def RiemannLogDeriv.gammaRFactor (s : ℂ) : ℂ :=
>   (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)
> ```

> **Theorem 2. Digamma identity for the real gamma factor.**
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
>     logDeriv gammaRFactor s = -((Real.log Real.pi) / 2) + (1/2) * digamma (s/2)
> ```

> **Lemma 1. Gamma factor non-vanishing and differentiability.**
>
> **In Lean:**
>
> ```lean
> lemma RiemannLogDeriv.gammaRFactor_ne_zero (s : ℂ)
>     (hs : s / 2 ∉ Set.range (fun n : ℤ => (n : ℂ))) : gammaRFactor s ≠ 0
> ```

> **Lemma 2. Continuity of digamma away from poles.**
>
> **In Lean:**
>
> ```lean
> lemma RiemannLogDeriv.digamma_continuousOn_complement_poles :
>     ContinuousOn digamma {s | s ∉ Set.range (fun n : ℤ => (n : ℂ))}
> ```

---

## IV. The Three-Component Expansion

> **Theorem 3. Full log-derivative expansion.**
>
> **In Lean:**
>
> ```lean
> theorem RiemannLogDeriv.entireXiLogDeriv_expansion (s : ℂ)
>     (hs_poly : s ≠ 0 ∧ s ≠ 1) (hs_gamma : ...) :
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

Expected: `[propext, Classical.choice, Quot.sound]`

---

## VII. Verification

```text
lake env lean XiLogDeriv/XiLogDerivLive/XiLogDeriv.live.lean
lake build XiLogDeriv
```
