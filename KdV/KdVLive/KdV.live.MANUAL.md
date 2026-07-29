# KdV

**A single-file live presentation of the exact KdV soliton, the travelling-wave
reduction, and compact-support conservation laws, formalised in Lean 4 over
Mathlib.**

- Author: Bezalel Izquierdo Perez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0
- Companion file: `KdV.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`KdV.live.lean`.  It presents the mathematical content in the same order as the
live Lean file.  Proof scripts are intentionally omitted here; the live Lean
file is the certificate.

---

## I. The Mathematical Problem

The Korteweg-de Vries equation

$$
u_t + u u_x + u_{xxx} = 0
$$

is the prototypical integrable dispersive PDE.  Its exact soliton solution is

$$
u(t,x) = 3c \operatorname{sech}^2\Bigl(\frac{\sqrt{c}}{2}(x - ct)\Bigr),
\qquad c > 0.
$$

The package proves three facts: the travelling-wave reduction, the exact
hyperbolic soliton profile, and the compact-support conservation laws for
mass and energy.

---

## II. Travelling-Wave Reduction

> **Definition 1. Travelling-wave ansatz.**
>
> $$
> u(t,x) = f(x - ct).
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def KdV.travellingWave (c : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
>   f (x - c * t)
> ```

> **Theorem 1. Travelling-wave reduction.**
>
> Substituting the ansatz into KdV reduces it to the stationary ODE
>
> $$
> -c f' + f f' + f''' = 0.
> $$
>
> **In Lean:**
>
> ```lean
> theorem KdV.travellingWave_reduction (c : ℝ) (f : ℝ → ℝ)
>     (hf : ContDiff ℝ 3 f) (t x : ℝ) :
>     (travellingWave c f) satisfies the KdV ODE iff ...
> ```

---

## III. The Exact Soliton

> **Definition 2. Soliton profile.**
>
> $$
> \phi_c(x) = 3c \operatorname{sech}^2\Bigl(\frac{\sqrt{c}}{2} x\Bigr).
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def KdV.solitonProfile (c : ℝ) (x : ℝ) : ℝ :=
>   3 * c * (Real.sech ((Real.sqrt c / 2) * x)) ^ 2
> ```

> **Lemma 1. Hyperbolic-function calculus.**
>
> The hyperbolic identities needed for the verification: derivatives of
> \(\operatorname{sech}\), \(\operatorname{tanh}\), and the algebraic
> relations between them.
>
> **In Lean:**
>
> ```lean
> lemma KdV.sech_deriv (x : ℝ) : deriv Real.sech x = -Real.sech x * Real.tanh x
> lemma KdV.sech_sq_add_tanh_sq (x : ℝ) : Real.sech x ^ 2 + Real.tanh x ^ 2 = 1
> ```

> **Theorem 2. Soliton satisfies the ODE.**
>
> For all \(c > 0\), the profile \(\phi_c\) satisfies
>
> $$
> -c \phi_c' + \phi_c \phi_c' + \phi_c''' = 0.
> $$
>
> **In Lean:**
>
> ```lean
> theorem KdV.soliton_satisfies_kdv (c : ℝ) (hc : c > 0) (x : ℝ) :
>     -c * deriv (solitonProfile c) x +
>       solitonProfile c x * deriv (solitonProfile c) x +
>       deriv (deriv (deriv (solitonProfile c))) x = 0
> ```

---

## IV. Conservation Laws

> **Definition 3. Conserved quantities for compactly supported solutions.**
>
> **In Lean:**
>
> ```lean
> structure KdV.ConservedSolution (u : ℝ → ℝ → ℝ) where
>   satisfies_kdv : ∀ t x, ...
>   compact_support : ∀ t, HasCompactSupport (u t)
> ```

> **Theorem 3. Mass conservation.**
>
> $$
> \frac{d}{dt} \int_{\mathbb{R}} u(t,x)\,dx = 0.
> $$
>
> **In Lean:**
>
> ```lean
> theorem KdV.ConservedSolution.massRate_conserved
>     (u : ConservedSolution) (t : ℝ) :
>     HasDerivAt (fun τ => ∫ x, u τ x) 0 t
> ```

> **Theorem 4. Energy conservation.**
>
> $$
> \frac{d}{dt} \int_{\mathbb{R}} u(t,x)^2\,dx = 0.
> $$
>
> **In Lean:**
>
> ```lean
> theorem KdV.ConservedSolution.energyRate_conserved
>     (u : ConservedSolution) (t : ℝ) :
>     HasDerivAt (fun τ => ∫ x, (u τ x)^2) 0 t
> ```

---

## V. Architecture

```text
Basic -> Hyperbolic -> Soliton -> ConservationLaws
```

- `Basic` -- KdV operator, travelling-wave ansatz
- `Hyperbolic` -- derivatives of sech/tanh, algebraic identities
- `Soliton` -- exact profile, ODE satisfaction
- `ConservationLaws` -- compact support, mass/energy integrals

---

## VI. Axiom Certificate

```text
printf 'import KdV
#print axioms KdV.soliton_satisfies_kdv
#print axioms KdV.ConservedSolution.massRate_conserved
' | lake env lean --stdin
```

Expected: `[propext, Classical.choice, Quot.sound]`

---

## VII. Verification

```text
lake env lean KdV/KdVLive/KdV.live.lean
lake build KdV
```
