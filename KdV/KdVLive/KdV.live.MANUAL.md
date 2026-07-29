# KdV.live

**A single-file live presentation of the exact KdV soliton, the travelling-wave
reduction, and compact-support conservation laws, formalised in Lean 4 over
Mathlib.**

**Author:** Bezalel Izquierdo Pérez
**License:** Apache 2.0
**Live file:** `KdV.live.lean`

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

The package proves the travelling-wave reduction, the exact hyperbolic soliton
profile, and the compact-support conservation laws for mass and energy.

---

## II. Travelling-Wave Reduction

> **Definition 1. Travelling-wave structure.**
>
> **In Lean:**
>
> ```lean
> structure KdV.TravellingWave (c : ℝ) where
>   profile : ℝ → ℝ
>   h_contdiff : ContDiff ℝ 3 profile
> ```

> **Theorem 1. Travelling-wave reduction.**
>
> Substituting a travelling wave \(f(x - ct)\) into KdV reduces it to the
> stationary ODE \(-c f' + f f' + f''' = 0\).
>
> **In Lean:**
>
> ```lean
> theorem KdV.travellingWave_reduction
>     {T : ℝ} {u : ℝ → ℝ → ℝ} (sol : IsSolution T u)
>     (c : ℝ) (tw : TravellingWave c)
>     (h_eq : ∀ t x, u t x = tw.profile (x - c * t))
>     {t : ℝ} (ht : t ∈ Set.Ico 0 T) (x : ℝ) :
>     -c * deriv tw.profile x +
>       tw.profile x * deriv tw.profile x +
>       deriv (deriv (deriv tw.profile)) x = 0
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
>   3 * c * (sech ((Real.sqrt c / 2) * x)) ^ 2
> ```

> **Lemma 1. Hyperbolic-function calculus.**
>
> The package uses a local `sech` with the standard identities.
>
> **In Lean:**
>
> ```lean
> lemma KdV.hasDerivAt_sech (x : ℝ) :
>     HasDerivAt sech (-sech x * Real.tanh x) x
>
> lemma KdV.sech_sq_eq_one_sub_tanh_sq (x : ℝ) :
>     sech x ^ 2 = 1 - Real.tanh x ^ 2
> ```

> **Theorem 2. Soliton satisfies the ODE.**
>
> For all \(c > 0\), the profile \(\phi_c\) satisfies
> \(-c \phi_c' + \phi_c \phi_c' + \phi_c''' = 0\).
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
>     (sol : ConservedSolution T u)
>     {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
>     ∫ x, KdV.ut u t x = 0
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
>     (sol : ConservedSolution T u)
>     {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
>     ∫ x, u t x * KdV.ut u t x = 0
> ```

---

## V. Architecture

```text
Basic -> Hyperbolic -> Soliton -> ConservationLaws
```

- `Basic` -- KdV operator, travelling-wave structure, reduction
- `Hyperbolic` -- derivatives of local `sech`, algebraic identities
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

'KdV.soliton_satisfies_kdv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KdV.ConservedSolution.massRate_conserved' depends on axioms: [propext, Classical.choice, Quot.sound]

---

## VII. Verification

```text
cd KdV && lake build
```
