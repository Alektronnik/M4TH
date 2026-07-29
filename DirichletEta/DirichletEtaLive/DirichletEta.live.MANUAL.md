# DirichletEta

**A single-file live presentation of the Dirichlet eta function, its
zeta-product identity, and the non-vanishing of zeta on the real interval
(0,1), formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Perez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0
- Companion file: `DirichletEta.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`DirichletEta.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

The Dirichlet eta function is the alternating zeta series

$$
\eta(s) = \sum_{n=1}^{\infty} \frac{(-1)^{n-1}}{n^{s}}, \qquad \Re(s) > 0.
$$

It is related to the Riemann zeta function by the elementary identity

$$
\eta(s) = (1 - 2^{1-s})\,\zeta(s), \qquad \Re(s) > 1.
$$

The package proves this identity and uses the positivity of the real alternating
series to establish

$$
\zeta(x) \neq 0 \quad\text{for all}\quad x \in (0,1).
$$

The logical flow is:

```text
etaTerm n s = (-1)^(n-1) / n^s
    |
    v   even-odd split for Re(s) > 1
eta(s) = odd_block - even_block
    |
    v   even block = 2^(1-s) * zeta(s)
eta(s) = (1 - 2^(1-s)) * zeta(s)
    |
    v   for x in (0,1): eta(x) > 0, (1-2^(1-x)) != 0
zeta(x) != 0
```

---

## II. The Alternating Eta Series

> **Definition 1. Eta term.**
>
> $$
> \eta_n(s) = \frac{(-1)^{n-1}}{n^s}.
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def DirichletEta.etaTerm (n : ℕ) (s : ℂ) : ℂ :=
>   (-1 : ℂ) ^ (n - 1) / (n : ℂ) ^ s
> ```

> **Definition 2. Dirichlet eta series and partial sums.**
>
> **In Lean:**
>
> ```lean
> noncomputable def DirichletEta.dirichletEtaSeries (s : ℂ) : ℂ :=
>   ∑' n : ℕ, etaTerm (n + 1) s
>
> noncomputable def DirichletEta.dirichletEta (s : ℂ) : ℂ
> ```

> **Lemma 1. Absolute convergence for Re(s) > 1.**
>
> **In Lean:**
>
> ```lean
> lemma DirichletEta.eta_summable_one_div_nat_add_one_cpow
>     {s : ℂ} (hs : 1 < s.re) :
>     Summable fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ s‖
> ```

---

## III. The Zeta-Product Identity

> **Lemma 2. Even-odd split.**
>
> **In Lean:**
>
> ```lean
> lemma DirichletEta.eta_zeta_odd_even_split
>     {s : ℂ} (hs : 1 < s.re) :
>     dirichletEtaSeries s =
>       (∑' n : ℕ, 1 / ((2 * (n : ℂ) + 1) ^ s)) -
>       (∑' n : ℕ, 1 / ((2 * ((n : ℂ) + 1)) ^ s))
> ```

> **Theorem 1. The eta-zeta identity.**
>
> $$
> \eta(s) = (1 - 2^{1-s})\,\zeta(s), \qquad \Re(s) > 1.
> $$
>
> **In Lean:**
>
> ```lean
> theorem DirichletEta.eta_eq_zeta_of_re_gt_one
>     {s : ℂ} (hs : 1 < s.re) :
>     dirichletEtaSeries s = (1 - 2 ^ (1 - s)) * riemannZeta s
> ```

---

## IV. Non-Vanishing on (0,1)

> **Lemma 3. Real alternating limit is positive.**
>
> **In Lean:**
>
> ```lean
> lemma DirichletEta.alternating_zeta_real_pos
>     (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : 0 < dirichletEta (x : ℂ)
> ```

> **Theorem 2. Riemann zeta non-vanishing on the open unit interval.**
>
> $$
> \zeta(x) \neq 0 \quad\text{for all}\quad x \in (0,1).
> $$
>
> **In Lean:**
>
> ```lean
> theorem DirichletEta.zeta_real_open_interval_nonvanishing_from_eta
>     (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
>     riemannZeta (x : ℂ) ≠ 0
> ```

---

## V. Architecture

```text
Basic -> Analytic -> Nonvanishing
```

- `Basic` -- series definitions, even-odd split, eta-zeta identity
- `Analytic` -- differentiability, analytic continuation, uniform convergence
- `Nonvanishing` -- positivity, non-vanishing on (0,1)

---

## VI. Axiom Certificate

```text
printf 'import DirichletEta
#print axioms DirichletEta.eta_eq_zeta_of_re_gt_one
#print axioms DirichletEta.zeta_real_open_interval_nonvanishing_from_eta
' | lake env lean --stdin
```

Expected: `[propext, Classical.choice, Quot.sound]`

---

## VII. Verification

```text
lake env lean DirichletEta/DirichletEtaLive/DirichletEta.live.lean
lake build DirichletEta
```
