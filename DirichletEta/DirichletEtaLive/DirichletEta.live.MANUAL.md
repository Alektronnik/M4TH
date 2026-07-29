# DirichletEta.live

**A single-file live presentation of the Dirichlet eta function, its
zeta-product identity, and the conditional non-vanishing of zeta on
the real interval (0,1), formalised in Lean 4 over Mathlib.**

\*\*Author:\*\* Bezalel Izquierdo Pérez
\*\*License:\*\* Apache 2.0
\*\*Live file:\*\* `DirichletEta.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`DirichletEta.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

The Dirichlet eta function is the alternating zeta series

$$
\eta(s) = \sum_{n=0}^{\infty} \frac{(-1)^n}{(n+1)^{s}}, \qquad \Re(s) > 0.
$$

It is related to the Riemann zeta function by the elementary identity

$$
\eta(s) = (1 - 2^{1-s})\,\zeta(s), \qquad \Re(s) > 1.
$$

The package proves this identity unconditionally.  The non-vanishing of
\(\zeta(x)\) for \(x \in (0,1)\) is **conditional** on the typed frontier
`RiemannZetaAlternatingLimitIdentity`, which states that the real alternating
limit equals the zeta-product formula.

The logical flow is:

```text
etaTerm n s = (-1)^n / (n+1)^s
    |
    v
dirichletEtaSeries s = sum_{n>=0} etaTerm n s
    |
    v   (even-odd split for Re(s) > 1)
eta_zeta_odd_even_split
    |
    v   (unconditional)
eta_eq_zeta_of_re_gt_one: eta(s) = (1 - 2^(1-s)) * zeta(s)
    |
    v   (conditional on RiemannZetaAlternatingLimitIdentity)
zeta_real_open_interval_nonvanishing_from_eta
```

---

## II. The Alternating Eta Series

> **Definition 1. Eta term.**
>
> $$
> \eta_n(s) = \frac{(-1)^n}{(n+1)^s}.
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def DirichletEta.etaTerm (n : ℕ) (s : ℂ) : ℂ :=
>   (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s
> ```

> **Definition 2. Dirichlet eta series.**
>
> $$
> \eta(s) = \sum_{n=0}^{\infty} \eta_n(s).
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def DirichletEta.dirichletEtaSeries (s : ℂ) : ℂ :=
>   ∑' n, etaTerm n s
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

> **Theorem 1. The eta-zeta identity (unconditional).**
>
> For \(\Re(s) > 1\),
>
> $$
> \eta(s) = (1 - 2^{1-s})\,\zeta(s).
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

## IV. Conditional Non-Vanishing on (0,1)

> **Definition 3. Typed frontier.**
>
> The identity connecting the real alternating limit to the zeta product.
> This is the single conditional hypothesis of the package.
>
> **In Lean:**
>
> ```lean
> def DirichletEta.RiemannZetaAlternatingLimitIdentity : Prop :=
>   ∀ (x : ℝ), 0 < x → x ≠ 1 → ∀ l : ℝ,
>     Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i / (i + 1 : ℝ) ^ x)
>       atTop (𝓝 l) →
>     riemannZeta x * (1 - (2 : ℂ) ^ (1 - (x : ℂ))) = l
> ```

> **Lemma 2. Positivity of the real alternating limit.**
>
> For every real \(x > 0\), the alternating series converges to a positive limit.
>
> **In Lean:**
>
> ```lean
> lemma DirichletEta.alternating_zeta_real_pos (x : ℝ) (hx0 : 0 < x) :
>     ∃ l, Tendsto
>       (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i / (i + 1 : ℝ) ^ x)
>       atTop (𝓝 l) ∧ 0 < l
> ```

> **Theorem 2. Conditional non-vanishing on the open unit interval.**
>
> Under the typed frontier, \(\zeta(x) \neq 0\) for all \(x \in (0,1)\).
>
> **In Lean:**
>
> ```lean
> theorem DirichletEta.zeta_real_open_interval_nonvanishing_from_eta
>     (hη : RiemannZetaAlternatingLimitIdentity) :
>     ∀ x : ℝ, 0 < x → x < 1 → riemannZeta x ≠ 0
> ```

The package does **not** claim an unconditional non-vanishing theorem.
The hypothesis `RiemannZetaAlternatingLimitIdentity` is the explicit
analytic frontier.

---

## V. Architecture

```text
Basic -> Analytic -> Nonvanishing
```

- `Basic` -- series definitions, even-odd split, eta-zeta identity (unconditional)
- `Analytic` -- differentiability, uniform convergence
- `Nonvanishing` -- positivity, conditional non-vanishing on (0,1)

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
