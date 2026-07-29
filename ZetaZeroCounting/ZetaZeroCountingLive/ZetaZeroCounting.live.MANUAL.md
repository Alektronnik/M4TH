# ZetaZeroCounting.live

**A single-file live presentation of the Riemann-von Mangoldt zero-counting
infrastructure: N(T) with multiplicities, safe heights, and the von Mangoldt
main term, formalised in Lean 4 over Mathlib.**

\*\*Author:\*\* Bezalel Izquierdo Pérez
\*\*License:\*\* Apache 2.0
\*\*Live file:\*\* `ZetaZeroCounting.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`ZetaZeroCounting.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

The Riemann-von Mangoldt formula counts the nontrivial zeros up to height \(T\):

$$
N(T) = \#\{\rho : \zeta(\rho) = 0,\; 0 < \Re(\rho) < 1,\; 0 < \Im(\rho) \le T\}.
$$

The package builds the infrastructure: the finite set of zeros, the density of
safe heights, and the asymptotic main term.  It does **not** prove the counting
formula; that is the conditional frontier addressed by v4.0.0 packages.

---

## II. Nontrivial Zeros and Counting

> **Definition 1. Nontrivial zeros and zeros up to height T.**
>
> **In Lean:**
>
> ```lean
> def Riemann.nontrivialZeros : Set ℂ :=
>   {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}
>
> def Riemann.zerosUpToIm (T : ℝ) : Set ℂ :=
>   {s | s ∈ nontrivialZeros ∧ 0 < s.im ∧ s.im ≤ T}
> ```

> **Theorem 1. Finite number of zeros up to any height.**
>
> **In Lean:**
>
> ```lean
> theorem Riemann.zerosUpToIm_finite (T : ℝ) :
>     Set.Finite (zerosUpToIm T)
> ```

> **Definition 2. Counting functions.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Riemann.zeroCountingFun (T : ℝ) : ℕ
> noncomputable def Riemann.distinctZeroCount (T : ℝ) : ℕ
> ```

`zeroCountingFun` counts with multiplicities; `distinctZeroCount` counts
distinct zeros.

---

## III. Safe Heights

> **Definition 3. Safe height predicate.**
>
> **In Lean:**
>
> ```lean
> def Riemann.IsSafeHeight (T : ℝ) : Prop :=
>   ∀ s ∈ nontrivialZeros, s.im ≠ T
> ```

> **Theorem 2. Density of safe heights.**
>
> Every interval \((T, T + \varepsilon]\) contains a safe height.
>
> **In Lean:**
>
> ```lean
> theorem Riemann.exists_safe_height_above
>     (T : ℝ) (ε : ℝ) (hε : 0 < ε) :
>     ∃ T' ∈ Set.Ioc T (T + ε), IsSafeHeight T'
> ```

---

## IV. The Von Mangoldt Main Term

> **Definition 4. Classical von Mangoldt main term.**
>
> $$
> N(T) \sim \frac{T}{2\pi}\Bigl(\log\frac{T}{2\pi} - 1\Bigr).
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def Riemann.vonMangoldtMainTerm (T : ℝ) : ℝ :=
>   (T / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1)
> ```

> **Theorem 3. T is o of the main term.**
>
> **In Lean:**
>
> ```lean
> theorem Riemann.T_isLittleO_vonMangoldtMainTerm :
>     (fun T : ℝ => T) =o[atTop] vonMangoldtMainTerm
> ```

---

## V. Architecture

```text
Xi -> ZeroCounting -> SafeHeights -> MainTerm
```

- `Xi` -- completed Xi function, symmetry, nontrivial zeros
- `ZeroCounting` -- N(T) with multiplicities, finiteness
- `SafeHeights` -- density of safe heights, enclosures
- `MainTerm` -- von Mangoldt main term, asymptotic API

---

## VI. Axiom Certificate

```text
printf 'import ZetaZeroCounting
#print axioms Riemann.zerosUpToIm_finite
#print axioms Riemann.exists_safe_height_above
' | lake env lean --stdin
```

'Riemann.zerosUpToIm_finite' depends on axioms: [propext, Classical.choice, Quot.sound]

---

## VII. Verification

```text
lake env lean ZetaZeroCounting/ZetaZeroCountingLive/ZetaZeroCounting.live.lean
lake build ZetaZeroCounting
```
