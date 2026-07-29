# XiArgumentPrinciple.live

**A single-file live presentation of the critical-box argument-principle chain
for the Riemann Xi variant, formalised in Lean 4 over Mathlib.**

\*\*Author:\*\* Bezalel Izquierdo Pérez
\*\*License:\*\* Apache 2.0
\*\*Live file:\*\* `XiArgumentPrinciple.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`XiArgumentPrinciple.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

The argument principle relates the contour integral of the logarithmic derivative
\(f'/f\) around a closed curve to the number of zeros of \(f\) inside.  For the
Riemann Xi function, the contour is the boundary of the critical box
\(\{0 \le \Re(s) \le 1,\; 0 \le \Im(s) \le T\}\).

The package proves the unconditional contour/rectangle identity and packages the
counting step as a theorem conditional on an explicit typed bridge.  The
rectangular residue theorem is NOT proved; its content is exposed as the
`ArgumentPrincipleBridge` structure.

The logical flow is:

```text
entireXiLogDeriv
    |
    v   parametrised edges: bottom, right, top, left
entireXiContourIntegral T
    |
    v   unconditional algebraic identity
entireXiContourIntegral T = criticalBoxRectangleIntegral entireXiLogDeriv T
    |
    v   conditional on ArgumentPrincipleBridge
contour_winding_equals_count_of_safe: contour integral = 2πi * N(T)
```

---

## II. Critical Box and Contour

> **Definition 1. Entire Xi variant.**
>
> **In Lean:**
>
> ```lean
> noncomputable def RiemannArgumentPrinciple.entireXi (s : ℂ) : ℂ :=
>   s * (s - 1) * completedRiemannZeta₀ s + 1
> ```

> **Definition 2. Critical box and safe heights.**
>
> **In Lean:**
>
> ```lean
> def RiemannArgumentPrinciple.criticalBox (T : ℝ) : Set ℂ :=
>   {s | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}
>
> def RiemannArgumentPrinciple.IsSafeHeight (T : ℝ) : Prop :=
>   -- no nontrivial zero lies on the top edge
> ```

> **Definition 3. Four edge parametrisations.**
>
> Each edge is given an explicit parametrisation for the contour integral.
>
> **In Lean:**
>
> ```lean
> noncomputable def RiemannArgumentPrinciple.criticalBoxBottomParam (t : ℝ) : ℂ := (t : ℂ)
> noncomputable def RiemannArgumentPrinciple.criticalBoxRightParam (T t : ℝ) : ℂ := 1 + (t : ℂ) * I
> noncomputable def RiemannArgumentPrinciple.criticalBoxTopParam (T t : ℝ) : ℂ := (t : ℂ) + (T : ℂ) * I
> noncomputable def RiemannArgumentPrinciple.criticalBoxLeftParam (T t : ℝ) : ℂ := (t : ℂ) * I
> ```

> **Definition 4. Oriented contour integral.**
>
> **In Lean:**
>
> ```lean
> noncomputable def RiemannArgumentPrinciple.entireXiContourIntegral (T : ℝ) : ℂ :=
>   entireXiBottomEdgeIntegral + entireXiRightEdgeIntegral T +
>     entireXiTopEdgeIntegral T + entireXiLeftEdgeIntegral T
> ```

---

## III. Unconditional Theorem

> **Theorem 1. Contour equals rectangle.**
>
> The edge-by-edge contour integral equals the rectangular integral of the
> same integrand.  This is unconditional and purely algebraic: it follows from
> the explicit edge parametrisations and the change-of-variables formula.
>
> **In Lean:**
>
> ```lean
> theorem RiemannArgumentPrinciple.entireXiContourIntegral_eq_rectangleIntegral
>     (T : ℝ) :
>     entireXiContourIntegral T =
>       criticalBoxRectangleIntegral entireXiLogDeriv T
> ```

---

## IV. The Typed Argument-Principle Bridge

> **Definition 5. Argument principle bridge.**
>
> The three analytic facts the classical proof would import from the
> rectangular residue theorem are exposed as explicit `Prop` fields:
>
> **In Lean:**
>
> ```lean
> structure RiemannArgumentPrinciple.ArgumentPrincipleBridge (T : ℝ) : Prop where
>   index_one : ∀ {w : ℂ}, w ∈ criticalBoxInterior T →
>     contourCauchyIndexIntegral w T = 2 * Real.pi * I
>   index_zero : ∀ {w : ℂ}, w ∉ criticalBox T →
>     contourCauchyIndexIntegral w T = 0
>   residue_sum :
>     entireXiContourIntegral T / (2 * Real.pi * I) =
>       entireXiCriticalBoxResidueSum T
> ```

---

## V. Conditional Counting Theorems

> **Theorem 2. Winding equals count.**
>
> Under the typed bridge, the contour integral equals \(2\pi i\) times the
> multiplicity-counting function.
>
> **In Lean:**
>
> ```lean
> theorem RiemannArgumentPrinciple.contour_winding_equals_count_of_safe
>     {T : ℝ} (hT : 0 < T) (hSafe : IsSafeHeight T)
>     (hBridge : ArgumentPrincipleBridge T) :
>     ContourWindingEqualsCount T
> ```

> **Theorem 3. Winding index = +1 for interior zeros.**
>
> **In Lean:**
>
> ```lean
> theorem RiemannArgumentPrinciple.contour_winding_index_one_of_safe
>     {T : ℝ} (hT : 0 < T) (hSafe : IsSafeHeight T)
>     (hBridge : ArgumentPrincipleBridge T) :
>     ContourWindingIndexOne T
> ```

> **Theorem 4. Residue sum equals multiplicity count.**
>
> **In Lean:**
>
> ```lean
> theorem RiemannArgumentPrinciple.contour_residue_sum_equals_N_of_safe
>     {T : ℝ} (hT : 0 < T) (hSafe : IsSafeHeight T)
>     (hBridge : ArgumentPrincipleBridge T) :
>     ContourResidueSumEqualsN T
> ```

---

## VI. Architecture

```text
Basic -> Contour -> Counting
```

- `Basic` -- entire Xi, critical box, nontrivial zeros, safe heights, multiplicity
- `Contour` -- four edge parametrisations, contour/rectangle integral identity
- `Counting` -- `ArgumentPrincipleBridge`, conditional winding = count theorems

The mathematical spine:

```text
entireXiContourIntegral T = sum of four edge integrals
    = criticalBoxRectangleIntegral entireXiLogDeriv T   [unconditional]
    = 2πi * zeroCountingWithMultiplicity T               [conditional on bridge]
```

---

## VII. Axiom Certificate

```text
printf 'import XiArgumentPrinciple
#print axioms RiemannArgumentPrinciple.entireXiContourIntegral_eq_rectangleIntegral
#print axioms RiemannArgumentPrinciple.contour_winding_equals_count_of_safe
' | lake env lean --stdin
```

'RiemannArgumentPrinciple.entireXiContourIntegral_eq_rectangleIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]

---

## VIII. Verification

```text
lake env lean XiArgumentPrinciple/XiArgumentPrincipleLive/XiArgumentPrinciple.live.lean
lake build XiArgumentPrinciple
```
