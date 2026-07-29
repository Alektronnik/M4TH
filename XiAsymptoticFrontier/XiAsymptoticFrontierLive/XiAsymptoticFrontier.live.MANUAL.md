# XiAsymptoticFrontier

**A single-file live presentation of the typed analytic frontier for the
Riemann-von Mangoldt contour synthesis, formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Perez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0
- Companion file: `XiAsymptoticFrontier.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`XiAsymptoticFrontier.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

Once the argument principle counts the zeros, the next question is: why is the
count asymptotic to the von Mangoldt main term

$$
\frac{T}{2\pi}\Bigl(\log\frac{T}{2\pi} - 1\Bigr)?
$$

The answer is a bookkeeping of contour contributions.  The contour integral
splits into named pieces -- near-origin, polynomial horizontal/vertical, gamma
horizontal/vertical, zeta horizontal/vertical -- and the typed frontier records
which pieces are negligible and which supplies the main term.

The package proves the conditional synthesis: if the typed `AnalyticFrontier`
holds, then the multiplicity counting function is equivalent at infinity to the
von Mangoldt main term.

---

## II. The Von Mangoldt Main Term

> **Definition 1. Classical von Mangoldt main term.**
>
> $$
> N(T) \sim \frac{T}{2\pi}\Bigl(\log\frac{T}{2\pi} - 1\Bigr).
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def RiemannAsymptoticFrontier.vonMangoldtMainTerm (T : ℝ) : ℝ :=
>   (T / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1)
> ```

> **Definition 2. Abstract zero-counting function.**
>
> **In Lean:**
>
> ```lean
> abbrev RiemannAsymptoticFrontier.ZeroCountingFunction := ℝ → ℝ
> ```

---

## III. Contour Components

> **Definition 3. Contour components.**
>
> The boundary integral splits into seven named pieces.
>
> **In Lean:**
>
> ```lean
> structure RiemannAsymptoticFrontier.ContourComponents where
>   origin : ℝ → ℝ
>   polynomialHorizontal : ℝ → ℝ
>   polynomialVertical : ℝ → ℝ
>   gammaHorizontal : ℝ → ℝ
>   gammaVertical : ℝ → ℝ
>   zetaHorizontal : ℝ → ℝ
>   zetaVertical : ℝ → ℝ
> ```

> **Definition 4. Residual and reconstruction.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ContourComponents.residual (C : ContourComponents) : ℝ → ℝ :=
>   fun T => C.origin T + C.polynomialHorizontal T + C.polynomialVertical T +
>     C.gammaVertical T + C.zetaHorizontal T + C.zetaVertical T
>
> def ContourComponents.reconstructs (C : ContourComponents) (N : ZeroCountingFunction) : Prop :=
>   ∀ᶠ T in atTop, N T = C.gammaHorizontal T + C.residual T
> ```

---

## IV. The Typed Analytic Frontier

> **Definition 5. Analytic frontier.**
>
> Seven explicit fields capture exactly which contour contributions are
> negligible and which supplies the main term.
>
> **In Lean:**
>
> ```lean
> structure RiemannAsymptoticFrontier.AnalyticFrontier
>     (N Nsafe : ZeroCountingFunction) (C : ContourComponents) : Prop where
>   reconstructs_safe : C.reconstructs Nsafe
>   near_origin : NearOriginNegligible C
>   polynomial : PolynomialContourNegligible C
>   gamma_horizontal : GammaHorizontalStirlingGoal C
>   gamma_vertical : GammaVerticalEdgesNegligible C
>   zeta_edges : ZetaEdgesNegligible C
>   safe_height_counting : SafeHeightCountingEquivalent N Nsafe
> ```

The seven fields express:

| Field | Meaning |
|---|---|
| `reconstructs_safe` | The safe-height count is built from gamma + residual |
| `near_origin` | The near-origin block is negligible |
| `polynomial` | Polynomial contour contributions are negligible |
| `gamma_horizontal` | Gamma horizontal/Stirling supplies the main term |
| `gamma_vertical` | Gamma vertical edges are negligible |
| `zeta_edges` | Zeta horizontal and vertical edges are negligible |
| `safe_height_counting` | Safe-height compression N ~ Nsafe |

> **Lemma 1. Residual negligibility.**
>
> If the individual negligibility fields hold, the total residual is `o` of
> the main term.
>
> **In Lean:**
>
> ```lean
> lemma RiemannAsymptoticFrontier.residual_negligible {C : ContourComponents}
>     (hOrigin : NearOriginNegligible C) (hPoly : PolynomialContourNegligible C)
>     (hGammaVert : GammaVerticalEdgesNegligible C)
>     (hZeta : ZetaEdgesNegligible C) :
>     C.residual =o[atTop] vonMangoldtMainTerm
> ```

---

## V. The Conditional Synthesis Theorem

> **Theorem 1. Safe-height counting follows the main term.**
>
> **In Lean:**
>
> ```lean
> theorem RiemannAsymptoticFrontier.safe_counting_equiv_main
>     {Nsafe : ZeroCountingFunction} {C : ContourComponents}
>     (hReconstruct : C.reconstructs Nsafe)
>     (hGamma : GammaHorizontalStirlingGoal C)
>     (hResidual : C.residual =o[atTop] vonMangoldtMainTerm) :
>     IsEquivalent atTop Nsafe vonMangoldtMainTerm
> ```

> **Theorem 2. Riemann-von Mangoldt from contour frontier.**
>
> Under the typed `AnalyticFrontier`, the counting function is equivalent
> to the von Mangoldt main term.
>
> **In Lean:**
>
> ```lean
> theorem RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_frontier
>     {N Nsafe : ZeroCountingFunction} {C : ContourComponents}
>     (h : AnalyticFrontier N Nsafe C) :
>     RiemannVonMangoldtMultiplicityCounting N
> ```

> **Theorem 3. Point-free Prop form.**
>
> **In Lean:**
>
> ```lean
> theorem RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_bridge :
>     RiemannVonMangoldtFromContourFrontier
> ```

---

## VI. Architecture

```text
Basic -> Frontier -> Synthesis
```

- `Basic` -- von Mangoldt main term, asymptotic API, contour normalisation
- `Frontier` -- `ContourComponents`, `AnalyticFrontier` (7 fields), residual lemma
- `Synthesis` -- conditional safe-height theorem, main synthesis theorem

---

## VII. Axiom Certificate

```text
printf 'import XiAsymptoticFrontier
#print axioms RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_frontier
#print axioms RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_bridge
' | lake env lean --stdin
```

Expected: `[propext, Classical.choice, Quot.sound]`

---

## VIII. Verification

```text
lake env lean XiAsymptoticFrontier/XiAsymptoticFrontierLive/XiAsymptoticFrontier.live.lean
lake build XiAsymptoticFrontier
```
