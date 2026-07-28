/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import MertensPNT.Connections

set_option linter.style.setOption false
set_option maxHeartbeats 800000

/-!
# Conditional PNT+ frontier

This file states the second theorem of Mertens and residual-rate frontiers as
`Prop`s and proves the conditional Euler-product closure from those hypotheses.
-/

/-! ### From `ErdosReciprocals/PNTFrontier.lean` -/

/-!
# Frontera PNT+ — puente Mathlib y cierre condicional de `Δ(n) → 0`

## Inventario Mathlib (este proyecto)

| Disponible ahora | Fuente |
|------------------|--------|
| `θ`, `ψ`, cotas Chebyshev | `Mathlib.NumberTheory.Chebyshev` |
| `π(n)` vs `θ/log` + integral (Abel) | `Chebyshev.primeCounting_eq_theta_div_log_add_integral` |
| `π =O(x/log²)` | `Chebyshev.primeCounting_sub_theta_div_log_isBigO` |
| Cota asintótica `π(x) ≤ (log 4 + ε)x/log x` | `Chebyshev.eventually_primeCounting_le` |
| `∑ 1/p` diverge (Erdős) | `Nat.Primes.not_summable_one_div` |
| `H_n - log n → γ` | `Real.tendsto_harmonic_sub_log` |

## Fuera de Mathlib (proyecto externo)

El PNT con términos de error está en
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
(`MediumPNT.lean`, tasa `O(x exp(-c√log x))` y variantes).

`MertensSecondTheorem` se instancia en `PNTClosure.lean` vía
`PrimeNumberTheoremAnd.IEANTN.Mertens` (`E₂p → 0`, `M = mertensConstant`).
La tasa `|Δ| ≤ C/log n` se instancia en lake `PNTRate.lean` (`C = log 4 + 6 + E₁`);
Rosser–Schoenfeld fuerte (`O(1/log²)` cola Meissel; término `θ` en `O(1/log³)`) en
lake `PNTRateStrong.lean`.

## Escalera hacia `Δ → 0`

1. **Hoy (Tier 0):** identidades exactas `log(∏·log n) = C(n) - Δ(n) - M`; correcciones `C → M`.
2. **Chebyshev (Tier 1):** `S(n) ≥ π(n)/n`; `∑(log p)/p ≤ θ(n)/2 ≤ (log 4)n/2`.
3. **Hipótesis Mertens (Tier 2):** `S(n) = log log n + M + o(1)` ⟺ `Δ → 0`.
4. **PNT+ importado (Tier 3):** tasa `|Δ(n)| ≤ C/log n` desde PrimeNumberTheoremAnd →
   `|Δ·log n| ≤ C`, `∏·log n → e^{-γ}` una vez `Δ → 0`.

Este archivo formaliza los pasos 2–3 y el **cierre condicional** del ciclo Euler una vez
`Δ → 0` está disponible.
-/

@[expose] public section

namespace ErdosReciprocals

open scoped Topology Chebyshev
open Filter Real

/-!
## Tier 1 — Puentes Chebyshev ↔ definiciones del proyecto
-/

/-- Reexportación del puente ya demostrado: `∑(log p)/p ≤ θ(n)/2`. -/
theorem partialLogSum_chebyshev_bridge (n : ℕ) :
    partialLogSum n ≤ θ n / 2 :=
  partialLogSum_le_half_theta n

/-- Reexportación: `S(n) ≥ π(n)/n` (minoración tipo Chebyshev para recíprocos). -/
theorem partialSum_primeCounting_bridge {n : ℕ} (hn : 0 < n) :
    (Nat.primeCounting n : ℝ) / n ≤ partialSum n :=
  partialSum_ge_primeCounting_div hn

/-- Versión asintótica de Chebyshev para `π` en la variable real `x`. -/
theorem eventually_primeCounting_upper_bound_real (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (log 4 + ε) * x / log x :=
  Chebyshev.eventually_primeCounting_le hε

/-!
## Tier 2 — Hipótesis del segundo teorema de Mertens (PNT+)
-/

/-- Segundo teorema de Mertens en la normalización del proyecto:
    `S(n) - log log n → M`. -/
def MertensSecondTheorem : Prop :=
  Tendsto (fun n : ℕ => partialSum n - log (log n)) atTop (𝓝 mertensConstant)

/-- Forma residual: `Δ(n) → 0`. -/
def MertensResidualVanishes : Prop :=
  Tendsto mertensResidual atTop (𝓝 0)

/-- Tasa PNT+ estándar: `|Δ(n)| ≤ C/log n` eventualmente. -/
def MertensResidualBigOInvLog (C : ℝ) : Prop :=
  ∀ᶠ n in atTop, |mertensResidual n| ≤ C / log n

/-- Término `θ` en la identidad Meissel–Mertens: `(θ n - n) / (n log n)`. -/
noncomputable def mertensThetaMeisselTerm (n : ℕ) : ℝ :=
  (θ (n : ℝ) - n) / (n * log n)

/-- Tasa Rosser–Schoenfeld (término `θ`): `|(θ n-n)/(n log n)| ≤ C/log³ n` eventualmente.

La cola integral Meissel es `O(1/log² n)`; el residual completo está en
`MertensResidualBigOInvLogSquared`. Instanciación en lake `PNTRateStrong.lean`. -/
def MertensResidualBigOInvLogCubed (C : ℝ) : Prop :=
  ∀ᶠ n in atTop, |mertensThetaMeisselTerm n| ≤ C / log n ^ 3

/-- Tasa Rosser–Schoenfeld completa (identidad Meissel + PNT medio): `|Δ(n)| ≤ C/log² n`. -/
def MertensResidualBigOInvLogSquared (C : ℝ) : Prop :=
  ∀ᶠ n in atTop, |mertensResidual n| ≤ C / log n ^ 2

/-- Cota uniforme Rosser–Schoenfeld: `|Δ(n)| ≤ C` para todo `n ≥ 2` (no decay). -/
def MertensResidualUniformlyBounded (C : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → |mertensResidual n| ≤ C

/-- Constante explícita de referencia (PNTA / Goldmakher):
    `C = log 4 + 6 + (5·log 2 + 3)/4`. Instanciación demostrada en lake `PNTRate.lean`. -/
noncomputable def mertensResidualErrorConstantExplicit : ℝ :=
  log 4 + 6 + (5 * log 2 + 3) / 4

lemma mertensResidual_eq_sub (n : ℕ) :
    mertensResidual n = partialSum n - log (log n) - mertensConstant := by
  simp only [mertensResidual, mertensApprox, sub_add_eq_sub_sub]

lemma partialSum_sub_loglog_eq_mertensResidual_add (n : ℕ) :
    partialSum n - log (log n) = mertensResidual n + mertensConstant := by
  simp [mertensResidual, mertensApprox]; ring

/-- Las dos formulaciones de Mertens son equivalentes (definición de `mertensResidual`). -/
theorem mertens_second_theorem_iff_residual_vanishes :
    MertensSecondTheorem ↔ MertensResidualVanishes := by
  constructor
  · intro h
    dsimp only [MertensResidualVanishes]
    have hfun :
        mertensResidual = fun n => partialSum n - log (log n) - mertensConstant :=
      funext mertensResidual_eq_sub
    rw [hfun]
    simpa using h.sub_const mertensConstant
  · intro h
    dsimp only [MertensResidualVanishes] at h
    dsimp only [MertensSecondTheorem]
    have hfun :
        (fun n => partialSum n - log (log n)) =
          fun n => mertensResidual n + mertensConstant :=
      funext partialSum_sub_loglog_eq_mertensResidual_add
    rw [hfun]
    simpa using h.add_const mertensConstant

/-- Si `|Δ| ≤ C/log n` eventualmente, el residual escalado queda acotado por `C`.

Nota: `Δ → 0` no implica `Δ·log n → 0` (contraejemplo `Δ(n) = 1/log n`). -/
theorem mertensScaledResidual_bounded_of_bigO (C : ℝ) (h : MertensResidualBigOInvLog C) :
    ∀ᶠ n in atTop, |mertensScaledResidual n| ≤ C := by
  filter_upwards [h, eventually_ge_atTop 3] with n hn hn3
  dsimp [mertensScaledResidual]
  have hlog : 0 < log n := log_pos (mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hn3))
  rw [abs_mul, abs_of_pos hlog]
  calc
    |mertensResidual n| * log n ≤ (C / log n) * log n := by gcongr
    _ = C := by field_simp [hlog.ne']

/-!
## Tier 3 — Cierre condicional del ciclo Euler (dado `Δ → 0`)
-/

/-- Si `Δ → 0` y las correcciones convergen (ya demostrado), entonces
    `log(∏_{p≤n}(1-1/p) · log n) → -γ`. -/
theorem tendsto_log_partialEulerProductScaled_neg_gamma_of_residual_vanishes
    (hΔ : MertensResidualVanishes) :
    Tendsto (fun n : ℕ => log (partialEulerProductScaled n)) atTop
      (𝓝 (-eulerMascheroniConstant)) := by
  have h_ev :
      ∀ᶠ n in atTop, log (partialEulerProductScaled n) =
        partialMertensCorrection n - mertensResidual n - mertensConstant :=
    (eventually_ge_atTop 2).mono fun n hn => log_partialEulerProductScaled_eq hn
  have hlim :
      Tendsto (fun n : ℕ => partialMertensCorrection n - mertensResidual n - mertensConstant) atTop
        (𝓝 (mertensPrimeCorrectionSum - mertensConstant)) := by
    simpa [sub_zero] using
      (partialMertensCorrection_tendsto_atTop.sub hΔ).sub_const mertensConstant
  have htarget :
      mertensPrimeCorrectionSum - mertensConstant = -eulerMascheroniConstant := by
    rw [mertensConstant_eq_gamma_add_correctionSum]
    ring
  exact (Tendsto.congr' (EventuallyEq.symm h_ev) hlim).trans (by rw [htarget])

/-- Corolario multiplicativo: `∏_{p≤n}(1-1/p) · log n → e^{-γ}` (condicional a `Δ → 0`). -/
theorem tendsto_partialEulerProductScaled_exp_neg_gamma_of_residual_vanishes
    (hΔ : MertensResidualVanishes) :
    Tendsto partialEulerProductScaled atTop (𝓝 (Real.exp (-eulerMascheroniConstant))) := by
  have hlog := tendsto_log_partialEulerProductScaled_neg_gamma_of_residual_vanishes hΔ
  have hpos_ev :
      ∀ᶠ n in atTop, 0 < partialEulerProductScaled n :=
    (eventually_ge_atTop 2).mono fun n hn => by
      unfold partialEulerProductScaled
      exact mul_pos (partialProduct_pos hn) (log_pos (mod_cast (one_lt_of_two_le hn)))
  have hexp := ((continuous_exp).tendsto _).comp hlog
  refine Tendsto.congr' (EventuallyEq.symm ?_) hexp
  filter_upwards [hpos_ev] with n hn
  simp only [Function.comp_apply, Real.exp_log hn]

/-!
## Mapa de dependencias externas (documentación ejecutable)

| Objetivo PNT+ | Estado |
|---------------|--------|
| `MertensSecondTheorem` | hipótesis (web); **demostrado** en lake `PNTClosure.lean` |
| `MertensResidualVanishes` | equivalente; cierre Euler condicional |
| `∏·log n → e^{-γ}` | condicional a `MertensSecondTheorem` (lake: incondicional) |
| Tasa `|Δ| ≤ C/log n` | **demostrado** en lake `PNTRate.lean` |
| Tasa RS término `θ`: `|·| ≤ C/log³ n` | **demostrado** en lake `PNTRateStrong.lean` |
| Tasa RS `|Δ| ≤ C/log² n` | **demostrado** en lake `PNTRateStrong.lean` |
| Cota uniforme RS `|Δ| ≤ C` | **demostrado** en lake `PNTRateStrong.lean` |
-/

/-- Punto de anclaje: bajo PNT+ (como `MertensSecondTheorem`), el residual desaparece. -/
theorem mertens_residual_vanishes_of_second_theorem (h : MertensSecondTheorem) :
    MertensResidualVanishes :=
  mertens_second_theorem_iff_residual_vanishes.mp h

/-- Cadena condicional completa hacia la heurística Tao `∏·log n ~ e^{-γ}`. -/
theorem tendsto_partialEulerProductScaled_exp_neg_gamma_of_second_theorem
    (h : MertensSecondTheorem) :
    Tendsto partialEulerProductScaled atTop (𝓝 (Real.exp (-eulerMascheroniConstant))) :=
  tendsto_partialEulerProductScaled_exp_neg_gamma_of_residual_vanishes
    (mertens_residual_vanishes_of_second_theorem h)

/-- Resumen ejecutable del cierre PNT+ condicional (un solo punto de entrada). -/
theorem mertens_euler_closure_conditional
    (hMertens : MertensSecondTheorem) :
    MertensResidualVanishes ∧
      Tendsto (fun n : ℕ => log (partialEulerProductScaled n)) atTop
        (𝓝 (-eulerMascheroniConstant)) ∧
      Tendsto partialEulerProductScaled atTop (𝓝 (Real.exp (-eulerMascheroniConstant))) := by
  refine ⟨mertens_residual_vanishes_of_second_theorem hMertens, ?_, ?_⟩
  · exact tendsto_log_partialEulerProductScaled_neg_gamma_of_residual_vanishes
      (mertens_residual_vanishes_of_second_theorem hMertens)
  · exact tendsto_partialEulerProductScaled_exp_neg_gamma_of_second_theorem hMertens

/-- Si además `|Δ| ≤ C/log n`, el residual escalado queda acotado (no necesariamente → 0). -/
theorem mertens_scaled_residual_bounded_of_second_theorem_and_bigO
    (_hMertens : MertensSecondTheorem) (C : ℝ) (hO : MertensResidualBigOInvLog C) :
    ∀ᶠ n in atTop, |mertensScaledResidual n| ≤ C :=
  mertensScaledResidual_bounded_of_bigO C hO

end ErdosReciprocals

end
