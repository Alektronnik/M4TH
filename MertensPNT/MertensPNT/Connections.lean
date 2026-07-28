/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import MertensPNT.TTAOData

set_option linter.style.setOption false
set_option maxHeartbeats 800000

/-!
# Connections and residual layer

This file connects the Erdos subsequence, product bridge, empirical tables, and
the residual definitions used at the PNT+ frontier.
-/

/-! ### From `ErdosReciprocals/Connections.lean` -/

/-!
# Conexiones entre capas

Teoremas compuestos que enlazan bloques Erdős con Chebyshev, log-sum y producto.
-/

@[expose] public section

namespace ErdosReciprocals

open scoped Topology
open Filter Real

lemma two_le_erdosBlockEnd (k : ℕ) : 2 ≤ erdosBlockEnd k := by
  unfold erdosBlockEnd
  have hexp : 1 ≤ k.primesBelow.card + 1 := Nat.succ_le_succ (Nat.zero_le _)
  exact (by decide : 2 ≤ 4 ^ 1).trans (Nat.pow_le_pow_right (by norm_num) hexp)

lemma two_le_erdosIter {t : ℕ} (ht : t ≠ 0) : 2 ≤ erdosIter t := by
  rcases t with _ | t
  · exact absurd rfl ht
  · simpa [erdosIter] using two_le_erdosBlockEnd (erdosIter t)

lemma one_lt_erdosIter {t : ℕ} (ht : t ≠ 0) : 1 < erdosIter t :=
  Nat.lt_of_lt_of_le (by decide : 1 < 2) (two_le_erdosIter ht)

/-- Testigo constructivo de divergencia: `S(erdosIter t)` supera cualquier umbral. -/
theorem exists_partialSum_gt_erdosIter (M : ℝ) : ∃ t, M ≤ partialSum (erdosIter t) := by
  by_cases hM : M ≤ 0
  · refine ⟨0, ?_⟩
    simpa [erdosIter, partialSum_zero] using hM
  · rcases exists_nat_gt (2 * M) with ⟨t, ht⟩
    have ht' : (2 * M : ℝ) < t := mod_cast ht
    have hden : (0 : ℝ) < 2 := by norm_num
    have hM' : M < (t : ℝ) / 2 := by
      have h1 : M = (2 * M) / 2 := by ring
      rw [h1]
      gcongr
    exact ⟨t, (le_of_lt hM').trans (partialSum_erdosIter_ge_half_mul t)⟩

/-- La subsecuencia `S(erdosIter t)` diverge (prueba directa, sin summability). -/
theorem tendsto_partialSum_comp_erdosIter :
    Tendsto (fun t : ℕ => partialSum (erdosIter t)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  rcases exists_partialSum_gt_erdosIter M with ⟨t, ht⟩
  refine ⟨t, fun s hs => ht.trans (partialSum_mono (erdosIter_mono hs))⟩

/-- En puntos Erdős: `∑ (log p)/p` minorada por `log 2 · t/2`. -/
theorem partialLogSum_erdosIter_ge_log2_half_mul (t : ℕ) :
    log 2 * ((t : ℝ) / 2) ≤ partialLogSum (erdosIter t) := by
  calc
    log 2 * ((t : ℝ) / 2)
        ≤ log 2 * partialSum (erdosIter t) := by gcongr; exact partialSum_erdosIter_ge_half_mul t
    _ ≤ partialLogSum (erdosIter t) := partialLogSum_ge_log_two_mul_partialSum _

/-- En puntos Erdős: `∑ (log p)/p` acotada por `log 4 · erdosIter t / 2`. -/
theorem partialLogSum_erdosIter_le_log4_half_mul (t : ℕ) :
    partialLogSum (erdosIter t) ≤ log 4 / 2 * erdosIter t := by
  simpa using partialLogSum_le_log4_mul_n (erdosIter t)

/-- En puntos Erdős: el producto cae al menos como `exp(-t/2)`. -/
theorem partialProduct_erdosIter_le_exp_neg_half_mul {t : ℕ} (ht : t ≠ 0) :
    partialProduct (erdosIter t) ≤ exp (-((t : ℝ) / 2)) := by
  have h2 := two_le_erdosIter ht
  calc
    partialProduct (erdosIter t)
        ≤ exp (-partialSum (erdosIter t)) := partialProduct_le_exp_neg_partialSum h2
    _ ≤ exp (-((t : ℝ) / 2)) :=
      exp_monotone (neg_le_neg (partialSum_erdosIter_ge_half_mul t))

/-- Cota fina del producto en puntos Erdős: `∏ ≤ exp(corrección - t/2)`. -/
theorem partialMertensCorrection_comp_erdosIter_tendsto :
    Tendsto (fun t : ℕ => partialMertensCorrection (erdosIter t)) atTop
      (𝓝 mertensPrimeCorrectionSum) :=
  partialMertensCorrection_tendsto_atTop.comp tendsto_erdosIter_atTop

/-- En puntos Erdős: `∏ · exp(S) → exp(∑' corrections)`. -/
theorem tendsto_partialProduct_mul_exp_partialSum_comp_erdosIter :
    Tendsto (fun t : ℕ => partialProduct (erdosIter t) * exp (partialSum (erdosIter t))) atTop
      (𝓝 (exp mertensPrimeCorrectionSum)) :=
  tendsto_partialProduct_mul_exp_partialSum.comp tendsto_erdosIter_atTop

/-- En puntos Erdős: el producto parcial tiende a `0`. -/
theorem partialProduct_comp_erdosIter_tendsto_zero :
    Tendsto (fun t : ℕ => partialProduct (erdosIter t)) atTop (𝓝 0) :=
  partialProduct_tendsto_zero.comp tendsto_erdosIter_atTop

/-- Misma convergencia en la subsecuencia Erdős `erdosIter t → ∞`. -/
theorem erdos_product_convergence :
    Tendsto (fun t => partialMertensCorrection (erdosIter t)) atTop
        (𝓝 mertensPrimeCorrectionSum) ∧
      Tendsto (fun t => partialProduct (erdosIter t) * exp (partialSum (erdosIter t))) atTop
        (𝓝 (exp mertensPrimeCorrectionSum)) ∧
      Tendsto (fun t => partialProduct (erdosIter t)) atTop (𝓝 0) :=
  ⟨partialMertensCorrection_comp_erdosIter_tendsto,
    tendsto_partialProduct_mul_exp_partialSum_comp_erdosIter,
    partialProduct_comp_erdosIter_tendsto_zero⟩

theorem partialProduct_erdosIter_le_exp_correction_sub_half_mul {t : ℕ} (ht : t ≠ 0) :
    partialProduct (erdosIter t) ≤
      exp (partialMertensCorrection (erdosIter t) - (t : ℝ) / 2) := by
  have h2 := two_le_erdosIter ht
  rw [partialProduct_eq_exp_partialMertensCorrection_sub_partialSum h2]
  gcongr
  exact partialSum_erdosIter_ge_half_mul t

/-- Cota de tasa uniforme: `∏(erdosIter t) ≤ exp(B - t/2)` eventualmente. -/
theorem partialProduct_erdosIter_eventually_le_exp_sub_half_mul :
    ∃ B, ∀ᶠ t in atTop,
      partialProduct (erdosIter t) ≤ exp (B - (t : ℝ) / 2) := by
  rcases partialMertensCorrection_bddAbove with ⟨B, hB⟩
  refine ⟨B, ((eventually_ge_atTop 1).mono fun t ht => by omega).mono fun t ht => ?_⟩
  have ht' : t ≠ 0 := by omega
  calc
    partialProduct (erdosIter t)
        ≤ exp (partialMertensCorrection (erdosIter t) - (t : ℝ) / 2) :=
      partialProduct_erdosIter_le_exp_correction_sub_half_mul ht'
    _ ≤ exp (B - (t : ℝ) / 2) := by
      gcongr
      exact hB ⟨erdosIter t, rfl⟩

/-- En puntos Erdős con `t ≠ 0`: minoración Chebyshev de `S(n)` vía `π(n)/n`. -/
theorem partialSum_erdosIter_ge_primeCounting_ratio {t : ℕ} (ht : t ≠ 0) :
    (Nat.primeCounting (erdosIter t) : ℝ) / erdosIter t ≤ partialSum (erdosIter t) := by
  have hn0 : 0 < erdosIter t := Nat.zero_lt_of_lt (one_lt_erdosIter ht)
  exact partialSum_ge_primeCounting_div hn0

/-- En puntos Erdős con `t ≠ 0`: minoración explícita tipo Chebyshev. -/
theorem partialSum_erdosIter_ge_chebyshev_ratio {t : ℕ} (ht : t ≠ 0) :
    ((erdosIter t * log 2 - log (erdosIter t + 1)) / log (erdosIter t)) / erdosIter t ≤
      partialSum (erdosIter t) :=
  partialSum_ge_chebyshev_ratio (one_lt_erdosIter ht)

/-- Cadena Erdős → log-sum → Chebyshev en la subsecuencia `erdosIter`. -/
theorem erdos_logsum_chebyshev_chain {t : ℕ} (ht : t ≠ 0) :
    log 2 * ((t : ℝ) / 2) ≤ partialLogSum (erdosIter t) ∧
      partialLogSum (erdosIter t) ≤ log 4 / 2 * erdosIter t ∧
        (Nat.primeCounting (erdosIter t) : ℝ) / erdosIter t ≤ partialSum (erdosIter t) :=
  ⟨partialLogSum_erdosIter_ge_log2_half_mul t,
    partialLogSum_erdosIter_le_log4_half_mul t,
    partialSum_erdosIter_ge_primeCounting_ratio ht⟩

end ErdosReciprocals

/-! ### From `ErdosReciprocals/Mertens.lean` -/

/-!
# Teoremas de Mertens: definiciones y base formal

## Frontera rigurosa actual (pruebas completas, sin PNT)

| Capa | Resultado |
|------|-----------|
| Elemental | `1/2 ≤ S(n) ≤ H_n ≤ 1 + log n` |
| Erdős | bloques `≥ 1/2`; `S(erdosIter t) ≥ t/2`; `¬ Summable (1/p)` |
| Conexiones | subsecuencia `erdosIter`: log-sum, producto, Chebyshev encadenados |
| Crecimiento | `erdosIter → ∞`; `log log(erdosIter t)` vs `S(erdosIter t) ≥ t/2` |
| Puente Mertens | `mertens_product_convergence`; `∏·exp(S+γ)→exp(M)`; `log(∏·log n)=C-Δ-M` |
| Asintótica unilateral | `S(n) - log n < γ + ε` eventualmente |
| Chebyshev | `∑ (log p)/p ≤ (log 4)·n/2`; `S(n) ≥ π(n)/n` |
| Log-sum | `log 2 · S(n) ≤ ∑ (log p)/p ≤ log n · S(n)`; Chebyshev vía `S` |
| Producto | `∏(1-1/p) ≤ exp(-S(n))` |
| Zeta prima | `∑_p p^r` converge ⟺ `r < -1` |
| Mertens (def.) | `M = γ + ∑'_p (log(1-1/p)+1/p)` summable |
| TTAO empírico | 3 escalas; low: `Δ_proxy` ↓; high/millions: ventana local |
| Residual `Δ` | `Δ ≤ H_n - log log - M`; proxy TTAO; PNT+: `Δ → 0` |

## Objetivo PNT+ (#1330) — aún no en Mathlib

* `S(n) = log log n + M + O(1/log n)`
* `∑_{p≤n} (log p)/p = log n + O(1)`
* `∏_{p≤n} (1-1/p) ~ e^{-γ}/log n`
* `Tendsto mertensScaledResidual atTop (𝓝 _)`
-/

namespace ErdosReciprocals

open scoped Topology
open Filter Real

/-- Aproximación principal de Mertens segundo teorema: `log log n + M`. -/
noncomputable def mertensApprox (n : ℕ) : ℝ :=
  log (log n) + mertensConstant

/-- Residual `Δ(n) = S(n) - (log log n + M)`. -/
noncomputable def mertensResidual (n : ℕ) : ℝ :=
  partialSum n - mertensApprox n

/-- Residual escalado `Δ(n) · log n` (término `O(1/log n)` de Mertens). -/
noncomputable def mertensScaledResidual (n : ℕ) : ℝ :=
  mertensResidual n * log n

/-- Producto de Euler escalado: `∏_{p≤n}(1-1/p) · log n` (heurística Tao: `→ e^{-γ}` con PNT+). -/
noncomputable def partialEulerProductScaled (n : ℕ) : ℝ :=
  partialProduct n * log n

theorem mertensResidual_eq_partialSum_sub_loglog_sub_mertensConstant (n : ℕ) :
    mertensResidual n = partialSum n - log (log n) - mertensConstant := by
  unfold mertensResidual mertensApprox
  ring

/-- Identidad exacta: `∏ = exp(C - (log log n + M) - Δ)`. -/
theorem partialProduct_eq_exp_correction_sub_mertensApprox_sub_residual {n : ℕ} (hn : 2 ≤ n) :
    partialProduct n =
      exp (partialMertensCorrection n - mertensApprox n - mertensResidual n) := by
  rw [partialProduct_eq_exp_partialMertensCorrection_sub_partialSum hn]
  congr 1
  simp only [mertensApprox, mertensResidual]
  ring

lemma one_lt_of_two_le {n : ℕ} (hn : 2 ≤ n) : 1 < n :=
  lt_of_lt_of_le (by decide : 1 < 2) hn

/-- Identidad exacta del escalado logarítmico (puente hacia `∏·log n ~ e^{-γ}`). -/
theorem log_partialEulerProductScaled_eq {n : ℕ} (hn : 2 ≤ n) :
    log (partialEulerProductScaled n) =
      partialMertensCorrection n - mertensResidual n - mertensConstant := by
  unfold partialEulerProductScaled
  have hprod := partialProduct_pos hn
  have hlogn : 0 < log n := log_pos (mod_cast (one_lt_of_two_le hn))
  have hlog :
      log (partialProduct n) = partialMertensCorrection n - partialSum n := by
    linarith [log_partialProduct_add_partialSum_eq_partialMertensCorrection n]
  rw [log_mul (ne_of_gt hprod) (ne_of_gt hlogn), hlog]
  simp only [mertensResidual, mertensApprox]
  linarith

theorem partialEulerProductScaled_eq_exp {n : ℕ} (hn : 2 ≤ n) :
    partialEulerProductScaled n =
      exp (partialMertensCorrection n - mertensResidual n - mertensConstant) := by
  have hpos : 0 < partialEulerProductScaled n := by
    unfold partialEulerProductScaled
    exact mul_pos (partialProduct_pos hn) (log_pos (mod_cast (one_lt_of_two_le hn)))
  rw [← exp_log hpos, log_partialEulerProductScaled_eq hn]

/-- `log log n` diverge. -/
theorem tendsto_log_log_atTop :
    Tendsto (fun n : ℕ => log (log n)) atTop atTop := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto log atTop atTop := tendsto_log_atTop
  exact tendsto_log_atTop.comp (hlog.comp hcast)

/-- `S(n)` no está acotada superiormente. -/
theorem partialSum_not_bddAbove : ¬ BddAbove (Set.range partialSum) := by
  intro h
  rcases h with ⟨C, hC⟩
  rcases exists_partialSum_gt C with ⟨n, hn⟩
  linarith [hC ⟨n, rfl⟩, hn]

/-- `S(n)` supera cualquier umbral real. -/
theorem partialSum_outgrows_any_fixed_bound (M : ℝ) : ∃ n, partialSum n > M :=
  exists_partialSum_gt M

/-- La aproximación numérica de referencia es positiva. -/
theorem mertensConstant_pos : 0 < mertensConstantApprox :=
  mertensConstantApprox_pos

/-- La constante γ de Euler-Mascheroni es positiva (Mathlib). -/
theorem eulerMascheroni_pos : 0 < eulerMascheroniConstant := by
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-!
### Cierre PNT+ condicional (`PNTFrontier.lean`)

Web: `mertens_euler_closure_conditional` en `PNTFrontier.lean` (dado `MertensSecondTheorem`).
Lake: cierre incondicional en `PNTClosure.lean` (`mertens_euler_closure`).
La tasa `|Δ| ≤ C/log n` queda como frontera externa.
-/

theorem tendsto_partialProduct_mul_exp_gamma_comp_erdosIter :
    Tendsto (fun t =>
        partialProduct (erdosIter t) * exp (partialSum (erdosIter t) + eulerMascheroniConstant))
      atTop (𝓝 (exp mertensConstant)) :=
  tendsto_partialProduct_mul_exp_partialSum_add_gamma.comp tendsto_erdosIter_atTop

end ErdosReciprocals

/-! ### From `ErdosReciprocals/MertensResidual.lean` -/

/-!
# Residual `Δ(n)` de Mertens: frontera formal y puente TTAO

Sin PNT+ no hay cota inferior uniforme de `Δ`; sí identidades exactas,
cota superior vía armónicos, y proxies empíricos en `TTAOData`.
-/

namespace ErdosReciprocals

open scoped Topology
open Filter Real

/-- Cota superior débil: `Δ(n) ≤ H_n - log log n - M` (sin tasa `O(1/log n)`). -/
theorem mertensResidual_le_harmonic_sub_loglog_sub_mertensConstant (n : ℕ) :
    mertensResidual n ≤ harmonic n - log (log n) - mertensConstant := by
  unfold mertensResidual mertensApprox
  linarith [partialSum_le_harmonic n]

/-- Cota inferior trivial desde `S(n) ≥ 1/2` (no informativa para PNT+). -/
theorem mertensResidual_ge_half_sub_loglog_sub_mertensConstant {n : ℕ} (hn : 2 ≤ n) :
    1 / 2 - log (log n) - mertensConstant ≤ mertensResidual n := by
  unfold mertensResidual mertensApprox
  linarith [partialSum_ge_one_half hn]

/-!
### Puente empírico TTAO — escala baja acumulativa (x = 104729)
-/

theorem taoCp104729_residualProxy_lt_thousandth' :
    taoCp104729_residualProxy < (1 / 1000 : ℝ) :=
  taoCp104729_residualProxy_lt_thousandth

theorem taoEmpirical_residual_tightens_on_low_from_2 :
    taoCp104729_residualProxy < taoCp7919_residualProxy :=
  taoResidualProxy_tightens_Cp7919_to_Cp104729

/-!
### Contraste de escalas (mensaje Tao §2)
-/

theorem taoLow_scale_prod_heuristic_valid :
    taoCp104729_prodOverHeuristic < (2 : ℝ) :=
  taoLow_prodOverHeuristic_near_one

theorem taoHigh10M_scale_prod_heuristic_invalid :
    (20 : ℝ) < taoHigh10M_Cp10160539_prodOverHeuristic :=
  taoHigh10M_prodOverHeuristic_gt_twenty

theorem taoMillions_scale_prod_heuristic_invalid :
    (20 : ℝ) < taoMillions_Cp9999991_prodOverHeuristic :=
  taoMillions_prodOverHeuristic_gt_twenty

theorem taoLow_scale_sum_minus_loglog_near_M :
    (1 / 4 : ℝ) < taoCp104729_sumMinusLogLog ∧
      taoCp104729_sumMinusLogLog < (1 / 2 : ℝ) :=
  taoLow_sumMinusLogLog_near_M

/-!
### Puente criba `mertens_table` (potencias de 10 → `10¹¹`)
-/

theorem criba_table_delta_tightens_empirically :
    cribaCp100000000000_delta < cribaCp1000_delta :=
  criba_empirical_delta_toward_zero

theorem criba_table_S_grows_to_1e11 :
    cribaCp1000_S < cribaCp100000000000_S :=
  criba_empirical_S_monotone_to_1e11

theorem criba_cross_tao_low_scale_consistent :
    cribaCp100000_S < taoCp104729_sumOneOverP :=
  cribaCp100000_S_lt_taoCp104729_sum

/-!
### Objetivo PNT+ (#1330)

  Web: cierre condicional en `PNTFrontier.lean` bajo `MertensSecondTheorem`.
  Lake: `MertensSecondTheorem` demostrado en `PNTClosure.lean` (PrimeNumberTheoremAnd).
  Tasa `|Δ| ≤ C/log n`: instanciada en lake `PNTRate.lean`
  (`mertensResidualBigOInvLog_explicit`, `C = log 4 + 6 + (5·log 2 + 3)/4`).
-/

end ErdosReciprocals

end
