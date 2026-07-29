/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order.OrderClosed

/-!
# MertensPNT live edition

Single-file live edition of the `MertensPNT` package for web certification and
study.  The mathematical content is the package source fused in dependency
order: `Basic`, `MertensConstant`, `ErdosBlocks`, `MertensBridge`, `TTAOData`,
`Connections`, and `PNTFrontier`.
-/


/-!
## Source file: `MertensPNT/Basic.lean`
-/

/-!
# Basic reciprocal-prime and elementary Erdos layer

This file contains the core definitions `partialSum`, `partialLogSum`,
`partialProduct`, elementary harmonic/product bounds, divergence of prime
reciprocals, Chebyshev bridges, and the first Erdos lemmas.
-/

/-! ### From `ErdosReciprocals/Basic.lean` -/

/-!
# Definiciones centrales de Mertens / Erdős

* `partialSum n`     — `S(n) = ∑_{p ≤ n} 1/p`
* `partialLogSum n`  — `∑_{p ≤ n} (log p)/p`
* `partialProduct n` — `∏_{p ≤ n} (1 - 1/p)`
-/

@[expose] public section

namespace ErdosReciprocals

open scoped BigOperators

/-- Coerción explícita `Nat.Primes → ℝ` (evita ambigüedades `↑↑p`). -/
def primeR (p : Nat.Primes) : ℝ :=
  (p.val : ℝ)

lemma primeR_pos (p : Nat.Primes) : 0 < primeR p := by
  unfold primeR
  exact_mod_cast p.property.pos

lemma one_lt_primeR (p : Nat.Primes) : 1 < primeR p := by
  unfold primeR
  exact_mod_cast p.property.one_lt

lemma two_le_primeR (p : Nat.Primes) : 2 ≤ primeR p := by
  unfold primeR
  exact_mod_cast p.property.two_le

/-- Término `1/p` en primos y `0` en compuestos. -/
noncomputable def primeReciprocalTerm : ℕ → ℝ :=
  Set.indicator {p | Nat.Prime p} (fun p => (1 : ℝ) / p)

lemma primeReciprocalTerm_nonneg (n : ℕ) : 0 ≤ primeReciprocalTerm n := by
  simpa [primeReciprocalTerm] using
    Set.indicator_nonneg (fun p _ => by positivity) n

lemma primeReciprocalTerm_eq_indicator :
    primeReciprocalTerm = Set.indicator {p | Nat.Prime p} (fun n : ℕ => (1 : ℝ) / n) := rfl

/-- Suma parcial `S(n) = ∑_{p ≤ n} 1/p`. -/
noncomputable def partialSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), primeReciprocalTerm k

/-- `∑_{p ≤ n} (log p)/p`. -/
noncomputable def partialLogSum (n : ℕ) : ℝ :=
  ((n + 1).primesBelow).sum (fun p => Real.log p / p)

/-- `∏_{p ≤ n} (1 - 1/p)`. -/
noncomputable def partialProduct (n : ℕ) : ℝ :=
  ((n + 1).primesBelow).prod (fun p => (1 - (1 : ℝ) / p))

lemma partialSum_eq_primesBelow_sum (n : ℕ) :
    partialSum n = ((n + 1).primesBelow).sum (fun p => (1 : ℝ) / p) := by
  simp only [partialSum, primeReciprocalTerm, Nat.primesBelow, Finset.sum_filter,
    Set.indicator_apply, div_eq_inv_mul]
  refine Finset.sum_congr rfl ?_
  intro p _
  by_cases hp : Nat.Prime p <;> simp [hp]

lemma partialSum_eq_sum_primesBelow : partialSum = fun n =>
    ((n + 1).primesBelow).sum (fun p => (1 : ℝ) / p) := by
  funext n; exact partialSum_eq_primesBelow_sum n

lemma partialSum_mono {m n : ℕ} (hmn : m ≤ n) : partialSum m ≤ partialSum n := by
  simp only [partialSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hmn)) ?_
  intro k _ _; exact primeReciprocalTerm_nonneg k

lemma partialSum_zero : partialSum 0 = 0 := by
  simp [partialSum, primeReciprocalTerm]

lemma succ_sub_one {k : ℕ} (hk : k ≠ 0) : (k - 1).succ = k := by
  rcases k with _ | k
  · exact (hk rfl).elim
  · rfl

/-- `((k-1)+1).primesBelow = k.primesBelow` (normaliza `pred`/`succ` en índices). -/
lemma primesBelow_pred_add_one (k : ℕ) : ((k - 1) + 1).primesBelow = k.primesBelow := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [← Nat.succ_eq_add_one, succ_sub_one hk]

lemma primesBelow_subset_primesBelow_succ {k m : ℕ} (h : k ≤ m + 1) :
    k.primesBelow ⊆ (m + 1).primesBelow := by
  intro p hp
  simp only [Nat.mem_primesBelow] at hp ⊢
  exact ⟨lt_of_lt_of_le hp.1 h, hp.2⟩

/-- Incremento de `S(m)` sobre primos nuevos respecto al umbral `k`. -/
lemma partialSum_sdiff {m k : ℕ} (h : k.primesBelow ⊆ (m + 1).primesBelow) :
    partialSum m - partialSum (k - 1) =
      ∑ p ∈ (m + 1).primesBelow \ k.primesBelow, (1 : ℝ) / p := by
  rw [partialSum_eq_primesBelow_sum, partialSum_eq_primesBelow_sum, primesBelow_pred_add_one]
  have hdisj := Finset.disjoint_sdiff (s := k.primesBelow) (t := (m + 1).primesBelow)
  have hunion := Finset.sdiff_union_of_subset h
  have hadd := Finset.sum_union (f := fun p : ℕ => (1 : ℝ) / p) hdisj
  have hunion' :
      k.primesBelow ∪ ((m + 1).primesBelow \ k.primesBelow) = (m + 1).primesBelow := by
    rw [Finset.union_comm]
    exact hunion
  rw [hunion'] at hadd
  linarith

lemma primesBelow_succ_eq_of_not_prime {k : ℕ} (hkp : ¬ Nat.Prime k) :
    (k + 1).primesBelow = k.primesBelow := by
  rw [Nat.primesBelow_succ, if_neg hkp]

/-- Si `k` no es primo, añadir `k` no cambia `S(k-1)` ni `S(k)`. -/
lemma partialSum_pred_eq_of_not_prime {k : ℕ} (hk : k ≠ 0) (hkp : ¬ Nat.Prime k) :
    partialSum (k - 1) = partialSum k := by
  rw [partialSum_eq_primesBelow_sum, partialSum_eq_primesBelow_sum]
  rcases k with _ | k
  · exact (hk rfl).elim
  · rw [primesBelow_pred_add_one, (primesBelow_succ_eq_of_not_prime hkp).symm]

lemma partialProduct_pos {n : ℕ} (hn : 2 ≤ n) : 0 < partialProduct n := by
  unfold partialProduct
  have hmem : 2 ∈ (n + 1).primesBelow := by
    simp [Nat.primesBelow, Finset.mem_filter, Finset.mem_range, Nat.prime_two]
    omega
  refine Finset.prod_pos fun p hp => ?_
  have hp' := Nat.prime_of_mem_primesBelow hp
  have hppos : (0 : ℝ) < p := mod_cast hp'.pos
  have hle : (1 : ℝ) / p ≤ 1 / 2 := by
    gcongr
    exact mod_cast hp'.two_le
  linarith

end ErdosReciprocals

/-! ### From `ErdosReciprocals/HarmonicBound.lean` -/

/-!
# Cotas elementales

* `1/2 ≤ S(n)` (monotonía desde `S(2)`).
* `S(n) ≤ H_n` (suma sobre primos ⊆ recíprocos armónicos).
* `S(n) ≤ 1 + log n` (vía `harmonic_le_one_add_log`).
-/

namespace ErdosReciprocals

open scoped BigOperators

lemma partialSum_eq_sum_range_indicator (n : ℕ) :
    partialSum n =
      ∑ i ∈ Finset.range (n + 1), if Nat.Prime i then (i : ℝ)⁻¹ else 0 := by
  unfold partialSum primeReciprocalTerm
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Set.indicator_apply, div_eq_inv_mul]
  by_cases hp : Nat.Prime i <;> simp [hp]

lemma range_succ_filter_ne_zero_eq_Icc (n : ℕ) :
    (Finset.range (n + 1)).filter (fun i => i ≠ 0) = Finset.Icc 1 n := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Nat.succ_le_iff]
  constructor
  · rintro ⟨hi, hi0⟩
    rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with rfl | hpos
    · exact (hi0 rfl).elim
    · exact ⟨hpos, Nat.le_of_lt_succ hi⟩
  · rintro ⟨h1, hn⟩
    exact ⟨Nat.lt_succ_of_le hn, Nat.one_le_iff_ne_zero.mp h1⟩

lemma harmonic_cast_eq_sum_range_indicator (n : ℕ) :
    (harmonic n : ℝ) =
      ∑ i ∈ Finset.range (n + 1), if i = 0 then 0 else (i : ℝ)⁻¹ := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [← range_succ_filter_ne_zero_eq_Icc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = 0 <;> simp [hi]

/-- Cota global: `S(n) ≤ H_n`. -/
theorem partialSum_le_harmonic (n : ℕ) : partialSum n ≤ (harmonic n : ℝ) := by
  rw [partialSum_eq_sum_range_indicator, harmonic_cast_eq_sum_range_indicator]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i = 0
  · simp [hi]
  · by_cases hp : Nat.Prime i <;> simp [hi, hp, inv_nonneg]

/-- Cota logarítmica: `S(n) ≤ 1 + log n`. -/
theorem partialSum_le_one_add_log (n : ℕ) :
    partialSum n ≤ 1 + Real.log n :=
  (partialSum_le_harmonic n).trans (harmonic_le_one_add_log n)

/-- `S(2) = 1/2`. -/
theorem partialSum_two : partialSum 2 = 1 / 2 := by
  rw [partialSum_eq_primesBelow_sum]
  have hfin : (2 + 1).primesBelow = {2} := by decide
  rw [hfin]
  norm_num

theorem partialSum_ge_one_half {n : ℕ} (hn : 2 ≤ n) : 1 / 2 ≤ partialSum n := by
  simpa [partialSum_two] using partialSum_mono hn

theorem partialSum_pos {n : ℕ} (hn : 2 ≤ n) : 0 < partialSum n := by
  linarith [partialSum_ge_one_half hn]

/-- Cota superior puntual: `S(2) ≤ H_2`. -/
theorem partialSum_two_le_harmonic : partialSum 2 ≤ (harmonic 2 : ℝ) := by
  rw [partialSum_two]
  unfold harmonic
  simp only [Finset.sum_range_succ]
  norm_num

end ErdosReciprocals

/-! ### From `ErdosReciprocals/ProductBounds.lean` -/

/-!
# Cotas elementales de `∏_{p≤n}(1 - 1/p)`
-/

namespace ErdosReciprocals

open Real

lemma partialProduct_factor_le_one {n p : ℕ} (_hp : p ∈ (n + 1).primesBelow) :
    (1 - (1 : ℝ) / p) ≤ 1 := by
  have : 0 ≤ (1 : ℝ) / p := by positivity
  linarith

lemma partialProduct_factor_nonneg {n p : ℕ} (hp : p ∈ (n + 1).primesBelow) :
    0 ≤ (1 - (1 : ℝ) / p) := by
  have hp' := Nat.prime_of_mem_primesBelow hp
  have hppos : 0 < (p : ℝ) := mod_cast hp'.pos
  have : (1 : ℝ) / p ≤ 1 := by
    rw [one_div_le hppos zero_lt_one, one_div_one]
    exact_mod_cast hp'.one_lt.le
  linarith

lemma partialProduct_factor_pos {n p : ℕ} (hp : p ∈ (n + 1).primesBelow) :
    0 < (1 - (1 : ℝ) / p) := by
  have hp' := Nat.prime_of_mem_primesBelow hp
  have hppos : 0 < (p : ℝ) := mod_cast hp'.pos
  have : (1 : ℝ) / p < 1 := by
    rw [one_div_lt hppos zero_lt_one, one_div_one]
    exact_mod_cast hp'.one_lt
  linarith

theorem partialProduct_le_one {n : ℕ} : partialProduct n ≤ 1 := by
  unfold partialProduct
  refine Finset.prod_le_one (fun p hp => partialProduct_factor_nonneg hp) fun p hp => ?_
  exact partialProduct_factor_le_one hp

theorem partialProduct_antitone {m n : ℕ} (hmn : m ≤ n) :
    partialProduct n ≤ partialProduct m := by
  unfold partialProduct
  refine Finset.prod_le_prod_of_subset_of_le_one (Nat.primesBelow_mono (Nat.succ_le_succ hmn)) ?_ ?_
  · intro p hp; exact partialProduct_factor_nonneg hp
  · intro p hp _; exact partialProduct_factor_le_one hp

lemma log_partialProduct_eq_sum (n : ℕ) :
    log (partialProduct n) = ∑ p ∈ (n + 1).primesBelow, log (1 - (1 : ℝ) / p) := by
  unfold partialProduct
  rw [Real.log_prod (fun p hp => ne_of_gt (partialProduct_factor_pos hp))]

theorem partialProduct_le_exp_neg_partialSum {n : ℕ} (hn : 2 ≤ n) :
    partialProduct n ≤ Real.exp (-partialSum n) := by
  have hpos := partialProduct_pos hn
  have hterm :
      ∀ p ∈ (n + 1).primesBelow, log (1 - (1 : ℝ) / p) ≤ -(1 : ℝ) / p := fun p hp => by
    have hp' := Nat.prime_of_mem_primesBelow hp
    have hppos : 0 < (p : ℝ) := mod_cast hp'.pos
    have : (1 : ℝ) / p < 1 := by
      rw [one_div_lt hppos zero_lt_one, one_div_one]
      exact_mod_cast hp'.one_lt
    have hone : 0 < 1 - (1 : ℝ) / p := by linarith
    simpa [neg_div] using (log_le_sub_one_of_pos hone)
  have hsum :
      log (partialProduct n) ≤ -∑ p ∈ (n + 1).primesBelow, (1 : ℝ) / p := by
    rw [log_partialProduct_eq_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun p hp => by simpa [neg_div] using hterm p hp
  have hsum' : log (partialProduct n) ≤ -partialSum n := by
    rwa [partialSum_eq_primesBelow_sum]
  calc
    partialProduct n = exp (log (partialProduct n)) := (exp_log hpos).symm
    _ ≤ exp (-partialSum n) := exp_monotone hsum'

end ErdosReciprocals

/-! ### From `ErdosReciprocals/Divergence.lean` -/

/-!
# Divergencia de `∑ 1/p` (prueba de Erdős en Mathlib)

Mathlib formaliza la prueba elemental de Erdős en
`Mathlib.NumberTheory.SumPrimeReciprocals`.

Este archivo conecta esa no-summabilidad con las sumas parciales `partialSum`
del proyecto y deduce la infinitud de primos por acotación.
-/

namespace ErdosReciprocals

open scoped BigOperators Topology
open Filter

lemma tendsto_sum_range_succ_of_tendsto_sum_range {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop atTop) :
    Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), f i) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) h
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (hf n)

/-- **Teorema de Erdős (Mathlib)**: la serie de recíprocos de primos no es summable. -/
theorem erdos_not_summable_primes : ¬ Summable (fun p : Nat.Primes => (1 / p : ℝ)) :=
  Nat.Primes.not_summable_one_div

/-- Las sumas parciales `S(n)` tienden a infinito. -/
theorem tendsto_partialSum_atTop : Tendsto partialSum atTop atTop := by
  have hf := primeReciprocalTerm_nonneg
  have hterm := primeReciprocalTerm_eq_indicator ▸ not_summable_one_div_on_primes
  have hrange :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).1 hterm
  unfold partialSum
  exact tendsto_sum_range_succ_of_tendsto_sum_range hf hrange

/-- Forma aritmética: `∀ M, ∃ n, S(n) > M`. -/
theorem exists_partialSum_gt (M : ℝ) : ∃ n, partialSum n > M := by
  rcases (tendsto_atTop_atTop.mp tendsto_partialSum_atTop (M + 1)) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have := hN N le_rfl
  linarith

lemma partialSum_le_sum_finset_primes {s : Finset ℕ}
    (hs : ∀ p, Nat.Prime p → p ∈ s) (n : ℕ) :
    partialSum n ≤ ∑ p ∈ s, (1 : ℝ) / p := by
  rw [partialSum_eq_primesBelow_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => by positivity)
  exact hs _ (Nat.prime_of_mem_primesBelow hp)

/-- Si solo hay finitos primos, las sumas parciales están acotadas. -/
theorem bddAbove_partialSum_of_finite_primes {s : Finset ℕ}
    (hs : ∀ p, Nat.Prime p → p ∈ s) : BddAbove (Set.range partialSum) := by
  refine ⟨∑ p ∈ s, (1 : ℝ) / p, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact partialSum_le_sum_finset_primes hs n

/-- La divergencia de `∑ 1/p` implica infinitud de primos. -/
theorem infinite_primes_of_divergent_reciprocals :
    Set.Infinite {p | Nat.Prime p} := by
  intro hfin
  let s := hfin.toFinset
  have hs : ∀ p, Nat.Prime p → p ∈ s := fun p hp => hfin.mem_toFinset.mpr hp
  have hbdd := bddAbove_partialSum_of_finite_primes hs
  rcases hbdd with ⟨C, hC⟩
  rcases exists_partialSum_gt C with ⟨n, hn⟩
  linarith [hC ⟨n, rfl⟩, hn]

/-- Corolario: existen primos arbitrariamente grandes. -/
theorem exists_prime_gt (n : ℕ) : ∃ p, Nat.Prime p ∧ n < p := by
  rcases (Set.infinite_iff_exists_gt.mp infinite_primes_of_divergent_reciprocals) n with
    ⟨p, hp, hgt⟩
  exact ⟨p, hp, hgt⟩

end ErdosReciprocals

/-! ### From `ErdosReciprocals/ChebyshevLink.lean` -/

/-!
# Enlace con Chebyshev (frontera de Mathlib)

Cotas explícitas para `∑_{p≤n} (log p)/p` y minoraciones de `S(n)` vía `π(n)`.
-/

namespace ErdosReciprocals

open scoped BigOperators Nat.Prime
open Real

open Chebyshev in
/-- `∑_{p≤n} (log p)/p ≤ θ(n)/2` porque `log p / p ≤ (log p)/2` para `p ≥ 2`. -/
theorem partialLogSum_le_half_theta (n : ℕ) :
    partialLogSum n ≤ θ n / 2 := by
  unfold partialLogSum
  have hterm :
      ∀ p ∈ (n + 1).primesBelow, log (p : ℝ) / (p : ℝ) ≤ log (p : ℝ) / 2 := fun p hp => by
    have hp' := Nat.prime_of_mem_primesBelow hp
    gcongr
    exact mod_cast hp'.two_le
  calc
    ∑ p ∈ (n + 1).primesBelow, log (p : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ (n + 1).primesBelow, log (p : ℝ) / 2 := Finset.sum_le_sum hterm
    _ = (∑ p ∈ (n + 1).primesBelow, log (p : ℝ)) / 2 := by
      rw [← Finset.sum_div]
    _ = θ n / 2 := by
      rw [theta_eq_sum_primesLE_log, Nat.primesBelow_eq_primesLE_sub_one (n + 1)]
      simp only [Nat.succ_sub_one]

open Chebyshev in
/-- Cota explícita de Chebyshev para la suma logarítmica ponderada. -/
theorem partialLogSum_le_log4_mul_div_two (n : ℕ) :
    partialLogSum n ≤ log 4 * n / 2 := by
  refine (partialLogSum_le_half_theta n).trans ?_
  gcongr
  exact theta_le_log4_mul_x (mod_cast n.zero_le)

/-- `S(n) ≥ π(n)/n`: cada término `1/p` con `p ≤ n` contribuye al menos `1/n`. -/
theorem partialSum_ge_primeCounting_div {n : ℕ} (_ : 0 < n) :
    (Nat.primeCounting n : ℝ) / n ≤ partialSum n := by
  rw [partialSum_eq_primesBelow_sum]
  have hle : ∀ p ∈ (n + 1).primesBelow, (1 : ℝ) / n ≤ (1 : ℝ) / p := fun p hp => by
    have hp' := Nat.prime_of_mem_primesBelow hp
    have hpn : p ≤ n := Nat.le_of_lt_succ (Nat.lt_of_mem_primesBelow hp)
    exact one_div_le_one_div_of_le (mod_cast hp'.pos) (mod_cast hpn)
  have hcard : (Nat.primeCounting n : ℝ) = ((n + 1).primesBelow.card : ℝ) := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.primesBelow_card_eq_primeCounting']
  calc
    (Nat.primeCounting n : ℝ) / n
        = ((n + 1).primesBelow.card : ℝ) / n := by rw [hcard]
    _ = ∑ _ ∈ (n + 1).primesBelow, (1 : ℝ) / n := by
      rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      ring
    _ ≤ ∑ p ∈ (n + 1).primesBelow, (1 : ℝ) / p := Finset.sum_le_sum hle

/-- Minoración explícita de `S(n)` combinando Chebyshev y `π(n)/n`. -/
theorem partialSum_ge_chebyshev_ratio {n : ℕ} (hn : 1 < n) :
    ((n * log 2 - log (n + 1)) / log n) / n ≤ partialSum n := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  refine le_trans ?_ (partialSum_ge_primeCounting_div hn0)
  gcongr
  exact_mod_cast Chebyshev.pi_ge n

end ErdosReciprocals

/-! ### From `ErdosReciprocals/Erdos.lean` -/

/-!
# Capa Erdős: lema clave importado de Mathlib

La demostración elemental completa está en `Mathlib.NumberTheory.SumPrimeReciprocals`.
Aquí reexportamos el corazón combinatorio y lo conectamos con nuestra notación.
-/

namespace ErdosReciprocals

open scoped BigOperators Topology
open Filter

/-- **Lema de Erdős (Mathlib)**: bloques de primos con masa `≥ 1/2` en recíprocos. -/
theorem erdos_half_block_lemma (k : ℕ) :
    1 / 2 ≤ ∑ p ∈ (4 ^ (k.primesBelow.card + 1)).succ.primesBelow \ k.primesBelow,
      (1 / p : ℝ) :=
  one_half_le_sum_primes_ge_one_div k

/-- Versión en términos de `Nat.Primes`. -/
theorem erdos_series_not_summable :
    ¬ Summable (fun p : Nat.Primes => (1 / p : ℝ)) :=
  erdos_not_summable_primes

/-- Divergencia en sumas parciales `S(n)`. -/
theorem erdos_partial_sums_diverge :
    Tendsto partialSum atTop atTop :=
  tendsto_partialSum_atTop

/-- Forma clásica: la serie de recíprocos de primos no converge. -/
theorem erdos_sum_diverges (M : ℝ) : ∃ n, partialSum n > M :=
  exists_partialSum_gt M

end ErdosReciprocals

end


/-!
## Source file: `MertensPNT/MertensConstant.lean`
-/

/-!
# The Meissel-Mertens constant

This file defines the prime correction series and the Meissel-Mertens constant
`mertensConstant = gamma + tsum corrections`, with summability certificates and
the elementary one-sided asymptotic boundary.
-/

/-! ### From `ErdosReciprocals/MertensConstant.lean` -/

/-!
# Constante de Mertens (definición analítica)

`M = γ + ∑'_p (log(1 - 1/p) + 1/p)`, con serie de corrección summable por `O(1/p²)`.
-/

@[expose] public section

namespace ErdosReciprocals

open scoped BigOperators Topology
open Filter Real

lemma primeR_eq_cast (p : Nat.Primes) : primeR p = (p : ℝ) := by
  unfold primeR
  rfl

/-- Corrección de Mertens en un primo: `log(1 - 1/p) + 1/p`. -/
noncomputable def mertensPrimeCorrection (p : Nat.Primes) : ℝ :=
  log (1 - 1 / primeR p) + 1 / primeR p

lemma inv_primeR_pos (p : Nat.Primes) : 0 < 1 / primeR p :=
  one_div_pos.mpr (primeR_pos p)

lemma inv_primeR_lt_one (p : Nat.Primes) : |1 / primeR p| < 1 := by
  rw [abs_of_pos (inv_primeR_pos p)]
  have hp1 := one_lt_primeR p
  rwa [one_div_lt (by positivity) zero_lt_one, one_div_one]

lemma inv_primeR_lt_one' (p : Nat.Primes) : 1 / primeR p < 1 := by
  have hp1 := one_lt_primeR p
  rwa [one_div_lt (by positivity) zero_lt_one, one_div_one]

lemma inv_primeR_le_half (p : Nat.Primes) : 1 / primeR p ≤ 1 / 2 := by
  gcongr
  exact two_le_primeR p

lemma mertensPrimeCorrection_eq_neg_tsum (p : Nat.Primes) :
    mertensPrimeCorrection p =
      -∑' n : ℕ, (1 / primeR p) ^ (n + 2) / (n + 2) := by
  have hx := inv_primeR_lt_one p
  have hf := (hasSum_pow_div_log_of_abs_lt_one hx).summable
  have hsum := (hasSum_pow_div_log_of_abs_lt_one hx).tsum_eq
  have hsplit := hf.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at hsplit
  have hindex (n : ℕ) :
      (1 / primeR p) ^ (n + 1 + 1) / (↑(n + 1) + 1) =
        (1 / primeR p) ^ (n + 2) / (↑n + 2) := by
    rw [show n + 1 + 1 = n + 2 by ring,
      show (↑(n + 1) + 1 : ℝ) = ↑(n + 2) by norm_cast,
      show (↑n + 2 : ℝ) = ↑(n + 2) by norm_cast]
  have htail_eq :
      ∑' i : ℕ, (1 / primeR p) ^ (i + 1 + 1) / (↑(i + 1) + 1) =
        ∑' i : ℕ, (1 / primeR p) ^ (i + 2) / (↑i + 2) :=
    tsum_congr fun i => hindex i
  have hmain :
      (1 / primeR p) + ∑' n : ℕ, (1 / primeR p) ^ (n + 2) / (n + 2) =
        -log (1 - 1 / primeR p) := by
    have hsplit' := hsplit.trans hsum
    convert hsplit' using 2
    · simp [pow_one, div_one]
    · simp_rw [htail_eq]
  dsimp [mertensPrimeCorrection]
  linarith

lemma tsum_inv_primeR_pow_add_geometric (p : Nat.Primes) :
    ∑' n : ℕ, (1 / primeR p) ^ (n + 2) = (1 / primeR p) ^ 2 / (1 - 1 / primeR p) := by
  set r := 1 / primeR p
  have hx := inv_primeR_lt_one p
  have hr : |r| < 1 := by simpa [r] using hx
  have hr1 : r < 1 := by simpa [r] using inv_primeR_lt_one' p
  have hpos : 0 < 1 - r := sub_pos.mpr hr1
  have hsum : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ := by simpa [r] using tsum_geometric_of_abs_lt_one hr
  have hsplit := (summable_geometric_of_abs_lt_one hr).sum_add_tsum_nat_add 2
  rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one] at hsplit
  rw [hsum] at hsplit
  have htail : ∑' n : ℕ, r ^ (n + 2) = (1 - r)⁻¹ - 1 - r := by linarith
  have halgebra : (1 - r)⁻¹ - 1 - r = r ^ 2 / (1 - r) := by
    field_simp [hpos.ne']
    ring
  calc
    ∑' n : ℕ, (1 / primeR p) ^ (n + 2) = ∑' n : ℕ, r ^ (n + 2) := by simp only [r]
    _ = (1 - r)⁻¹ - 1 - r := htail
    _ = r ^ 2 / (1 - r) := halgebra
    _ = (1 / primeR p) ^ 2 / (1 - 1 / primeR p) := by simp only [r, div_eq_mul_inv, pow_two]

lemma mertensPrimeCorrection_abs_le (p : Nat.Primes) :
    |mertensPrimeCorrection p| ≤ 2 / primeR p ^ 2 := by
  have hxpos := inv_primeR_pos p
  have hx := inv_primeR_lt_one p
  have hx1 := inv_primeR_lt_one' p
  have hxle := inv_primeR_le_half p
  rw [mertensPrimeCorrection_eq_neg_tsum]
  have hnonneg : 0 ≤ ∑' n : ℕ, (1 / primeR p) ^ (n + 2) / (n + 2) := by
    refine tsum_nonneg fun n => ?_
    positivity
  rw [abs_neg, abs_of_nonneg hnonneg]
  have hterm (n : ℕ) :
      (1 / primeR p) ^ (n + 2) / (n + 2) ≤ (1 / primeR p) ^ (n + 2) := by
    have hn : 0 < (n + 2 : ℝ) := by norm_cast; omega
    have hpow := pow_nonneg (inv_primeR_pos p).le (n + 2)
    rw [div_le_iff₀ hn]
    apply le_mul_of_one_le_right hpow
    norm_cast
    omega
  have hg : Summable fun (n : ℕ) => (1 / primeR p) ^ (n + 2) :=
    (summable_nat_add_iff 2).mpr (summable_geometric_of_abs_lt_one hx)
  have hf_tail : Summable fun (n : ℕ) => (1 / primeR p) ^ (n + 2) / (n + 2) := by
    refine Summable.of_norm_bounded hg ?_
    intro n
    rw [norm_eq_abs, abs_div, abs_of_pos (pow_pos hxpos _)]
    have hn : 0 < (n + 2 : ℝ) := by norm_cast; omega
    rw [abs_of_pos hn]
    exact hterm n
  have hle :
      ∑' n : ℕ, (1 / primeR p) ^ (n + 2) / (n + 2) ≤ ∑' n : ℕ, (1 / primeR p) ^ (n + 2) :=
    Summable.tsum_mono hf_tail hg fun n => hterm n
  have hgeo :=
    tsum_inv_primeR_pow_add_geometric p
  have hbound :
      (1 / primeR p) ^ 2 / (1 - 1 / primeR p) ≤ 2 * (1 / primeR p) ^ 2 := by
    rw [div_le_iff₀ (sub_pos.mpr hx1)]
    nlinarith [hxle]
  calc
    ∑' n : ℕ, (1 / primeR p) ^ (n + 2) / (n + 2) ≤ ∑' n : ℕ, (1 / primeR p) ^ (n + 2) := hle
    _ = (1 / primeR p) ^ 2 / (1 - 1 / primeR p) := hgeo
    _ ≤ 2 * (1 / primeR p) ^ 2 := hbound
    _ = 2 / primeR p ^ 2 := by field_simp [pow_two]

/-- Corrección de Mertens indexada por `k` ↦ `k`-ésimo primo. -/
noncomputable def mertensCorrectionIndexed (k : ℕ) : ℝ :=
  mertensPrimeCorrection ⟨Nat.nth Nat.Prime k, Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k⟩

noncomputable def natPrimesEquiv : ℕ ≃ Nat.Primes where
  toFun k := ⟨Nat.nth Nat.Prime k, Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k⟩
  invFun p := Nat.count Nat.Prime p
  left_inv k := Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime k
  right_inv p := Subtype.ext (Nat.nth_count (p := Nat.Prime) p.property)

/-- La serie de corrección sobre primos converge. -/
theorem summable_mertensPrimeCorrection :
    Summable mertensPrimeCorrection := by
  have hcomp := (Nat.Primes.summable_rpow (r := (-2 : ℝ))).mpr (by norm_num : (-2 : ℝ) < -1)
  refine Summable.of_norm_bounded (Summable.mul_left 2 hcomp) fun p => ?_
  rw [Real.norm_eq_abs]
  have heq : (2 : ℝ) / primeR p ^ 2 = 2 * (p : ℝ) ^ (-2 : ℝ) := by
    have h : (1 : ℝ) / primeR p ^ 2 = (primeR p : ℝ) ^ (-2 : ℝ) := by
      have hmid : (1 / primeR p) ^ 2 = (primeR p ^ 2)⁻¹ := by
        rw [← one_div, one_div_pow]
      have hrpow : (primeR p ^ 2)⁻¹ = (primeR p : ℝ) ^ (-2 : ℝ) := by
        symm
        simp [Real.rpow_neg (primeR_pos p).le]
      rw [← one_div_pow, hmid, hrpow]
    calc
      (2 : ℝ) / primeR p ^ 2 = 2 * (1 / primeR p ^ 2) := by ring
      _ = 2 * (primeR p : ℝ) ^ (-2 : ℝ) := by rw [h]
      _ = 2 * (p : ℝ) ^ (-2 : ℝ) := by rw [primeR_eq_cast]
  calc
    |mertensPrimeCorrection p| ≤ 2 / primeR p ^ 2 := mertensPrimeCorrection_abs_le p
    _ = 2 * (p : ℝ) ^ (-2 : ℝ) := heq

/-- Suma de las correcciones primas (serie convergente). -/
noncomputable def mertensPrimeCorrectionSum : ℝ :=
  ∑' p : Nat.Primes, mertensPrimeCorrection p

theorem mertensPrimeCorrectionSum_eq_tsum :
    mertensPrimeCorrectionSum = ∑' p : Nat.Primes, mertensPrimeCorrection p := rfl

theorem summable_mertensCorrectionIndexed : Summable mertensCorrectionIndexed := by
  have h := (natPrimesEquiv.summable_iff (f := mertensPrimeCorrection)).mpr
    summable_mertensPrimeCorrection
  have heq : mertensCorrectionIndexed = mertensPrimeCorrection ∘ ⇑natPrimesEquiv := by
    ext k
    dsimp [mertensCorrectionIndexed]
    have hk : natPrimesEquiv k = ⟨Nat.nth Nat.Prime k,
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k⟩ := rfl
    rw [hk]
  rw [heq]
  exact h

theorem mertensPrimeCorrectionSum_eq_tsum_indexed :
    mertensPrimeCorrectionSum = ∑' k : ℕ, mertensCorrectionIndexed k := by
  rw [mertensPrimeCorrectionSum_eq_tsum, ← natPrimesEquiv.tsum_eq]
  refine tsum_congr fun k => ?_
  dsimp [mertensCorrectionIndexed]
  have hk : natPrimesEquiv k = ⟨Nat.nth Nat.Prime k,
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k⟩ := rfl
  rw [hk]

/-- Constante de Mertens: `γ + ∑'_p (log(1 - 1/p) + 1/p)`. -/
noncomputable def mertensConstant : ℝ :=
  eulerMascheroniConstant + mertensPrimeCorrectionSum

theorem mertensConstant_eq_gamma_add_correctionSum :
    mertensConstant = eulerMascheroniConstant + mertensPrimeCorrectionSum := rfl

/-- Valor numérico de referencia (tabla `../data/`). -/
noncomputable def mertensConstantApprox : ℝ := 0.26149721284478386

theorem mertensConstantApprox_pos : 0 < mertensConstantApprox := by
  unfold mertensConstantApprox
  norm_num

end ErdosReciprocals

/-! ### From `ErdosReciprocals/Asymptotics.lean` -/

/-!
# Asintótica unilateral disponible (sin PNT)

De `S(n) ≤ H_n` y `H_n - log n → γ` (Mathlib) se deduce una cota superior
asintótica para `S(n) - log n`. Esto es estrictamente más débil que Mertens
(`S(n) ~ log log n + M`), pero es completamente riguroso con la infraestructura actual.
-/

namespace ErdosReciprocals

open scoped Topology
open Filter Real

/-- `S(n) - log n` está acotado superiormente por `H_n - log n`. -/
theorem partialSum_sub_log_le_harmonic_sub_log (n : ℕ) :
    partialSum n - log n ≤ harmonic n - log n := by
  have := partialSum_le_harmonic n
  linarith

/-- Existe `N` tal que `S(n) - log n < γ + ε` para todo `n ≥ N`. -/
theorem partialSum_sub_log_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, partialSum n - log n < eulerMascheroniConstant + ε := by
  set U := Set.Ioo (eulerMascheroniConstant - 1) (eulerMascheroniConstant + ε)
  have hmem : eulerMascheroniConstant ∈ U :=
    ⟨by linarith [Real.one_half_lt_eulerMascheroniConstant], lt_add_of_pos_right _ hε⟩
  rcases ((tendsto_atTop_nhds (α := ℕ)).1 Real.tendsto_harmonic_sub_log U hmem isOpen_Ioo) with
    ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hn' := hN n hn
  simp only [U, Set.mem_Ioo] at hn'
  linarith [partialSum_sub_log_le_harmonic_sub_log n, hn'.2]

/-- `S(n) - log n` no puede tender a `+∞`. -/
theorem not_tendsto_partialSum_sub_log_atTop :
    ¬ Tendsto (fun n : ℕ => partialSum n - log n) atTop atTop := by
  intro h
  rcases partialSum_sub_log_eventually_lt 1 one_pos with ⟨S, hS⟩
  rcases (tendsto_atTop_atTop.mp h (eulerMascheroniConstant + 2)) with ⟨N, hN⟩
  have := hN (max N S) (le_max_left N S)
  have := hS _ (le_max_right N S)
  linarith [Real.one_half_lt_eulerMascheroniConstant]

end ErdosReciprocals

end


/-!
## Source file: `MertensPNT/ErdosBlocks.lean`
-/

/-!
# Erdos block construction

This file contains the explicit block endpoints, the iterated Erdos subsequence,
growth certificates, and logarithmic sum bounds.
-/

/-! ### From `ErdosReciprocals/ErdosBlocks.lean` -/

/-!
# Bloques cuantitativos de Erdős

Conectamos el lema de Mathlib con incrementos de `partialSum` y una iteración
que produce crecimiento lineal `S(erdosIter t) ≥ t/2`.
-/

@[expose] public section

namespace ErdosReciprocals

open scoped BigOperators Nat.Prime

/-- Umbral del bloque Erdős: `4^(π(k-1)+1)`. -/
noncomputable def erdosBlockEnd (k : ℕ) : ℕ :=
  4 ^ (k.primesBelow.card + 1)

lemma primesBelow_card_mono {m k : ℕ} (h : m ≤ k) :
    (m.primesBelow).card ≤ (k.primesBelow).card :=
  Finset.card_le_card (Nat.primesBelow_mono h)

/-- Masa mínima del bloque Erdős (forma Finset de Mathlib). -/
theorem erdos_block_mass (k : ℕ) :
    1 / 2 ≤ ∑ p ∈ ((4 ^ (k.primesBelow.card + 1)).succ).primesBelow \ k.primesBelow,
      (1 : ℝ) / p :=
  erdos_half_block_lemma k

/-- Cada bloque Erdős incrementa `partialSum` en al menos `1/2`. -/
theorem partialSum_erdos_block_increment {k : ℕ} (hk : k ≤ erdosBlockEnd k + 1) :
    1 / 2 ≤ partialSum (erdosBlockEnd k) - partialSum (k - 1) := by
  have hsubset :
      k.primesBelow ⊆ (erdosBlockEnd k + 1).primesBelow :=
    primesBelow_subset_primesBelow_succ hk
  rw [partialSum_sdiff hsubset]
  have hfin :
      (erdosBlockEnd k + 1).primesBelow \ k.primesBelow =
        ((4 ^ (k.primesBelow.card + 1)).succ).primesBelow \ k.primesBelow := by
    simp [erdosBlockEnd]
  rw [hfin]
  exact erdos_block_mass k

/-- Primer bloque: `S(4) ≥ 1/2`. -/
theorem partialSum_four_ge_half : 1 / 2 ≤ partialSum 4 := by
  have h := partialSum_erdos_block_increment (k := 0) (by simp [erdosBlockEnd])
  simpa [erdosBlockEnd, partialSum_zero] using h

/-- Iteración Erdős: `0, 4, 4^(π(4)+1), …` -/
noncomputable def erdosIter : ℕ → ℕ
  | 0 => 0
  | t + 1 => erdosBlockEnd (erdosIter t)

lemma erdosIter_succ (t : ℕ) : erdosIter (t + 1) = erdosBlockEnd (erdosIter t) := rfl

lemma four_dvd_erdosBlockEnd (k : ℕ) : 4 ∣ erdosBlockEnd k := by
  unfold erdosBlockEnd
  exact ⟨4 ^ k.primesBelow.card, pow_succ' 4 k.primesBelow.card⟩

lemma erdosIter_le_blockEnd (t : ℕ) : erdosIter t ≤ erdosBlockEnd (erdosIter t) := by
  induction t with
  | zero => simp [erdosIter, erdosBlockEnd]
  | succ t ih =>
    rw [erdosIter_succ]
    unfold erdosBlockEnd
    apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 4)
    exact Nat.succ_le_succ (primesBelow_card_mono ih)

lemma erdosIter_le_blockEnd_succ (t : ℕ) : erdosIter t ≤ erdosBlockEnd (erdosIter t) + 1 :=
  Nat.le_succ_of_le (erdosIter_le_blockEnd t)

lemma erdosIter_mono {m n : ℕ} (hmn : m ≤ n) : erdosIter m ≤ erdosIter n := by
  induction n with
  | zero =>
    rcases Nat.le_zero.mp hmn
    rfl
  | succ n ih =>
    rcases Nat.le_succ_iff.mp hmn with hmn' | rfl
    · exact (ih hmn').trans (erdosIter_le_blockEnd n)
    · rfl

lemma erdosIter_ne_zero {t : ℕ} (ht : t ≠ 0) : erdosIter t ≠ 0 := by
  rcases t with _ | t
  · exact absurd rfl ht
  · simp only [erdosIter, erdosBlockEnd]
    exact ne_of_gt (pow_pos (by norm_num) _)

lemma four_pow_ne_prime {n : ℕ} (hn : 2 ≤ n) : ¬ Nat.Prime (4 ^ n) := by
  intro hp
  have hpos : 0 < n := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have h4 : 4 ∣ 4 ^ n := dvd_pow (dvd_refl 4) (Nat.ne_of_gt hpos)
  have hne : (4 : ℕ) ≠ 1 := by norm_num
  have heq := (Nat.Prime.dvd_iff_eq hp hne).mp h4
  have hinj := Nat.pow_right_injective (by norm_num : 2 ≤ 4)
  have hn1 : n = 1 := hinj (by simpa [pow_one] using heq)
  omega

lemma erdosBlockEnd_not_prime (k : ℕ) : ¬ Nat.Prime (erdosBlockEnd k) := by
  unfold erdosBlockEnd
  rcases k.primesBelow.card + 1 with _ | n
  · simpa [pow_zero] using Nat.not_prime_one
  · rcases n with _ | n
    · decide
    · exact four_pow_ne_prime (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))

lemma erdos_block_primes_sdiff_nonempty (k : ℕ) :
    ((erdosBlockEnd k + 1).primesBelow \ k.primesBelow).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hmass := erdos_block_mass k
  unfold erdosBlockEnd at h hmass
  rw [h, Finset.sum_empty] at hmass
  linarith

lemma primesBelow_ssubset_erdosBlockEnd (k : ℕ) :
    k.primesBelow ⊂ (erdosBlockEnd k).primesBelow := by
  obtain ⟨p, hp⟩ := erdos_block_primes_sdiff_nonempty k
  have ⟨hp_mem, hp_not_low⟩ := Finset.mem_sdiff.mp hp
  have hp_prime := Nat.prime_of_mem_primesBelow hp_mem
  have hk_le_p : k ≤ p :=
    Nat.le_of_not_lt fun hlt => hp_not_low (Nat.mem_primesBelow.mpr ⟨hlt, hp_prime⟩)
  have hp_lt_block : p < erdosBlockEnd k := by
    by_contra hnot
    have hp_ge : erdosBlockEnd k ≤ p := Nat.le_of_not_lt hnot
    have hp_eq : p = erdosBlockEnd k :=
      Nat.eq_of_le_of_lt_succ hp_ge (Nat.lt_of_mem_primesBelow hp_mem)
    exact erdosBlockEnd_not_prime k (hp_eq ▸ hp_prime)
  have hklt : k < erdosBlockEnd k := hk_le_p.trans_lt hp_lt_block
  have hsub : k.primesBelow ⊆ (erdosBlockEnd k).primesBelow := by
    intro x hx
    exact Nat.mem_primesBelow.mpr ⟨(Nat.lt_of_mem_primesBelow hx).trans hklt,
      Nat.prime_of_mem_primesBelow hx⟩
  have hnotsub : ¬ (erdosBlockEnd k).primesBelow ⊆ k.primesBelow := by
    intro h
    exact hp_not_low (h (Nat.mem_primesBelow.mpr ⟨hp_lt_block, hp_prime⟩))
  exact (Finset.ssubset_def).mpr ⟨hsub, hnotsub⟩

lemma primesBelow_card_lt_erdosBlockEnd (k : ℕ) :
    (k.primesBelow).card < (erdosBlockEnd k).primesBelow.card :=
  Finset.card_lt_card (primesBelow_ssubset_erdosBlockEnd k)

lemma primeCounting'_lt_erdosBlockEnd (k : ℕ) :
    Nat.primeCounting' k < Nat.primeCounting' (erdosBlockEnd k) := by
  simpa [Nat.primesBelow_card_eq_primeCounting'] using primesBelow_card_lt_erdosBlockEnd k

lemma erdosIter_not_prime {t : ℕ} (ht : t ≠ 0) : ¬ Nat.Prime (erdosIter t) := by
  rcases t with _ | t
  · exact absurd rfl ht
  · simpa [erdosIter] using erdosBlockEnd_not_prime (erdosIter t)

/-- Tras `t` bloques Erdős, `S(erdosIter t) ≥ t/2`. -/
theorem partialSum_erdosIter_ge_half_mul (t : ℕ) :
    (t : ℝ) / 2 ≤ partialSum (erdosIter t) := by
  induction t with
  | zero => simp [erdosIter, partialSum_zero]
  | succ t ih =>
    by_cases ht : t = 0
    · subst ht
      simpa [erdosIter, erdosBlockEnd] using partialSum_four_ge_half
    · set k := erdosIter t with hkdef
      have hinc := partialSum_erdos_block_increment (erdosIter_le_blockEnd_succ t)
      have hk₀ : k ≠ 0 := erdosIter_ne_zero ht
      have heq : partialSum k = partialSum (k - 1) := by
        by_cases hkp : Nat.Prime k
        · exact (erdosIter_not_prime ht hkp).elim
        · exact (partialSum_pred_eq_of_not_prime hk₀ hkp).symm
      rw [← hkdef] at hinc
      rw [heq] at ih
      rw [erdosIter_succ, ← hkdef]
      calc
        (↑(t + 1) : ℝ) / 2 = (↑t : ℝ) / 2 + 1 / 2 := by
          simp [Nat.cast_add, div_eq_mul_inv]
          ring
        _ ≤ partialSum (k - 1) + 1 / 2 := add_le_add ih (le_refl _)
        _ ≤ partialSum (erdosBlockEnd k) := by linarith

end ErdosReciprocals

/-! ### From `ErdosReciprocals/LogSumBounds.lean` -/

/-!
# Cotas entre `partialLogSum` y `partialSum`

Para `p ≥ 2` se tiene `log 2 ≤ log p ≤ log n` cuando `p ≤ n`.
-/

namespace ErdosReciprocals

open Real

lemma partialLogSum_ge_log_two_mul_partialSum (n : ℕ) :
    log 2 * partialSum n ≤ partialLogSum n := by
  rw [partialSum_eq_primesBelow_sum,
    show log 2 * (∑ p ∈ (n + 1).primesBelow, (1 : ℝ) / p) =
        ∑ p ∈ (n + 1).primesBelow, log 2 * ((1 : ℝ) / p) from Finset.mul_sum _ _ _]
  simp only [partialLogSum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp' := Nat.prime_of_mem_primesBelow hp
  have hlog : log 2 ≤ log (p : ℝ) :=
    (log_le_log_iff (by norm_num) (mod_cast hp'.pos)).mpr (mod_cast hp'.two_le)
  have hpos : 0 ≤ (1 : ℝ) / p := by positivity
  calc log 2 * ((1 : ℝ) / p)
      ≤ log (p : ℝ) * ((1 : ℝ) / p) := mul_le_mul_of_nonneg_right hlog hpos
    _ = log (p : ℝ) / (p : ℝ) := by ring

lemma partialLogSum_le_log_mul_partialSum {n : ℕ} (hn : 1 < n) :
    partialLogSum n ≤ log n * partialSum n := by
  have hterm :
      ∀ p ∈ (n + 1).primesBelow, log (p : ℝ) / (p : ℝ) ≤ log n * ((1 : ℝ) / p) := fun p hp => by
    have hp' := Nat.prime_of_mem_primesBelow hp
    have hpn : p ≤ n := Nat.le_of_lt_succ (Nat.lt_of_mem_primesBelow hp)
    have hnpos : (0 : ℝ) < n := mod_cast (Nat.zero_lt_of_lt hn)
    have hlog : log (p : ℝ) ≤ log n :=
      (log_le_log_iff (mod_cast hp'.pos) hnpos).mpr (mod_cast hpn)
    have hpos : 0 ≤ (1 : ℝ) / p := by positivity
    calc log (p : ℝ) / (p : ℝ)
        ≤ log n / (p : ℝ) := by gcongr
      _ = log n * ((1 : ℝ) / p) := by ring
  calc
    partialLogSum n
        = ∑ p ∈ (n + 1).primesBelow, log (p : ℝ) / (p : ℝ) := by simp [partialLogSum]
    _ ≤ ∑ p ∈ (n + 1).primesBelow, log n * ((1 : ℝ) / p) := Finset.sum_le_sum hterm
    _ = log n * partialSum n := by
      rw [← Finset.mul_sum, partialSum_eq_primesBelow_sum]

/-- Versión explícita de la cota superior de Chebyshev en términos de `S(n)`. -/
theorem partialLogSum_le_log4_mul_n (n : ℕ) :
    partialLogSum n ≤ log 4 / 2 * n := by
  calc
    partialLogSum n ≤ log 4 * n / 2 := partialLogSum_le_log4_mul_div_two n
    _ = log 4 / 2 * n := by ring

end ErdosReciprocals

/-! ### From `ErdosReciprocals/ErdosGrowth.lean` -/

/-!
# Crecimiento de `erdosIter` y contraste asintótico

* `erdosIter t → ∞`
* `log (erdosIter t)`, `log log (erdosIter t) → ∞`
* `S(erdosIter t) - log(erdosIter t)` permanece acotado arriba (vía armónicos)
* `S(erdosIter t) ≥ t/2` crece linealmente en el índice
-/

namespace ErdosReciprocals

open scoped Topology Nat.Prime
open Filter Real

lemma succ_le_quart_pow (n : ℕ) : n + 1 ≤ 4 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih => omega

lemma le_primesBelow_card_erdosIter (t : ℕ) : t ≤ (erdosIter t).primesBelow.card := by
  induction t with
  | zero => simp [erdosIter]
  | succ t ih =>
    rw [erdosIter_succ]
    have hlt := primeCounting'_lt_erdosBlockEnd (erdosIter t)
    have hih : t ≤ Nat.primeCounting' (erdosIter t) := by
      simpa [Nat.primesBelow_card_eq_primeCounting'] using ih
    have hle : t + 1 ≤ Nat.primeCounting' (erdosBlockEnd (erdosIter t)) :=
      (Nat.succ_le_succ hih).trans (Nat.succ_le_of_lt hlt)
    simpa [Nat.primesBelow_card_eq_primeCounting'] using hle

lemma le_primeCounting_erdosIter (t : ℕ) : t ≤ Nat.primeCounting (erdosIter t) := by
  have hcard : t ≤ Nat.primeCounting' (erdosIter t) := by
    simpa [Nat.primesBelow_card_eq_primeCounting'] using le_primesBelow_card_erdosIter t
  simpa [Nat.primeCounting_eq_primeCounting'_succ] using
    hcard.trans (Nat.monotone_primeCounting' (Nat.le_succ (erdosIter t)))

theorem exists_erdosIter_ge (M : ℕ) : ∃ t, M ≤ erdosIter t := by
  refine ⟨M, ?_⟩
  induction M with
  | zero => simp [erdosIter]
  | succ M ih =>
    rw [erdosIter_succ, erdosBlockEnd]
    have hk : M + 1 ≤ (erdosIter M).primesBelow.card + 1 :=
      Nat.succ_le_succ (le_primesBelow_card_erdosIter M)
    exact hk.trans (succ_le_quart_pow (erdosIter M).primesBelow.card)

theorem tendsto_erdosIter_atTop : Tendsto erdosIter atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  rcases exists_erdosIter_ge M with ⟨t, ht⟩
  refine ⟨t, fun s hs => ht.trans (erdosIter_mono hs)⟩

theorem tendsto_natCast_erdosIter_atTop :
    Tendsto (fun t : ℕ => (erdosIter t : ℝ)) atTop atTop := by
  exact tendsto_natCast_atTop_atTop.comp tendsto_erdosIter_atTop

theorem tendsto_log_erdosIter_atTop :
    Tendsto (fun t : ℕ => log (erdosIter t)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_erdosIter_atTop

theorem tendsto_log_log_comp_erdosIter_atTop :
    Tendsto (fun t : ℕ => log (log (erdosIter t))) atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_erdosIter_atTop

theorem partialSum_erdosIter_sub_log_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ t ≥ T, partialSum (erdosIter t) - log (erdosIter t) < eulerMascheroniConstant + ε := by
  rcases partialSum_sub_log_eventually_lt ε hε with ⟨N, hN⟩
  rcases (tendsto_atTop_atTop.mp tendsto_erdosIter_atTop N) with ⟨T, hT⟩
  refine ⟨T, fun t ht => hN _ (hT t ht)⟩

theorem not_tendsto_partialSum_sub_log_comp_erdosIter_atTop :
    ¬ Tendsto (fun t : ℕ => partialSum (erdosIter t) - log (erdosIter t)) atTop atTop := by
  intro h
  rcases partialSum_erdosIter_sub_log_eventually_lt 1 one_pos with ⟨T, hT⟩
  rcases (tendsto_atTop_atTop.mp h (eulerMascheroniConstant + 2)) with ⟨S, hS⟩
  have := hS (max S T) (le_max_left S T)
  have := hT (max S T) (le_max_right S T)
  linarith [Real.one_half_lt_eulerMascheroniConstant]

end ErdosReciprocals

end


/-!
## Source file: `MertensPNT/MertensBridge.lean`
-/

/-!
# Unconditional Mertens product bridge

This file proves the finite identity between Euler products, reciprocal-prime
sums and Mertens corrections, and derives the unconditional compensated
convergence of the product.
-/

/-! ### From `ErdosReciprocals/MertensBridge.lean` -/

/-!
# Puente producto–suma–constante de Mertens

Identidad finita:
`log(∏(1-1/p)) + ∑(1/p) = ∑(log(1-1/p)+1/p)`.
-/

@[expose] public section

namespace ErdosReciprocals

open scoped BigOperators Topology
open Filter Real

/-- Suma parcial de correcciones de Mertens: `∑_{p≤n}(log(1-1/p)+1/p)`. -/
noncomputable def partialMertensCorrection (n : ℕ) : ℝ :=
  ((n + 1).primesBelow).sum fun (p : ℕ) => log (1 - (1 : ℝ) / p) + (1 : ℝ) / p

/-- Identidad de Mertens en sumas parciales. -/
theorem log_partialProduct_add_partialSum_eq_partialMertensCorrection (n : ℕ) :
    log (partialProduct n) + partialSum n = partialMertensCorrection n := by
  unfold partialMertensCorrection
  rw [log_partialProduct_eq_sum, partialSum_eq_primesBelow_sum, ← Finset.sum_add_distrib]

theorem partialProduct_eq_exp_partialMertensCorrection_sub_partialSum {n : ℕ} (hn : 2 ≤ n) :
    partialProduct n = exp (partialMertensCorrection n - partialSum n) := by
  have hpos := partialProduct_pos hn
  have hlog : log (partialProduct n) = partialMertensCorrection n - partialSum n := by
    linarith [log_partialProduct_add_partialSum_eq_partialMertensCorrection n]
  calc
    partialProduct n = exp (log (partialProduct n)) := (exp_log hpos).symm
    _ = exp (partialMertensCorrection n - partialSum n) := by rw [hlog]

theorem partialProduct_eq_exp_mertensConstant_approx_sub_partialSum {n : ℕ} (hn : 2 ≤ n)
    (hM : partialMertensCorrection n = mertensPrimeCorrectionSum) :
    partialProduct n = exp (mertensPrimeCorrectionSum - partialSum n) := by
  rw [partialProduct_eq_exp_partialMertensCorrection_sub_partialSum hn, hM]

lemma partialMertensCorrection_term_le {n : ℕ} {p : ℕ} (hp : p ∈ (n + 1).primesBelow) :
    log (1 - (1 : ℝ) / p) + (1 : ℝ) / p ≤ 2 / (p : ℝ) ^ 2 := by
  have hprime := Nat.prime_of_mem_primesBelow hp
  have h := mertensPrimeCorrection_abs_le ⟨p, hprime⟩
  have heq : mertensPrimeCorrection ⟨p, hprime⟩ = log (1 - (1 : ℝ) / p) + (1 : ℝ) / p := by
    dsimp [mertensPrimeCorrection, primeR]
  rw [← heq]
  exact (abs_le.mp h).2

theorem partialMertensCorrection_le_two_mul_sum_inv_sq (n : ℕ) :
    partialMertensCorrection n ≤
      2 * ∑ p ∈ (n + 1).primesBelow, (1 : ℝ) / (p : ℝ) ^ 2 := by
  unfold partialMertensCorrection
  calc
    ∑ p ∈ (n + 1).primesBelow, (log (1 - (1 : ℝ) / p) + (1 : ℝ) / p)
        ≤ ∑ p ∈ (n + 1).primesBelow, (2 / (p : ℝ) ^ 2) :=
      Finset.sum_le_sum fun p hp => partialMertensCorrection_term_le hp
    _ = 2 * ∑ p ∈ (n + 1).primesBelow, (1 : ℝ) / (p : ℝ) ^ 2 := by
      simp [div_eq_mul_inv, Finset.mul_sum, mul_comm]

/-- La constante `M` es γ más la serie convergente de correcciones. -/
theorem mertensConstant_eq_gamma_add_correctionSeries :
    mertensConstant = eulerMascheroniConstant + ∑' p : Nat.Primes, mertensPrimeCorrection p := by
  rw [mertensConstant_eq_gamma_add_correctionSum, mertensPrimeCorrectionSum_eq_tsum]

lemma partialMertensCorrection_eq_sum_range (n : ℕ) :
    partialMertensCorrection n =
      ∑ k ∈ Finset.range (Nat.primeCounting n), mertensCorrectionIndexed k := by
  unfold partialMertensCorrection
  have hcard :
      Nat.primeCounting n = (n + 1).primesBelow.card := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.primesBelow_card_eq_primeCounting']
  symm
  have hrange :
      Finset.range (Nat.primeCounting n) = Finset.range ((n + 1).primesBelow.card) := by
    rw [hcard]
  rw [hrange]
  apply Finset.sum_bij (fun k _ => Nat.nth Nat.Prime k)
  · intro k hk
    have hk' : k < Nat.count Nat.Prime (n + 1) := by
      have h1 : k < (n + 1).primesBelow.card := Finset.mem_range.mp hk
      have h2 : (n + 1).primesBelow.card = Nat.count Nat.Prime (n + 1) := by
        simpa [Nat.primeCounting'] using Nat.primesBelow_card_eq_primeCounting' (n + 1)
      exact h2 ▸ h1
    exact Nat.mem_primesBelow.mpr
      ⟨Nat.nth_lt_of_lt_count (p := Nat.Prime) hk',
        Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k⟩
  · intro a ha b hb hab
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hab
  · intro p hp
    refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
    · simp only [Finset.mem_range]
      have hp' := Nat.prime_of_mem_primesBelow hp
      have hlt := Nat.lt_of_mem_primesBelow hp
      have hcount : Nat.count Nat.Prime p < Nat.count Nat.Prime (n + 1) := by
        calc
          Nat.count Nat.Prime p < Nat.count Nat.Prime (p + 1) :=
            Nat.count_lt_count_succ_iff.mpr hp'
          _ ≤ Nat.count Nat.Prime (n + 1) :=
            Nat.count_monotone Nat.Prime (Nat.succ_le_succ (Nat.le_of_lt_succ hlt))
      have hcard' : Nat.count Nat.Prime (n + 1) = (n + 1).primesBelow.card := by
        simpa [Nat.primeCounting'] using (Nat.primesBelow_card_eq_primeCounting' (n + 1)).symm
      exact Nat.lt_of_lt_of_eq hcount hcard'
    · exact Nat.nth_count (Nat.prime_of_mem_primesBelow hp)
  · intro k hk
    dsimp [mertensCorrectionIndexed, mertensPrimeCorrection, primeR]

/-- Las sumas parciales de correcciones convergen a la serie de Mertens. -/
theorem partialMertensCorrection_tendsto_atTop :
    Tendsto partialMertensCorrection atTop (𝓝 mertensPrimeCorrectionSum) := by
  rw [mertensPrimeCorrectionSum_eq_tsum_indexed, funext partialMertensCorrection_eq_sum_range]
  exact (summable_mertensCorrectionIndexed.hasSum.tendsto_sum_nat).comp
    Nat.tendsto_primeCounting

lemma partialProduct_mul_exp_partialSum_eq_exp_partialMertensCorrection {n : ℕ} (hn : 2 ≤ n) :
    partialProduct n * exp (partialSum n) = exp (partialMertensCorrection n) := by
  rw [partialProduct_eq_exp_partialMertensCorrection_sub_partialSum hn, ← exp_add,
    sub_add_cancel]

/-- `∏(1-1/p) · exp(∑1/p) → exp(∑' corrections)` por continuidad de `exp`. -/
theorem tendsto_partialProduct_mul_exp_partialSum :
    Tendsto (fun n => partialProduct n * exp (partialSum n)) atTop
      (𝓝 (exp mertensPrimeCorrectionSum)) := by
  have h_ev :
      ∀ᶠ n in atTop, partialProduct n * exp (partialSum n) = exp (partialMertensCorrection n) :=
    (eventually_ge_atTop 2).mono fun n hn =>
      partialProduct_mul_exp_partialSum_eq_exp_partialMertensCorrection hn
  exact Tendsto.congr' (EventuallyEq.symm h_ev)
    (Filter.Tendsto.rexp partialMertensCorrection_tendsto_atTop)

lemma partialMertensCorrection_bddAbove : BddAbove (Set.range partialMertensCorrection) :=
  partialMertensCorrection_tendsto_atTop.bddAbove_range

/-- La corrección menos la suma armónica prima diverge a `-∞`. -/
theorem partialMertensCorrection_sub_partialSum_tendsto_atBot :
    Tendsto (fun n => partialMertensCorrection n - partialSum n) atTop atBot := by
  rw [tendsto_atTop_atBot]
  intro M
  rcases partialMertensCorrection_bddAbove with ⟨B, hB⟩
  rcases (tendsto_atTop_atTop.mp tendsto_partialSum_atTop (B - M)) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hSn : B - M ≤ partialSum n := hN n hn
  have hCn : partialMertensCorrection n ≤ B := hB ⟨n, rfl⟩
  linarith

/-- El producto parcial `∏_{p≤n}(1-1/p)` tiende a `0`. -/
theorem partialProduct_tendsto_zero : Tendsto partialProduct atTop (𝓝 0) := by
  have h_ev : ∀ᶠ n in atTop, partialProduct n = exp (partialMertensCorrection n - partialSum n) :=
    (eventually_ge_atTop 2).mono fun n hn =>
      partialProduct_eq_exp_partialMertensCorrection_sub_partialSum hn
  exact Tendsto.congr' (EventuallyEq.symm h_ev)
    (tendsto_exp_atBot.comp partialMertensCorrection_sub_partialSum_tendsto_atBot)

/-!
### Demostración compuesta (sin PNT)

Cadena:
`log ∏ + S = C`  →  `∏ = exp(C - S)`  →  `C → M` acotado, `S → ∞`  →  `∏ → 0`, `∏·exp(S) → exp(M)`.
-/

/-- Convergencia del producto de Euler: correcciones, renormalización y producto crudo. -/
theorem mertens_product_convergence :
    Tendsto partialMertensCorrection atTop (𝓝 mertensPrimeCorrectionSum) ∧
      Tendsto (fun n => partialProduct n * exp (partialSum n)) atTop
        (𝓝 (exp mertensPrimeCorrectionSum)) ∧
      Tendsto partialProduct atTop (𝓝 0) :=
  ⟨partialMertensCorrection_tendsto_atTop, tendsto_partialProduct_mul_exp_partialSum,
    partialProduct_tendsto_zero⟩

lemma partialProduct_mul_exp_partialSum_add_gamma_eq_exp_partialMertensCorrection_add_gamma
    {n : ℕ} (hn : 2 ≤ n) :
    partialProduct n * exp (partialSum n + eulerMascheroniConstant) =
      exp (partialMertensCorrection n + eulerMascheroniConstant) := by
  rw [exp_add, ← mul_assoc, partialProduct_mul_exp_partialSum_eq_exp_partialMertensCorrection hn,
    ← exp_add]

/-- `∏ · exp(S + γ) → exp(M)` con `M = γ + ∑' corrections`. -/
theorem tendsto_partialProduct_mul_exp_partialSum_add_gamma :
    Tendsto (fun n => partialProduct n * exp (partialSum n + eulerMascheroniConstant)) atTop
      (𝓝 (exp mertensConstant)) := by
  have h_ev :
      ∀ᶠ n in atTop,
        partialProduct n * exp (partialSum n + eulerMascheroniConstant) =
          exp (partialMertensCorrection n + eulerMascheroniConstant) :=
    (eventually_ge_atTop 2).mono fun n hn =>
      partialProduct_mul_exp_partialSum_add_gamma_eq_exp_partialMertensCorrection_add_gamma hn
  have hlim :
      Tendsto (fun n => exp (partialMertensCorrection n + eulerMascheroniConstant)) atTop
        (𝓝 (exp (mertensPrimeCorrectionSum + eulerMascheroniConstant))) :=
    Filter.Tendsto.rexp
      (Tendsto.add partialMertensCorrection_tendsto_atTop
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => eulerMascheroniConstant) atTop
          (𝓝 eulerMascheroniConstant)))
  have htarget : exp mertensConstant =
      exp (mertensPrimeCorrectionSum + eulerMascheroniConstant) := by
    congr 1
    rw [mertensConstant_eq_gamma_add_correctionSum, add_comm]
  simpa [htarget] using Tendsto.congr' (EventuallyEq.symm h_ev) hlim

end ErdosReciprocals

/-! ### From `ErdosReciprocals/PrimeZeta.lean` -/

/-!
# Serie prima `∑_p p^r` (criterio de convergencia)

Reexporta el resultado exacto de Mathlib: converge iff `r < -1`.
En particular, `∑ 1/p` diverge y `∑ 1/p²` converge.
-/

namespace ErdosReciprocals

open Real

/-- Criterio de convergencia para potencias primas (Mathlib). -/
theorem primes_summable_rpow_iff {r : ℝ} :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ r) ↔ r < -1 :=
  Nat.Primes.summable_rpow

/-- La serie `∑_p p^{-2}` converge; base de la summability de Mertens. -/
theorem summable_primes_rpow_neg_two :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) :=
  (Nat.Primes.summable_rpow (r := (-2 : ℝ))).mpr (by norm_num : (-2 : ℝ) < -1)

/-- Versión con `primeR`. -/
theorem summable_primes_primeR_rpow {r : ℝ} (hr : r < -1) :
    Summable (fun p : Nat.Primes => primeR p ^ r) := by
  simpa [primeR_eq_cast] using
    (Nat.Primes.summable_rpow (r := r)).mpr hr

end ErdosReciprocals

end


/-!
## Source file: `MertensPNT/TTAOData.lean`
-/

/-!
# Certified computational tables

This file preserves the kernel-checked TTAO, wheel-sieve and segmented-sieve
numerical certificates shipped with this standalone package.
-/

/-! ### Certified finite tables -/

/-!
The constants in this section are stored directly in Lean.  This package ships
only the kernel-checkable layer:
exact finite identities and numerical brackets proved with `norm_num`.

# Empirical TTAO bridge in Lean

These finite certificates do not replace Mertens' theorem or PNT.  They are
published here as audited computational data points.
-/

set_option maxRecDepth 200000

@[expose] public section

namespace ErdosReciprocals

open Real

/-- Empirical proxy for `Δ(x) = (S - log log) - M` using `mertensConstantApprox`. -/
noncomputable def taoResidualProxy (sumMinusLogLog : ℝ) : ℝ :=
  sumMinusLogLog - mertensConstantApprox


/-! ## Exact Euler products at primorials -/
theorem primorial_survival_2 :
    (1 : ℝ) / 2 = (1 : ℝ) / 2 := by
  norm_num

theorem primorial_survival_6 :
    (2 : ℝ) / 6 = (1 : ℝ) / 3 := by
  norm_num

theorem primorial_euler_product_6 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3)
      = (1 : ℝ) / 3 := by
  norm_num

theorem primorial_survival_30 :
    (8 : ℝ) / 30 = (4 : ℝ) / 15 := by
  norm_num

theorem primorial_euler_product_30 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5)
      = (4 : ℝ) / 15 := by
  norm_num

theorem primorial_survival_210 :
    (48 : ℝ) / 210 = (8 : ℝ) / 35 := by
  norm_num

theorem primorial_euler_product_210 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7)
      = (8 : ℝ) / 35 := by
  norm_num

theorem primorial_survival_2310 :
    (480 : ℝ) / 2310 = (16 : ℝ) / 77 := by
  norm_num

theorem primorial_euler_product_2310 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7) *
      (1 - (1 : ℝ) / 11)
      = (16 : ℝ) / 77 := by
  norm_num

theorem primorial_survival_30030 :
    (5760 : ℝ) / 30030 = (192 : ℝ) / 1001 := by
  norm_num

theorem primorial_euler_product_30030 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7) *
      (1 - (1 : ℝ) / 11) * (1 - (1 : ℝ) / 13)
      = (192 : ℝ) / 1001 := by
  norm_num

theorem primorial_survival_510510 :
    (92160 : ℝ) / 510510 = (3072 : ℝ) / 17017 := by
  norm_num

theorem primorial_euler_product_510510 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7) *
      (1 - (1 : ℝ) / 11) * (1 - (1 : ℝ) / 13) * (1 - (1 : ℝ) / 17)
      = (3072 : ℝ) / 17017 := by
  norm_num

theorem primorial_survival_9699690 :
    (1658880 : ℝ) / 9699690 = (55296 : ℝ) / 323323 := by
  norm_num

theorem primorial_euler_product_9699690 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7) *
      (1 - (1 : ℝ) / 11) * (1 - (1 : ℝ) / 13) * (1 - (1 : ℝ) / 17) * (1 - (1 : ℝ) / 19)
      = (55296 : ℝ) / 323323 := by
  norm_num

/-! ## Wheel sieves (residuos coprimos y saltos C++) -/

/-! ### Wheel sieve mod 6 (`PATRONES/factorizador.cpp`) -/

def taoWheel6_modulus : ℕ := 6
def taoWheel6_phi : ℕ := 2
def taoWheel6_coprimeResidues : List ℕ :=
  [1, 5]

theorem taoWheel6_residue_count_eq_phi :
    taoWheel6_coprimeResidues.length = taoWheel6_phi := by
  rfl

theorem taoWheel6_survival_fraction :
    (taoWheel6_phi : ℝ) / taoWheel6_modulus =
      (2 : ℝ) / 6 := by
  unfold taoWheel6_phi taoWheel6_modulus
  norm_num

/-! ### Wheel sieve mod 30 (`PATRONES/factorizador.cpp`) -/

def taoWheel30_modulus : ℕ := 30
def taoWheel30_phi : ℕ := 8
def taoWheel30_coprimeResidues : List ℕ :=
  [1, 7, 11, 13, 17, 19, 23, 29]

theorem taoWheel30_residue_count_eq_phi :
    taoWheel30_coprimeResidues.length = taoWheel30_phi := by
  rfl

theorem taoWheel30_survival_fraction :
    (taoWheel30_phi : ℝ) / taoWheel30_modulus =
      (8 : ℝ) / 30 := by
  unfold taoWheel30_phi taoWheel30_modulus
  norm_num

def taoWheel30_jumpsDocumented : List ℕ :=
  [3, 2, 1, 2, 1, 2, 3, 1]

theorem taoWheel30_documented_jump_count_eq_phi :
    taoWheel30_jumpsDocumented.length = taoWheel30_phi := by
  rfl

theorem taoWheel30_documented_jumps_sum_eq_half_modulus :
    taoWheel30_jumpsDocumented.sum = taoWheel30_modulus / 2 := by
  unfold taoWheel30_jumpsDocumented taoWheel30_modulus
  decide

def taoWheel30_residueGaps : List ℕ :=
  [6, 4, 2, 4, 2, 4, 6, 2]

theorem taoWheel30_residue_gap_count_eq_phi :
    taoWheel30_residueGaps.length = taoWheel30_phi := by
  rfl

theorem taoWheel30_residue_gaps_sum_eq_modulus :
    taoWheel30_residueGaps.sum = taoWheel30_modulus := by
  unfold taoWheel30_residueGaps taoWheel30_modulus
  decide

/-! ### Wheel sieve mod 210 (`PATRONES/factorizador.cpp`) -/

def taoWheel210_modulus : ℕ := 210
def taoWheel210_phi : ℕ := 48
def taoWheel210_coprimeResidues : List ℕ :=
  [1, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103,
    107, 109, 113, 121, 127, 131, 137, 139, 143, 149, 151, 157,
    163, 167, 169, 173, 179, 181, 187, 191, 193, 197, 199, 209]

theorem taoWheel210_residue_count_eq_phi :
    taoWheel210_coprimeResidues.length = taoWheel210_phi := by
  rfl

theorem taoWheel210_survival_fraction :
    (taoWheel210_phi : ℝ) / taoWheel210_modulus =
      (48 : ℝ) / 210 := by
  unfold taoWheel210_phi taoWheel210_modulus
  norm_num

def taoWheel210_jumpsDocumented : List ℕ :=
  [5, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 3,
    3, 1, 3, 2, 1, 3, 2, 3, 4, 2, 1, 2,
    1, 2, 4, 3, 2, 3, 1, 2, 3, 1, 3, 3,
    2, 1, 2, 3, 1, 3, 2, 1, 2, 1, 5, 1]

theorem taoWheel210_documented_jump_count_eq_phi :
    taoWheel210_jumpsDocumented.length = taoWheel210_phi := by
  rfl

theorem taoWheel210_documented_jumps_sum_eq_half_modulus :
    taoWheel210_jumpsDocumented.sum = taoWheel210_modulus / 2 := by
  unfold taoWheel210_jumpsDocumented taoWheel210_modulus
  decide

def taoWheel210_residueGaps : List ℕ :=
  [10, 2, 4, 2, 4, 6, 2, 6, 4, 2, 4, 6,
    6, 2, 6, 4, 2, 6, 4, 6, 8, 4, 2, 4,
    2, 4, 8, 6, 4, 6, 2, 4, 6, 2, 6, 6,
    4, 2, 4, 6, 2, 6, 4, 2, 4, 2, 10, 2]

theorem taoWheel210_residue_gap_count_eq_phi :
    taoWheel210_residueGaps.length = taoWheel210_phi := by
  rfl

theorem taoWheel210_residue_gaps_sum_eq_modulus :
    taoWheel210_residueGaps.sum = taoWheel210_modulus := by
  unfold taoWheel210_residueGaps taoWheel210_modulus
  decide

/-! ## Tabla criba `CONJETURA-009-ERDOS/data/mertens_table.json` -/

/-- Límite de la criba segmentada (potencias de 10 hasta `10^11`). -/
def cribaTableLimit : ℕ := 100000000000
noncomputable def cribaTableFinalS : ℝ := 3.4934250719082645

/-- Criba segmentada: checkpoint `n = 1000`. -/
def cribaCp1000_n : ℕ := 1000
def cribaCp1000_pi : ℕ := 169
noncomputable def cribaCp1000_S : ℝ := 2.19907120745259
noncomputable def cribaCp1000_delta : ℝ := 0.004929260691740822
noncomputable def cribaCp1000_prod : ℝ := 0.08088502043101808
noncomputable def cribaCp1000_logLog : ℝ := 1.9326447339160655

theorem cribaCp1000_S_bracket :
    (2199071207451 : ℝ) / 1000000000000 < cribaCp1000_S ∧
      cribaCp1000_S < (1099535603727 : ℝ) / 500000000000 := by
  constructor <;> unfold cribaCp1000_S <;> norm_num

theorem cribaCp1000_delta_bracket :
    (492926069 : ℝ) / 100000000000 < cribaCp1000_delta ∧
      cribaCp1000_delta < (4929260693 : ℝ) / 1000000000000 := by
  constructor <;> unfold cribaCp1000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 10000`. -/
def cribaCp10000_n : ℕ := 10000
def cribaCp10000_pi : ℕ := 1230
noncomputable def cribaCp10000_S : ℝ := 2.4831598772825303
noncomputable def cribaCp10000_delta : ℝ := 0.0013358580699001088
noncomputable def cribaCp10000_prod : ℝ := 0.06087860824553999
noncomputable def cribaCp10000_logLog : ℝ := 2.2203268063678463

theorem cribaCp10000_S_bracket :
    (2483159877281 : ℝ) / 1000000000000 < cribaCp10000_S ∧
      cribaCp10000_S < (620789969321 : ℝ) / 250000000000 := by
  constructor <;> unfold cribaCp10000_S <;> norm_num

theorem cribaCp10000_delta_bracket :
    (333964517 : ℝ) / 250000000000 < cribaCp10000_delta ∧
      cribaCp10000_delta < (1335858071 : ℝ) / 1000000000000 := by
  constructor <;> unfold cribaCp10000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 100000`. -/
def cribaCp100000_n : ℕ := 100000
def cribaCp100000_pi : ℕ := 9593
noncomputable def cribaCp100000_S : ℝ := 2.70528217874729
noncomputable def cribaCp100000_delta : ℝ := 0.0003146082204499301
noncomputable def cribaCp100000_prod : ℝ := 0.04875243033646201
noncomputable def cribaCp100000_logLog : ℝ := 2.443470357682056

theorem cribaCp100000_S_bracket :
    (1352641089373 : ℝ) / 500000000000 < cribaCp100000_S ∧
      cribaCp100000_S < (2705282178749 : ℝ) / 1000000000000 := by
  constructor <;> unfold cribaCp100000_S <;> norm_num

theorem cribaCp100000_delta_bracket :
    (314608219 : ℝ) / 1000000000000 < cribaCp100000_delta ∧
      cribaCp100000_delta < (157304111 : ℝ) / 500000000000 := by
  constructor <;> unfold cribaCp100000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 1000000`. -/
def cribaCp1000000_n : ℕ := 1000000
def cribaCp1000000_pi : ℕ := 78499
noncomputable def cribaCp1000000_S : ℝ := 2.8873290995646936
noncomputable def cribaCp1000000_delta : ℝ := 3.9972243898844795e-05
noncomputable def cribaCp1000000_prod : ℝ := 0.04063816953356033
noncomputable def cribaCp1000000_logLog : ℝ := 2.625791914476011

theorem cribaCp1000000_S_bracket :
    (2887329099563 : ℝ) / 1000000000000 < cribaCp1000000_S ∧
      cribaCp1000000_S < (1443664549783 : ℝ) / 500000000000 := by
  constructor <;> unfold cribaCp1000000_S <;> norm_num

theorem cribaCp1000000_delta_bracket :
    (399721 : ℝ) / 10000000000 < cribaCp1000000_delta ∧
      cribaCp1000000_delta < (99931 : ℝ) / 2500000000 := by
  constructor <;> unfold cribaCp1000000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 10000000`. -/
def cribaCp10000000_n : ℕ := 10000000
def cribaCp10000000_pi : ℕ := 664580
noncomputable def cribaCp10000000_S : ℝ := 3.0414494812793724
noncomputable def cribaCp10000000_delta : ℝ := 9.674131319581392e-06
noncomputable def cribaCp10000000_prod : ℝ := 0.03483377104624719
noncomputable def cribaCp10000000_logLog : ℝ := 2.779942594303269

theorem cribaCp10000000_S_bracket :
    (1520724740639 : ℝ) / 500000000000 < cribaCp10000000_S ∧
      cribaCp10000000_S < (3041449481281 : ℝ) / 1000000000000 := by
  constructor <;> unfold cribaCp10000000_S <;> norm_num

theorem cribaCp10000000_delta_bracket :
    (4837 : ℝ) / 500000000 < cribaCp10000000_delta ∧
      cribaCp10000000_delta < (96743 : ℝ) / 10000000000 := by
  constructor <;> unfold cribaCp10000000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 100000000`. -/
def cribaCp100000000_n : ℕ := 100000000
def cribaCp100000000_pi : ℕ := 5761456
noncomputable def cribaCp100000000_S : ℝ := 3.1749752399205624
noncomputable def cribaCp100000000_delta : ℝ := 4.040147986827947e-06
noncomputable def cribaCp100000000_prod : ℝ := 0.030479721305794072
noncomputable def cribaCp100000000_logLog : ℝ := 2.9134739869277917

theorem cribaCp100000000_S_bracket :
    (3174975239919 : ℝ) / 1000000000000 < cribaCp100000000_S ∧
      cribaCp100000000_S < (1587487619961 : ℝ) / 500000000000 := by
  constructor <;> unfold cribaCp100000000_S <;> norm_num

theorem cribaCp100000000_delta_bracket :
    (101 : ℝ) / 25000000 < cribaCp100000000_delta ∧
      cribaCp100000000_delta < (40403 : ℝ) / 10000000000 := by
  constructor <;> unfold cribaCp100000000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 1000000000`. -/
def cribaCp1000000000_n : ℕ := 1000000000
def cribaCp1000000000_pi : ℕ := 50847535
noncomputable def cribaCp1000000000_S : ℝ := 3.292755719800315
noncomputable def cribaCp1000000000_delta : ℝ := 1.4843713560530603e-06
noncomputable def cribaCp1000000000_prod : ℝ := 0.027093154842787338
noncomputable def cribaCp1000000000_logLog : ℝ := 3.031257022584175

theorem cribaCp1000000000_S_bracket :
    (3292755719799 : ℝ) / 1000000000000 < cribaCp1000000000_S ∧
      cribaCp1000000000_S < (1646377859901 : ℝ) / 500000000000 := by
  constructor <;> unfold cribaCp1000000000_S <;> norm_num

theorem cribaCp1000000000_delta_bracket :
    (7421 : ℝ) / 5000000000 < cribaCp1000000000_delta ∧
      cribaCp1000000000_delta < (2969 : ℝ) / 2000000000 := by
  constructor <;> unfold cribaCp1000000000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 10000000000`. -/
def cribaCp10000000000_n : ℕ := 10000000000
def cribaCp10000000000_pi : ℕ := 455052512
noncomputable def cribaCp10000000000_S : ℝ := 3.3981153423420314
noncomputable def cribaCp10000000000_delta : ℝ := 5.912552460962672e-07
noncomputable def cribaCp10000000000_prod : ℝ := 0.024383861135675634
noncomputable def cribaCp10000000000_logLog : ℝ := 3.1366175382420014

theorem cribaCp10000000000_S_bracket :
    (3398115342341 : ℝ) / 1000000000000 < cribaCp10000000000_S ∧
      cribaCp10000000000_S < (424764417793 : ℝ) / 125000000000 := by
  constructor <;> unfold cribaCp10000000000_S <;> norm_num

theorem cribaCp10000000000_delta_bracket :
    (5911 : ℝ) / 10000000000 < cribaCp10000000000_delta ∧
      cribaCp10000000000_delta < (2957 : ℝ) / 5000000000 := by
  constructor <;> unfold cribaCp10000000000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 100000000000`. -/
def cribaCp100000000000_n : ℕ := 100000000000
def cribaCp100000000000_pi : ℕ := 4118054813
noncomputable def cribaCp100000000000_S : ℝ := 3.4934250719082645
noncomputable def cribaCp100000000000_delta : ℝ := 1.4101715395398173e-07
noncomputable def cribaCp100000000000_prod : ℝ := 0.022167156466509352
noncomputable def cribaCp100000000000_logLog : ℝ := 3.2319277180463266

theorem cribaCp100000000000_S_bracket :
    (3493425071907 : ℝ) / 1000000000000 < cribaCp100000000000_S ∧
      cribaCp100000000000_S < (349342507191 : ℝ) / 100000000000 := by
  constructor <;> unfold cribaCp100000000000_S <;> norm_num

theorem cribaCp100000000000_delta_bracket :
    (1409 : ℝ) / 10000000000 < cribaCp100000000000_delta ∧
      cribaCp100000000000_delta < (353 : ℝ) / 2500000000 := by
  constructor <;> unfold cribaCp100000000000_delta <;> norm_num

/-! ## Tendencia criba: `S(n)` ↑ y `Δ` ↓ en potencias de 10 -/

theorem criba_delta_tightens_1e3_to_1e11 :
    cribaCp100000000000_delta < cribaCp1000_delta := by
  unfold cribaCp100000000000_delta cribaCp1000_delta
  norm_num

theorem cribaCp100000000000_delta_lt_micro :
    cribaCp100000000000_delta < (1 / 1000000 : ℝ) := by
  unfold cribaCp100000000000_delta
  norm_num

theorem cribaCp100000000000_S_gt_cribaCp1000_S :
    cribaCp1000_S < cribaCp100000000000_S := by
  unfold cribaCp1000_S cribaCp100000000000_S
  norm_num

theorem cribaCp10000_S_gt_cribaCp1000_S :
    cribaCp1000_S < cribaCp10000_S := by
  unfold cribaCp1000_S cribaCp10000_S
  norm_num

theorem cribaCp10000_delta_lt_cribaCp1000_delta :
    cribaCp10000_delta < cribaCp1000_delta := by
  unfold cribaCp1000_delta cribaCp10000_delta
  norm_num

theorem cribaCp100000_S_gt_cribaCp10000_S :
    cribaCp10000_S < cribaCp100000_S := by
  unfold cribaCp10000_S cribaCp100000_S
  norm_num

theorem cribaCp100000_delta_lt_cribaCp10000_delta :
    cribaCp100000_delta < cribaCp10000_delta := by
  unfold cribaCp10000_delta cribaCp100000_delta
  norm_num

theorem cribaCp1000000_S_gt_cribaCp100000_S :
    cribaCp100000_S < cribaCp1000000_S := by
  unfold cribaCp100000_S cribaCp1000000_S
  norm_num

theorem cribaCp1000000_delta_lt_cribaCp100000_delta :
    cribaCp1000000_delta < cribaCp100000_delta := by
  unfold cribaCp100000_delta cribaCp1000000_delta
  norm_num

theorem cribaCp10000000_S_gt_cribaCp1000000_S :
    cribaCp1000000_S < cribaCp10000000_S := by
  unfold cribaCp1000000_S cribaCp10000000_S
  norm_num

theorem cribaCp10000000_delta_lt_cribaCp1000000_delta :
    cribaCp10000000_delta < cribaCp1000000_delta := by
  unfold cribaCp1000000_delta cribaCp10000000_delta
  norm_num

theorem cribaCp100000000_S_gt_cribaCp10000000_S :
    cribaCp10000000_S < cribaCp100000000_S := by
  unfold cribaCp10000000_S cribaCp100000000_S
  norm_num

theorem cribaCp100000000_delta_lt_cribaCp10000000_delta :
    cribaCp100000000_delta < cribaCp10000000_delta := by
  unfold cribaCp10000000_delta cribaCp100000000_delta
  norm_num

theorem cribaCp1000000000_S_gt_cribaCp100000000_S :
    cribaCp100000000_S < cribaCp1000000000_S := by
  unfold cribaCp100000000_S cribaCp1000000000_S
  norm_num

theorem cribaCp1000000000_delta_lt_cribaCp100000000_delta :
    cribaCp1000000000_delta < cribaCp100000000_delta := by
  unfold cribaCp100000000_delta cribaCp1000000000_delta
  norm_num

theorem cribaCp10000000000_S_gt_cribaCp1000000000_S :
    cribaCp1000000000_S < cribaCp10000000000_S := by
  unfold cribaCp1000000000_S cribaCp10000000000_S
  norm_num

theorem cribaCp10000000000_delta_lt_cribaCp1000000000_delta :
    cribaCp10000000000_delta < cribaCp1000000000_delta := by
  unfold cribaCp1000000000_delta cribaCp10000000000_delta
  norm_num

theorem cribaCp100000000000_S_gt_cribaCp10000000000_S :
    cribaCp10000000000_S < cribaCp100000000000_S := by
  unfold cribaCp10000000000_S cribaCp100000000000_S
  norm_num

theorem cribaCp100000000000_delta_lt_cribaCp10000000000_delta :
    cribaCp100000000000_delta < cribaCp10000000000_delta := by
  unfold cribaCp10000000000_delta cribaCp100000000000_delta
  norm_num

/-! ## Serie acumulativa `low_from_2` (1k … 10k primos desde 2) -/

/-- Checkpoint: x = 7919, 1000 primos en ventana. -/
def taoCheckpointX_7919 : ℕ := 7919

noncomputable def taoCp7919_sumOneOverP : ℝ := 2.457411276711362
noncomputable def taoCp7919_logLogX : ℝ := 2.194668002549939
noncomputable def taoCp7919_sumMinusLogLog : ℝ := 0.26274327416142285
noncomputable def taoCp7919_partialProduct : ℝ := 0.062466592946666254
noncomputable def taoCp7919_prodOverHeuristic : ℝ := 0.9987610575790983
noncomputable def taoCp7919_residualProxy : ℝ := 0.0012460613166390133

theorem taoCp7919_sumMinusLogLog_bracket :
    (3284290927 : ℝ) / 12500000000 < taoCp7919_sumMinusLogLog ∧
      taoCp7919_sumMinusLogLog < (262743274163 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoCp7919_sumMinusLogLog <;> norm_num

theorem taoCp7919_residualProxy_pos : 0 < taoCp7919_residualProxy := by
  unfold taoCp7919_residualProxy
  norm_num

theorem taoCp7919_residualProxy_bracket :
    (3115153 : ℝ) / 2500000000 < taoCp7919_residualProxy ∧
      taoCp7919_residualProxy < (2492123 : ℝ) / 2000000000 := by
  unfold taoCp7919_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 17389, 2000 primos en ventana. -/
def taoCheckpointX_17389 : ℕ := 17389

noncomputable def taoCp17389_sumOneOverP : ℝ := 2.5408915524876656
noncomputable def taoCp17389_logLogX : ℝ := 2.2786604783094333
noncomputable def taoCp17389_sumMinusLogLog : ℝ := 0.2622310741782323
noncomputable def taoCp17389_partialProduct : ℝ := 0.057463384743108595
noncomputable def taoCp17389_prodOverHeuristic : ℝ := 0.9992690893661653
noncomputable def taoCp17389_residualProxy : ℝ := 0.0007338613334484934

theorem taoCp17389_sumMinusLogLog_bracket :
    (262231074177 : ℝ) / 1000000000000 < taoCp17389_sumMinusLogLog ∧
      taoCp17389_sumMinusLogLog < (13111553709 : ℝ) / 50000000000 := by
  constructor <;> unfold taoCp17389_sumMinusLogLog <;> norm_num

theorem taoCp17389_residualProxy_pos : 0 < taoCp17389_residualProxy := by
  unfold taoCp17389_residualProxy
  norm_num

theorem taoCp17389_residualProxy_bracket :
    (1834653 : ℝ) / 2500000000 < taoCp17389_residualProxy ∧
      taoCp17389_residualProxy < (1467723 : ℝ) / 2000000000 := by
  unfold taoCp17389_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 27449, 3000 primos en ventana. -/
def taoCheckpointX_27449 : ℕ := 27449

noncomputable def taoCp27449_sumOneOverP : ℝ := 2.5863620272696917
noncomputable def taoCp27449_logLogX : ℝ := 2.324354903371252
noncomputable def taoCp27449_sumMinusLogLog : ℝ := 0.2620071238984396
noncomputable def taoCp27449_partialProduct : ℝ := 0.05490895397799993
noncomputable def taoCp27449_prodOverHeuristic : ℝ := 0.9994918497979041
noncomputable def taoCp27449_residualProxy : ℝ := 0.000509911053655776

theorem taoCp27449_sumMinusLogLog_bracket :
    (262007123897 : ℝ) / 1000000000000 < taoCp27449_sumMinusLogLog ∧
      taoCp27449_sumMinusLogLog < (2620071239 : ℝ) / 10000000000 := by
  constructor <;> unfold taoCp27449_sumMinusLogLog <;> norm_num

theorem taoCp27449_residualProxy_pos : 0 < taoCp27449_residualProxy := by
  unfold taoCp27449_residualProxy
  norm_num

theorem taoCp27449_residualProxy_bracket :
    (5099109 : ℝ) / 10000000000 < taoCp27449_residualProxy ∧
      taoCp27449_residualProxy < (637389 : ℝ) / 1250000000 := by
  unfold taoCp27449_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 37813, 4000 primos en ventana. -/
def taoCheckpointX_37813 : ℕ := 37813

noncomputable def taoCp37813_sumOneOverP : ℝ := 2.61727832686903
noncomputable def taoCp37813_logLogX : ℝ := 2.355216274604724
noncomputable def taoCp37813_sumMinusLogLog : ℝ := 0.262062052264306
noncomputable def taoCp37813_partialProduct : ℝ := 0.053237319763928294
noncomputable def taoCp37813_prodOverHeuristic : ℝ := 0.9994364691012536
noncomputable def taoCp37813_residualProxy : ℝ := 0.0005648394195221784

theorem taoCp37813_sumMinusLogLog_bracket :
    (262062052263 : ℝ) / 1000000000000 < taoCp37813_sumMinusLogLog ∧
      taoCp37813_sumMinusLogLog < (131031026133 : ℝ) / 500000000000 := by
  constructor <;> unfold taoCp37813_sumMinusLogLog <;> norm_num

theorem taoCp37813_residualProxy_pos : 0 < taoCp37813_residualProxy := by
  unfold taoCp37813_residualProxy
  norm_num

theorem taoCp37813_residualProxy_bracket :
    (5648393 : ℝ) / 10000000000 < taoCp37813_residualProxy ∧
      taoCp37813_residualProxy < (1412099 : ℝ) / 2500000000 := by
  unfold taoCp37813_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 48611, 5000 primos en ventana. -/
def taoCheckpointX_48611 : ℕ := 48611

noncomputable def taoCp48611_sumOneOverP : ℝ := 2.6405528434271104
noncomputable def taoCp48611_logLogX : ℝ := 2.3787685283293087
noncomputable def taoCp48611_sumMinusLogLog : ℝ := 0.26178431509780165
noncomputable def taoCp48611_partialProduct : ℝ := 0.05201254091326835
noncomputable def taoCp48611_prodOverHeuristic : ℝ := 0.9997138161204105
noncomputable def taoCp48611_residualProxy : ℝ := 0.00028710225301781245

theorem taoCp48611_sumMinusLogLog_bracket :
    (32723039387 : ℝ) / 125000000000 < taoCp48611_sumMinusLogLog ∧
      taoCp48611_sumMinusLogLog < (261784315099 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoCp48611_sumMinusLogLog <;> norm_num

theorem taoCp48611_residualProxy_pos : 0 < taoCp48611_residualProxy := by
  unfold taoCp48611_residualProxy
  norm_num

theorem taoCp48611_residualProxy_bracket :
    (2871021 : ℝ) / 10000000000 < taoCp48611_residualProxy ∧
      taoCp48611_residualProxy < (179439 : ℝ) / 625000000 := by
  unfold taoCp48611_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 59359, 6000 primos en ventana. -/
def taoCheckpointX_59359 : ℕ := 59359

noncomputable def taoCp59359_sumOneOverP : ℝ := 2.6591357546549808
noncomputable def taoCp59359_logLogX : ℝ := 2.397109421492482
noncomputable def taoCp59359_sumMinusLogLog : ℝ := 0.26202633316249857
noncomputable def taoCp59359_partialProduct : ℝ := 0.051054912871272944
noncomputable def taoCp59359_prodOverHeuristic : ℝ := 0.9994717234391494
noncomputable def taoCp59359_residualProxy : ℝ := 0.0005291203177147374

theorem taoCp59359_sumMinusLogLog_bracket :
    (262026333161 : ℝ) / 1000000000000 < taoCp59359_sumMinusLogLog ∧
      taoCp59359_sumMinusLogLog < (65506583291 : ℝ) / 250000000000 := by
  constructor <;> unfold taoCp59359_sumMinusLogLog <;> norm_num

theorem taoCp59359_residualProxy_pos : 0 < taoCp59359_residualProxy := by
  unfold taoCp59359_residualProxy
  norm_num

theorem taoCp59359_residualProxy_bracket :
    (2645601 : ℝ) / 5000000000 < taoCp59359_residualProxy ∧
      taoCp59359_residualProxy < (1058241 : ℝ) / 2000000000 := by
  unfold taoCp59359_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 70657, 7000 primos en ventana. -/
def taoCheckpointX_70657 : ℕ := 70657

noncomputable def taoCp70657_sumOneOverP : ℝ := 2.6745562902631397
noncomputable def taoCp70657_logLogX : ℝ := 2.4128369482081533
noncomputable def taoCp70657_sumMinusLogLog : ℝ := 0.26171934205498637
noncomputable def taoCp70657_partialProduct : ℝ := 0.05027365194295217
noncomputable def taoCp70657_prodOverHeuristic : ℝ := 0.99977848030009
noncomputable def taoCp70657_residualProxy : ℝ := 0.0002221292102025374

theorem taoCp70657_sumMinusLogLog_bracket :
    (261719342053 : ℝ) / 1000000000000 < taoCp70657_sumMinusLogLog ∧
      taoCp70657_sumMinusLogLog < (32714917757 : ℝ) / 125000000000 := by
  constructor <;> unfold taoCp70657_sumMinusLogLog <;> norm_num

theorem taoCp70657_residualProxy_pos : 0 < taoCp70657_residualProxy := by
  unfold taoCp70657_residualProxy
  norm_num

theorem taoCp70657_residualProxy_bracket :
    (2221291 : ℝ) / 10000000000 < taoCp70657_residualProxy ∧
      taoCp70657_residualProxy < (1110647 : ℝ) / 5000000000 := by
  unfold taoCp70657_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 81799, 8000 primos en ventana. -/
def taoCheckpointX_81799 : ℕ := 81799

noncomputable def taoCp81799_sumOneOverP : ℝ := 2.687700665463508
noncomputable def taoCp81799_logLogX : ℝ := 2.425865903492886
noncomputable def taoCp81799_sumMinusLogLog : ℝ := 0.2618347619706216
noncomputable def taoCp81799_partialProduct : ℝ := 0.04961715594371256
noncomputable def taoCp81799_prodOverHeuristic : ℝ := 0.9996630060955574
noncomputable def taoCp81799_residualProxy : ℝ := 0.0003375491258377772

theorem taoCp81799_sumMinusLogLog_bracket :
    (261834761969 : ℝ) / 1000000000000 < taoCp81799_sumMinusLogLog ∧
      taoCp81799_sumMinusLogLog < (65458690493 : ℝ) / 250000000000 := by
  constructor <;> unfold taoCp81799_sumMinusLogLog <;> norm_num

theorem taoCp81799_residualProxy_pos : 0 < taoCp81799_residualProxy := by
  unfold taoCp81799_residualProxy
  norm_num

theorem taoCp81799_residualProxy_bracket :
    (337549 : ℝ) / 1000000000 < taoCp81799_residualProxy ∧
      taoCp81799_residualProxy < (3375493 : ℝ) / 10000000000 := by
  unfold taoCp81799_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 93179, 9000 primos en ventana. -/
def taoCheckpointX_93179 : ℕ := 93179

noncomputable def taoCp93179_sumOneOverP : ℝ := 2.6991401810819573
noncomputable def taoCp93179_logLogX : ℝ := 2.4373150617113732
noncomputable def taoCp93179_sumMinusLogLog : ℝ := 0.26182511937058406
noncomputable def taoCp93179_partialProduct : ℝ := 0.04905279066790089
noncomputable def taoCp93179_prodOverHeuristic : ℝ := 0.999672579988035
noncomputable def taoCp93179_residualProxy : ℝ := 0.0003279065258002256

theorem taoCp93179_sumMinusLogLog_bracket :
    (261825119369 : ℝ) / 1000000000000 < taoCp93179_sumMinusLogLog ∧
      taoCp93179_sumMinusLogLog < (65456279843 : ℝ) / 250000000000 := by
  constructor <;> unfold taoCp93179_sumMinusLogLog <;> norm_num

theorem taoCp93179_residualProxy_pos : 0 < taoCp93179_residualProxy := by
  unfold taoCp93179_residualProxy
  norm_num

theorem taoCp93179_residualProxy_bracket :
    (409883 : ℝ) / 1250000000 < taoCp93179_residualProxy ∧
      taoCp93179_residualProxy < (3279067 : ℝ) / 10000000000 := by
  unfold taoCp93179_residualProxy
  constructor <;> norm_num

/-- Checkpoint principal: x = 104729. -/
def taoCheckpointX : ℕ := 104729

noncomputable def taoCp104729_sumOneOverP : ℝ := 2.709258248797317
noncomputable def taoCp104729_logLogX : ℝ := 2.4474757168532646
noncomputable def taoCp104729_sumMinusLogLog : ℝ := 0.26178253194405254
noncomputable def taoCp104729_partialProduct : ℝ := 0.048558971171659714
noncomputable def taoCp104729_prodOverHeuristic : ℝ := 0.9997151031452159
noncomputable def taoCp104729_residualProxy : ℝ := 0.00028531909926871046

theorem taoCp104729_sumMinusLogLog_bracket :
    (261782531943 : ℝ) / 1000000000000 < taoCp104729_sumMinusLogLog ∧
      taoCp104729_sumMinusLogLog < (130891265973 : ℝ) / 500000000000 := by
  constructor <;> unfold taoCp104729_sumMinusLogLog <;> norm_num

theorem taoCp104729_residualProxy_pos : 0 < taoCp104729_residualProxy := by
  unfold taoCp104729_residualProxy
  norm_num

theorem taoCp104729_residualProxy_bracket :
    (2853189 : ℝ) / 10000000000 < taoCp104729_residualProxy ∧
      taoCp104729_residualProxy < (356649 : ℝ) / 1250000000 := by
  unfold taoCp104729_residualProxy
  constructor <;> norm_num

theorem taoEmpiricalSumMinusLogLog_near_mertensConstantApprox :
    |taoCp104729_sumMinusLogLog - mertensConstantApprox| < (1 / 1000 : ℝ) := by
  unfold taoCp104729_sumMinusLogLog mertensConstantApprox
  norm_num

/-- Heurística Tao: `∏ / (e^{-γ}/log x) ≈ 1` en x = 104729. -/
theorem taoEmpiricalProdOverHeuristic_near_one :
    (999715103 : ℝ) / 1000000000 < taoCp104729_prodOverHeuristic ∧
      taoCp104729_prodOverHeuristic < (9997151033 : ℝ) / 10000000000 := by
  constructor <;> unfold taoCp104729_prodOverHeuristic <;> norm_num

/-! ## Ventana local `high_from_10M` (10k primos desde 10M) -/

/-- Checkpoint (suma local, no acumulativa): x = 10016051, 1000 primos en ventana. -/
def taoCheckpointX_High10M_10016051 : ℕ := 10016051

noncomputable def taoHigh10M_Cp10016051_sumOneOverP : ℝ := 9.991925549458609e-05
noncomputable def taoHigh10M_Cp10016051_logLogX : ℝ := 2.7800420932422854
noncomputable def taoHigh10M_Cp10016051_sumMinusLogLog : ℝ := -2.779942173986791
noncomputable def taoHigh10M_Cp10016051_partialProduct : ℝ := 0.9999000857312778
noncomputable def taoHigh10M_Cp10016051_prodOverHeuristic : ℝ := 28.707483528075453
noncomputable def taoHigh10M_Cp10016051_residualProxy : ℝ := -3.0414393868315748

theorem taoHigh10M_Cp10016051_sumMinusLogLog_bracket :
    (-2779942173987 : ℝ) / 1000000000000 < taoHigh10M_Cp10016051_sumMinusLogLog ∧
      taoHigh10M_Cp10016051_sumMinusLogLog < (-86873192937 : ℝ) / 31250000000 := by
  constructor <;> unfold taoHigh10M_Cp10016051_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10016051_residualProxy_neg : taoHigh10M_Cp10016051_residualProxy < 0 := by
  unfold taoHigh10M_Cp10016051_residualProxy
  norm_num

theorem taoHigh10M_Cp10016051_residualProxy_bracket :
    (-30414393869 : ℝ) / 10000000000 < taoHigh10M_Cp10016051_residualProxy ∧
      taoHigh10M_Cp10016051_residualProxy < (-15207196933 : ℝ) / 5000000000 := by
  unfold taoHigh10M_Cp10016051_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10032181, 2000 primos en ventana. -/
def taoCheckpointX_High10M_10032181 : ℕ := 10032181

noncomputable def taoHigh10M_Cp10032181_sumOneOverP : ℝ := 0.00019967937720542848
noncomputable def taoHigh10M_Cp10032181_logLogX : ℝ := 2.78014191144857
noncomputable def taoHigh10M_Cp10032181_sumMinusLogLog : ℝ := -2.7799422320713645
noncomputable def taoHigh10M_Cp10032181_partialProduct : ℝ := 0.9998003405474292
noncomputable def taoHigh10M_Cp10032181_prodOverHeuristic : ℝ := 28.707485195394568
noncomputable def taoHigh10M_Cp10032181_residualProxy : ℝ := -3.0414394449161484

theorem taoHigh10M_Cp10032181_sumMinusLogLog_bracket :
    (-347492779009 : ℝ) / 125000000000 < taoHigh10M_Cp10032181_sumMinusLogLog ∧
      taoHigh10M_Cp10032181_sumMinusLogLog < (-2779942232069 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoHigh10M_Cp10032181_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10032181_residualProxy_neg : taoHigh10M_Cp10032181_residualProxy < 0 := by
  unfold taoHigh10M_Cp10032181_residualProxy
  norm_num

theorem taoHigh10M_Cp10032181_residualProxy_bracket :
    (-608287889 : ℝ) / 200000000 < taoHigh10M_Cp10032181_residualProxy ∧
      taoHigh10M_Cp10032181_residualProxy < (-30414394447 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10032181_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10047881, 3000 primos en ventana. -/
def taoCheckpointX_High10M_10047881 : ℕ := 10047881

noncomputable def taoHigh10M_Cp10047881_sumOneOverP : ℝ := 0.00029928090284024004
noncomputable def taoHigh10M_Cp10047881_logLogX : ℝ := 2.7802389051055623
noncomputable def taoHigh10M_Cp10047881_sumMinusLogLog : ℝ := -2.779939624202722
noncomputable def taoHigh10M_Cp10047881_partialProduct : ℝ := 0.9997007638622997
noncomputable def taoHigh10M_Cp10047881_prodOverHeuristic : ℝ := 28.707410329999373
noncomputable def taoHigh10M_Cp10047881_residualProxy : ℝ := -3.041436837047506

theorem taoHigh10M_Cp10047881_sumMinusLogLog_bracket :
    (-2779939624203 : ℝ) / 1000000000000 < taoHigh10M_Cp10047881_sumMinusLogLog ∧
      taoHigh10M_Cp10047881_sumMinusLogLog < (-13899698121 : ℝ) / 5000000000 := by
  constructor <;> unfold taoHigh10M_Cp10047881_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10047881_residualProxy_neg : taoHigh10M_Cp10047881_residualProxy < 0 := by
  unfold taoHigh10M_Cp10047881_residualProxy
  norm_num

theorem taoHigh10M_Cp10047881_residualProxy_bracket :
    (-30414368371 : ℝ) / 10000000000 < taoHigh10M_Cp10047881_residualProxy ∧
      taoHigh10M_Cp10047881_residualProxy < (-1900898023 : ℝ) / 625000000 := by
  unfold taoHigh10M_Cp10047881_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10063771, 4000 primos en ventana. -/
def taoCheckpointX_High10M_10063771 : ℕ := 10063771

noncomputable def taoHigh10M_Cp10063771_sumOneOverP : ℝ := 0.0003987251876420962
noncomputable def taoHigh10M_Cp10063771_logLogX : ℝ := 2.7803369088211594
noncomputable def taoHigh10M_Cp10063771_sumMinusLogLog : ℝ := -2.7799381836335173
noncomputable def taoHigh10M_Cp10063771_partialProduct : ℝ := 0.9996013542728166
noncomputable def taoHigh10M_Cp10063771_prodOverHeuristic : ℝ := 28.707368974875905
noncomputable def taoHigh10M_Cp10063771_residualProxy : ℝ := -3.041435396478301

theorem taoHigh10M_Cp10063771_sumMinusLogLog_bracket :
    (-1389969091817 : ℝ) / 500000000000 < taoHigh10M_Cp10063771_sumMinusLogLog ∧
      taoHigh10M_Cp10063771_sumMinusLogLog < (-2779938183631 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoHigh10M_Cp10063771_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10063771_residualProxy_neg : taoHigh10M_Cp10063771_residualProxy < 0 := by
  unfold taoHigh10M_Cp10063771_residualProxy
  norm_num

theorem taoHigh10M_Cp10063771_residualProxy_bracket :
    (-6082870793 : ℝ) / 2000000000 < taoHigh10M_Cp10063771_residualProxy ∧
      taoHigh10M_Cp10063771_residualProxy < (-15207176981 : ℝ) / 5000000000 := by
  unfold taoHigh10M_Cp10063771_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10080061, 5000 primos en ventana. -/
def taoCheckpointX_High10M_10080061 : ℕ := 10080061

noncomputable def taoHigh10M_Cp10080061_sumOneOverP : ℝ := 0.0004980100294140917
noncomputable def taoHigh10M_Cp10080061_logLogX : ℝ := 2.7804372091429688
noncomputable def taoHigh10M_Cp10080061_sumMinusLogLog : ℝ := -2.7799391991135547
noncomputable def taoHigh10M_Cp10080061_partialProduct : ℝ := 0.9995021139322078
noncomputable def taoHigh10M_Cp10080061_prodOverHeuristic : ℝ := 28.707398126509318
noncomputable def taoHigh10M_Cp10080061_residualProxy : ℝ := -3.0414364119583386

theorem taoHigh10M_Cp10080061_sumMinusLogLog_bracket :
    (-1389969599557 : ℝ) / 500000000000 < taoHigh10M_Cp10080061_sumMinusLogLog ∧
      taoHigh10M_Cp10080061_sumMinusLogLog < (-2779939199111 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoHigh10M_Cp10080061_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10080061_residualProxy_neg : taoHigh10M_Cp10080061_residualProxy < 0 := by
  unfold taoHigh10M_Cp10080061_residualProxy
  norm_num

theorem taoHigh10M_Cp10080061_residualProxy_bracket :
    (-760359103 : ℝ) / 250000000 < taoHigh10M_Cp10080061_residualProxy ∧
      taoHigh10M_Cp10080061_residualProxy < (-30414364117 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10080061_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10096169, 6000 primos en ventana. -/
def taoCheckpointX_High10M_10096169 : ℕ := 10096169

noncomputable def taoHigh10M_Cp10096169_sumOneOverP : ℝ := 0.0005971372015084941
noncomputable def taoHigh10M_Cp10096169_logLogX : ℝ := 2.780536219733681
noncomputable def taoHigh10M_Cp10096169_sumMinusLogLog : ℝ := -2.779939082532173
noncomputable def taoHigh10M_Cp10096169_partialProduct : ℝ := 0.9994030410197341
noncomputable def taoHigh10M_Cp10096169_prodOverHeuristic : ℝ := 28.70739477962042
noncomputable def taoHigh10M_Cp10096169_residualProxy : ℝ := -3.0414362953769567

theorem taoHigh10M_Cp10096169_sumMinusLogLog_bracket :
    (-2779939082533 : ℝ) / 1000000000000 < taoHigh10M_Cp10096169_sumMinusLogLog ∧
      taoHigh10M_Cp10096169_sumMinusLogLog < (-277993908253 : ℝ) / 100000000000 := by
  constructor <;> unfold taoHigh10M_Cp10096169_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10096169_residualProxy_neg : taoHigh10M_Cp10096169_residualProxy < 0 := by
  unfold taoHigh10M_Cp10096169_residualProxy
  norm_num

theorem taoHigh10M_Cp10096169_residualProxy_bracket :
    (-15207181477 : ℝ) / 5000000000 < taoHigh10M_Cp10096169_residualProxy ∧
      taoHigh10M_Cp10096169_residualProxy < (-30414362951 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10096169_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10112299, 7000 primos en ventana. -/
def taoCheckpointX_High10M_10112299 : ℕ := 10112299

noncomputable def taoHigh10M_Cp10112299_sumOneOverP : ℝ := 0.0006961052425863461
noncomputable def taoHigh10M_Cp10112299_logLogX : ℝ := 2.7806351975879138
noncomputable def taoHigh10M_Cp10112299_sumMinusLogLog : ℝ := -2.7799390923453275
noncomputable def taoHigh10M_Cp10112299_partialProduct : ℝ := 0.9993041369478766
noncomputable def taoHigh10M_Cp10112299_prodOverHeuristic : ℝ := 28.707395061189985
noncomputable def taoHigh10M_Cp10112299_residualProxy : ℝ := -3.0414363051901114

theorem taoHigh10M_Cp10112299_sumMinusLogLog_bracket :
    (-1389969546173 : ℝ) / 500000000000 < taoHigh10M_Cp10112299_sumMinusLogLog ∧
      taoHigh10M_Cp10112299_sumMinusLogLog < (-2779939092343 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoHigh10M_Cp10112299_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10112299_residualProxy_neg : taoHigh10M_Cp10112299_residualProxy < 0 := by
  unfold taoHigh10M_Cp10112299_residualProxy
  norm_num

theorem taoHigh10M_Cp10112299_residualProxy_bracket :
    (-7603590763 : ℝ) / 2500000000 < taoHigh10M_Cp10112299_residualProxy ∧
      taoHigh10M_Cp10112299_residualProxy < (-30414363049 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10112299_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10128439, 8000 primos en ventana. -/
def taoCheckpointX_High10M_10128439 : ℕ := 10128439

noncomputable def taoHigh10M_Cp10128439_sumOneOverP : ℝ := 0.0007949156195997105
noncomputable def taoHigh10M_Cp10128439_logLogX : ℝ := 2.780734069124213
noncomputable def taoHigh10M_Cp10128439_sumMinusLogLog : ℝ := -2.779939153504613
noncomputable def taoHigh10M_Cp10128439_partialProduct : ℝ := 0.9992054002026638
noncomputable def taoHigh10M_Cp10128439_prodOverHeuristic : ℝ := 28.707396816773677
noncomputable def taoHigh10M_Cp10128439_residualProxy : ℝ := -3.041436366349397

theorem taoHigh10M_Cp10128439_sumMinusLogLog_bracket :
    (-555987830701 : ℝ) / 200000000000 < taoHigh10M_Cp10128439_sumMinusLogLog ∧
      taoHigh10M_Cp10128439_sumMinusLogLog < (-1389969576751 : ℝ) / 500000000000 := by
  constructor <;> unfold taoHigh10M_Cp10128439_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10128439_residualProxy_neg : taoHigh10M_Cp10128439_residualProxy < 0 := by
  unfold taoHigh10M_Cp10128439_residualProxy
  norm_num

theorem taoHigh10M_Cp10128439_residualProxy_bracket :
    (-1900897729 : ℝ) / 625000000 < taoHigh10M_Cp10128439_residualProxy ∧
      taoHigh10M_Cp10128439_residualProxy < (-30414363661 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10128439_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10144187, 9000 primos en ventana. -/
def taoCheckpointX_High10M_10144187 : ℕ := 10144187

noncomputable def taoHigh10M_Cp10144187_sumOneOverP : ℝ := 0.0008935687840663146
noncomputable def taoHigh10M_Cp10144187_logLogX : ℝ := 2.7808303781756627
noncomputable def taoHigh10M_Cp10144187_sumMinusLogLog : ℝ := -2.7799368093915966
noncomputable def taoHigh10M_Cp10144187_partialProduct : ℝ := 0.9991068302853175
noncomputable def taoHigh10M_Cp10144187_prodOverHeuristic : ℝ := 28.707329523330326
noncomputable def taoHigh10M_Cp10144187_residualProxy : ℝ := -3.0414340222363805

theorem taoHigh10M_Cp10144187_sumMinusLogLog_bracket :
    (-173746050587 : ℝ) / 62500000000 < taoHigh10M_Cp10144187_sumMinusLogLog ∧
      taoHigh10M_Cp10144187_sumMinusLogLog < (-2779936809389 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoHigh10M_Cp10144187_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10144187_residualProxy_neg : taoHigh10M_Cp10144187_residualProxy < 0 := by
  unfold taoHigh10M_Cp10144187_residualProxy
  norm_num

theorem taoHigh10M_Cp10144187_residualProxy_bracket :
    (-30414340223 : ℝ) / 10000000000 < taoHigh10M_Cp10144187_residualProxy ∧
      taoHigh10M_Cp10144187_residualProxy < (-1520717011 : ℝ) / 500000000 := by
  unfold taoHigh10M_Cp10144187_residualProxy
  constructor <;> norm_num

/-- Checkpoint principal (suma local, no acumulativa): x = 10160539. -/
def taoHigh10M_CheckpointX : ℕ := 10160539

noncomputable def taoHigh10M_Cp10160539_sumOneOverP : ℝ := 0.0009920674957481137
noncomputable def taoHigh10M_Cp10160539_logLogX : ℝ := 2.7809302131860036
noncomputable def taoHigh10M_Cp10160539_sumMinusLogLog : ℝ := -2.7799381456902554
noncomputable def taoHigh10M_Cp10160539_partialProduct : ℝ := 0.9990084243913625
noncomputable def taoHigh10M_Cp10160539_prodOverHeuristic : ℝ := 28.707367884782663
noncomputable def taoHigh10M_Cp10160539_residualProxy : ℝ := -3.0414353585350393

theorem taoHigh10M_Cp10160539_sumMinusLogLog_bracket :
    (-2779938145691 : ℝ) / 1000000000000 < taoHigh10M_Cp10160539_sumMinusLogLog ∧
      taoHigh10M_Cp10160539_sumMinusLogLog < (-347492268211 : ℝ) / 125000000000 := by
  constructor <;> unfold taoHigh10M_Cp10160539_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10160539_residualProxy_neg : taoHigh10M_Cp10160539_residualProxy < 0 := by
  unfold taoHigh10M_Cp10160539_residualProxy
  norm_num

theorem taoHigh10M_Cp10160539_residualProxy_bracket :
    (-15207176793 : ℝ) / 5000000000 < taoHigh10M_Cp10160539_residualProxy ∧
      taoHigh10M_Cp10160539_residualProxy < (-30414353583 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10160539_residualProxy
  constructor <;> norm_num

/-! ## Ventana local `millions_1M_10M` (~586k primos en [1M, 10M)) -/

/-- Checkpoint (suma local, no acumulativa): x = 1069363, 5000 primos en ventana. -/
def taoCheckpointX_Millions_1069363 : ℕ := 1069363

noncomputable def taoMillions_Cp1069363_sumOneOverP : ℝ := 0.004835758923991824
noncomputable def taoMillions_Cp1069363_logLogX : ℝ := 2.6306343631098255
noncomputable def taoMillions_Cp1069363_sumMinusLogLog : ℝ := -2.6257986041858334
noncomputable def taoMillions_Cp1069363_partialProduct : ℝ := 0.9951759122058744
noncomputable def taoMillions_Cp1069363_prodOverHeuristic : ℝ := 24.606589348071424
noncomputable def taoMillions_Cp1069363_residualProxy : ℝ := -2.8872958170306173

theorem taoMillions_Cp1069363_sumMinusLogLog_bracket :
    (-1312899302093 : ℝ) / 500000000000 < taoMillions_Cp1069363_sumMinusLogLog ∧
      taoMillions_Cp1069363_sumMinusLogLog < (-2625798604183 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoMillions_Cp1069363_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp1069363_residualProxy_neg : taoMillions_Cp1069363_residualProxy < 0 := by
  unfold taoMillions_Cp1069363_residualProxy
  norm_num

theorem taoMillions_Cp1069363_residualProxy_bracket :
    (-28872958171 : ℝ) / 10000000000 < taoMillions_Cp1069363_residualProxy ∧
      taoMillions_Cp1069363_residualProxy < (-3609119771 : ℝ) / 1250000000 := by
  unfold taoMillions_Cp1069363_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 2432587, 100000 primos en ventana. -/
def taoCheckpointX_Millions_2432587 : ℕ := 2432587

noncomputable def taoMillions_Cp2432587_sumOneOverP : ℝ := 0.06235128945765767
noncomputable def taoMillions_Cp2432587_logLogX : ℝ := 2.6881512475159632
noncomputable def taoMillions_Cp2432587_sumMinusLogLog : ℝ := -2.6257999580583054
noncomputable def taoMillions_Cp2432587_partialProduct : ℝ := 0.9395527543289707
noncomputable def taoMillions_Cp2432587_prodOverHeuristic : ℝ := 24.60662220917977
noncomputable def taoMillions_Cp2432587_residualProxy : ℝ := -2.8872971709030892

theorem taoMillions_Cp2432587_sumMinusLogLog_bracket :
    (-2625799958059 : ℝ) / 1000000000000 < taoMillions_Cp2432587_sumMinusLogLog ∧
      taoMillions_Cp2432587_sumMinusLogLog < (-328224994757 : ℝ) / 125000000000 := by
  constructor <;> unfold taoMillions_Cp2432587_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp2432587_residualProxy_neg : taoMillions_Cp2432587_residualProxy < 0 := by
  unfold taoMillions_Cp2432587_residualProxy
  norm_num

theorem taoMillions_Cp2432587_residualProxy_bracket :
    (-2887297171 : ℝ) / 1000000000 < taoMillions_Cp2432587_residualProxy ∧
      taoMillions_Cp2432587_residualProxy < (-28872971707 : ℝ) / 10000000000 := by
  unfold taoMillions_Cp2432587_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 3928667, 200000 primos en ventana. -/
def taoCheckpointX_Millions_3928667 : ℕ := 3928667

noncomputable def taoMillions_Cp3928667_sumOneOverP : ℝ := 0.09443317011207081
noncomputable def taoMillions_Cp3928667_logLogX : ℝ := 2.720229777390412
noncomputable def taoMillions_Cp3928667_sumMinusLogLog : ℝ := -2.625796607278341
noncomputable def taoMillions_Cp3928667_partialProduct : ℝ := 0.9098885166875568
noncomputable def taoMillions_Cp3928667_prodOverHeuristic : ℝ := 24.606539628865995
noncomputable def taoMillions_Cp3928667_residualProxy : ℝ := -2.887293820123125

theorem taoMillions_Cp3928667_sumMinusLogLog_bracket :
    (-2625796607279 : ℝ) / 1000000000000 < taoMillions_Cp3928667_sumMinusLogLog ∧
      taoMillions_Cp3928667_sumMinusLogLog < (-656449151819 : ℝ) / 250000000000 := by
  constructor <;> unfold taoMillions_Cp3928667_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp3928667_residualProxy_neg : taoMillions_Cp3928667_residualProxy < 0 := by
  unfold taoMillions_Cp3928667_residualProxy
  norm_num

theorem taoMillions_Cp3928667_residualProxy_bracket :
    (-14436469101 : ℝ) / 5000000000 < taoMillions_Cp3928667_residualProxy ∧
      taoMillions_Cp3928667_residualProxy < (-28872938199 : ℝ) / 10000000000 := by
  unfold taoMillions_Cp3928667_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 5464031, 300000 primos en ventana. -/
def taoCheckpointX_Millions_5464031 : ℕ := 5464031

noncomputable def taoMillions_Cp5464031_sumOneOverP : ℝ := 0.11592961607639489
noncomputable def taoMillions_Cp5464031_logLogX : ℝ := 2.7417233339317644
noncomputable def taoMillions_Cp5464031_sumMinusLogLog : ℝ := -2.6257937178553696
noncomputable def taoMillions_Cp5464031_partialProduct : ℝ := 0.8905378754142584
noncomputable def taoMillions_Cp5464031_prodOverHeuristic : ℝ := 24.60646847289772
noncomputable def taoMillions_Cp5464031_residualProxy : ℝ := -2.8872909307001535

theorem taoMillions_Cp5464031_sumMinusLogLog_bracket :
    (-82056053683 : ℝ) / 31250000000 < taoMillions_Cp5464031_sumMinusLogLog ∧
      taoMillions_Cp5464031_sumMinusLogLog < (-2625793717853 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoMillions_Cp5464031_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp5464031_residualProxy_neg : taoMillions_Cp5464031_residualProxy < 0 := by
  unfold taoMillions_Cp5464031_residualProxy
  norm_num

theorem taoMillions_Cp5464031_residualProxy_bracket :
    (-7218227327 : ℝ) / 2500000000 < taoMillions_Cp5464031_residualProxy ∧
      taoMillions_Cp5464031_residualProxy < (-5774581861 : ℝ) / 2000000000 := by
  unfold taoMillions_Cp5464031_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 7028963, 400000 primos en ventana. -/
def taoCheckpointX_Millions_7028963 : ℕ := 7028963

noncomputable def taoMillions_Cp7028963_sumOneOverP : ℝ := 0.13202551167141097
noncomputable def taoMillions_Cp7028963_logLogX : ℝ := 2.7578271634475597
noncomputable def taoMillions_Cp7028963_sumMinusLogLog : ℝ := -2.6258016517761487
noncomputable def taoMillions_Cp7028963_partialProduct : ℝ := 0.8763186124736502
noncomputable def taoMillions_Cp7028963_prodOverHeuristic : ℝ := 24.60666366739903
noncomputable def taoMillions_Cp7028963_residualProxy : ℝ := -2.8872988646209325

theorem taoMillions_Cp7028963_sumMinusLogLog_bracket :
    (-2625801651777 : ℝ) / 1000000000000 < taoMillions_Cp7028963_sumMinusLogLog ∧
      taoMillions_Cp7028963_sumMinusLogLog < (-1312900825887 : ℝ) / 500000000000 := by
  constructor <;> unfold taoMillions_Cp7028963_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp7028963_residualProxy_neg : taoMillions_Cp7028963_residualProxy < 0 := by
  unfold taoMillions_Cp7028963_residualProxy
  norm_num

theorem taoMillions_Cp7028963_residualProxy_bracket :
    (-28872988647 : ℝ) / 10000000000 < taoMillions_Cp7028963_residualProxy ∧
      taoMillions_Cp7028963_residualProxy < (-7218247161 : ℝ) / 2500000000 := by
  unfold taoMillions_Cp7028963_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 8616547, 500000 primos en ventana. -/
def taoCheckpointX_Millions_8616547 : ℕ := 8616547

noncomputable def taoMillions_Cp8616547_sumOneOverP : ℝ := 0.14485477819817347
noncomputable def taoMillions_Cp8616547_logLogX : ℝ := 2.770661552837407
noncomputable def taoMillions_Cp8616547_sumMinusLogLog : ℝ := -2.6258067746392335
noncomputable def taoMillions_Cp8616547_partialProduct : ℝ := 0.8651478959777597
noncomputable def taoMillions_Cp8616547_prodOverHeuristic : ℝ := 24.60678970396996
noncomputable def taoMillions_Cp8616547_residualProxy : ℝ := -2.8873039874840174

theorem taoMillions_Cp8616547_sumMinusLogLog_bracket :
    (-32822584683 : ℝ) / 12500000000 < taoMillions_Cp8616547_sumMinusLogLog ∧
      taoMillions_Cp8616547_sumMinusLogLog < (-2625806774637 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoMillions_Cp8616547_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp8616547_residualProxy_neg : taoMillions_Cp8616547_residualProxy < 0 := by
  unfold taoMillions_Cp8616547_residualProxy
  norm_num

theorem taoMillions_Cp8616547_residualProxy_bracket :
    (-230984319 : ℝ) / 80000000 < taoMillions_Cp8616547_residualProxy ∧
      taoMillions_Cp8616547_residualProxy < (-28196328 : ℝ) / 9765625 := by
  unfold taoMillions_Cp8616547_residualProxy
  constructor <;> norm_num

/-- Checkpoint principal (suma local, no acumulativa): x = 9999991. -/
def taoMillions_CheckpointX : ℕ := 9999991

noncomputable def taoMillions_Cp9999991_sumOneOverP : ℝ := 0.15412128171203857
noncomputable def taoMillions_Cp9999991_logLogX : ℝ := 2.7799425384653804
noncomputable def taoMillions_Cp9999991_sumMinusLogLog : ℝ := -2.625821256753342
noncomputable def taoMillions_Cp9999991_partialProduct : ℝ := 0.8571680293616284
noncomputable def taoMillions_Cp9999991_prodOverHeuristic : ℝ := 24.6071460525909
noncomputable def taoMillions_Cp9999991_residualProxy : ℝ := -2.8873184695981258

theorem taoMillions_Cp9999991_sumMinusLogLog_bracket :
    (-1312910628377 : ℝ) / 500000000000 < taoMillions_Cp9999991_sumMinusLogLog ∧
      taoMillions_Cp9999991_sumMinusLogLog < (-2625821256751 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoMillions_Cp9999991_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp9999991_residualProxy_neg : taoMillions_Cp9999991_residualProxy < 0 := by
  unfold taoMillions_Cp9999991_residualProxy
  norm_num

theorem taoMillions_Cp9999991_residualProxy_bracket :
    (-3609148087 : ℝ) / 1250000000 < taoMillions_Cp9999991_residualProxy ∧
      taoMillions_Cp9999991_residualProxy < (-28873184693 : ℝ) / 10000000000 := by
  unfold taoMillions_Cp9999991_residualProxy
  constructor <;> norm_num

/-! ## Tendencia empírica `Δ_proxy` en escala baja (hacia PNT+ `Δ → 0`) -/

theorem taoResidualProxy_tightens_Cp7919_to_Cp104729 :
    taoCp104729_residualProxy < taoCp7919_residualProxy := by
  unfold taoCp7919_residualProxy taoCp104729_residualProxy
  norm_num

theorem taoCp104729_residualProxy_lt_thousandth :
    taoCp104729_residualProxy < (1 / 1000 : ℝ) := by
  unfold taoCp104729_residualProxy
  norm_num


/-! ## Contraste entre escalas (acumulativa vs ventana local) -/

/-- Escala baja acumulativa: `∏ / (e^{-γ}/log x) ≈ 1`. -/
theorem taoLow_prodOverHeuristic_near_one :
    taoCp104729_prodOverHeuristic < (2 : ℝ) := by
  unfold taoCp104729_prodOverHeuristic
  norm_num

/-- Ventana local 10M: la heurística Mertens-3 no aplica (producto ≈ 1 en ventana). -/
theorem taoHigh10M_prodOverHeuristic_gt_twenty :
    (20 : ℝ) < taoHigh10M_Cp10160539_prodOverHeuristic := by
  unfold taoHigh10M_Cp10160539_prodOverHeuristic
  norm_num

/-- Ventana local [1M,10M): mismo fenómeno en x ≈ 10⁷. -/
theorem taoMillions_prodOverHeuristic_gt_twenty :
    (20 : ℝ) < taoMillions_Cp9999991_prodOverHeuristic := by
  unfold taoMillions_Cp9999991_prodOverHeuristic
  norm_num

/-- Escala baja: `S - log log` cerca de `M`. Ventana 10M: suma local ≪ log log. -/
theorem taoLow_sumMinusLogLog_near_M :
    (1 / 4 : ℝ) < taoCp104729_sumMinusLogLog ∧
      taoCp104729_sumMinusLogLog < (1 / 2 : ℝ) := by
  constructor <;> unfold taoCp104729_sumMinusLogLog <;> norm_num

theorem taoHigh10M_sumMinusLogLog_far_below_loglog :
    taoHigh10M_Cp10160539_sumMinusLogLog < (-2 : ℝ) := by
  unfold taoHigh10M_Cp10160539_sumMinusLogLog
  norm_num


/-! ## Normalización de gaps `g_n / log p_n` -/
noncomputable def taoGapMean_low_from_2 : ℝ := 1.0041835788042288
theorem taoGapMean_low_from_2_near_one :
    (10041835787 : ℝ) / 10000000000 < taoGapMean_low_from_2 ∧
      taoGapMean_low_from_2 < (1004183579 : ℝ) / 1000000000 := by
  constructor <;> unfold taoGapMean_low_from_2 <;> norm_num

noncomputable def taoGapMean_high_from_10M : ℝ := 0.9955058562947525
theorem taoGapMean_high_from_10M_near_one :
    (9955058561 : ℝ) / 10000000000 < taoGapMean_high_from_10M ∧
      taoGapMean_high_from_10M < (2488764641 : ℝ) / 2500000000 := by
  constructor <;> unfold taoGapMean_high_from_10M <;> norm_num

noncomputable def taoGapMean_millions_1M_10M : ℝ := 1.000358672216777
theorem taoGapMean_millions_1M_10M_near_one :
    (10003586721 : ℝ) / 10000000000 < taoGapMean_millions_1M_10M ∧
      taoGapMean_millions_1M_10M < (2500896681 : ℝ) / 2500000000 := by
  constructor <;> unfold taoGapMean_millions_1M_10M <;> norm_num

end ErdosReciprocals

/-! ### From `ErdosReciprocals/WheelSieve.lean` -/

/-!
# Wheel sieves — puente formal al mensaje Tao §1

Datos generados en `TTAOData` desde `TTAO/data/wheel_sieve_mod_*.json`.

* Residuos coprimos mod `W`: `φ(W)` clases, fracción de supervivencia `φ(W)/W`.
* Saltos **documentados** (`factorizador.cpp`): una vuelta tiene `φ(W)` saltos;
  su suma es `W/2` (recorrido de índices `u` en la rama Sundaram).
* **Gaps entre residuos** (rueda aritmética cíclica): también `φ(W)` saltos,
  pero suman `W` (periodo completo).

Los saltos C++ no coinciden con los gaps de residuos; ambas listas están verificadas.
-/

namespace ErdosReciprocals

/-!
### Mod 30 — 8 saltos (mensaje Tao)
-/

theorem tao_message_wheel30_eight_jumps :
    taoWheel30_jumpsDocumented.length = 8 :=
  taoWheel30_documented_jump_count_eq_phi

theorem tao_wheel30_survival_matches_primorial :
    (taoWheel30_phi : ℝ) / taoWheel30_modulus = (4 : ℝ) / 15 := by
  rw [taoWheel30_survival_fraction]
  norm_num

theorem tao_wheel30_documented_jumps_half_period :
    taoWheel30_jumpsDocumented.sum = taoWheel30_modulus / 2 :=
  taoWheel30_documented_jumps_sum_eq_half_modulus

theorem tao_wheel30_residue_gaps_full_period :
    taoWheel30_residueGaps.sum = taoWheel30_modulus :=
  taoWheel30_residue_gaps_sum_eq_modulus

/-!
### Mod 210 — 48 saltos (mensaje Tao)
-/

theorem tao_message_wheel210_forty_eight_jumps :
    taoWheel210_jumpsDocumented.length = 48 :=
  taoWheel210_documented_jump_count_eq_phi

theorem tao_wheel210_survival_matches_primorial :
    (taoWheel210_phi : ℝ) / taoWheel210_modulus = (8 : ℝ) / 35 := by
  rw [taoWheel210_survival_fraction]
  norm_num

theorem tao_wheel210_documented_jumps_half_period :
    taoWheel210_jumpsDocumented.sum = taoWheel210_modulus / 2 :=
  taoWheel210_documented_jumps_sum_eq_half_modulus

theorem tao_wheel210_residue_gaps_full_period :
    taoWheel210_residueGaps.sum = taoWheel210_modulus :=
  taoWheel210_residue_gaps_sum_eq_modulus

/-!
### Enlace Mertens: tasa de exclusión = ∏_{p|W}(1 - 1/p)
-/

theorem tao_wheel30_exclusion_rate_eq_euler_product :
    (taoWheel30_phi : ℝ) / taoWheel30_modulus =
      (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) := by
  rw [tao_wheel30_survival_matches_primorial, primorial_euler_product_30]

theorem tao_wheel210_exclusion_rate_eq_euler_product :
    (taoWheel210_phi : ℝ) / taoWheel210_modulus =
      (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7) := by
  rw [tao_wheel210_survival_matches_primorial, primorial_euler_product_210]

end ErdosReciprocals

/-! ### From `ErdosReciprocals/MertensTableBridge.lean` -/

/-!
# Puente criba `mertens_table` ↔ TTAO

La criba segmentada (`CONJETURA-009-ERDOS/data/mertens_table.json`) registra
`S(n)`, `Δ = S(n) - (log log n + M)` y `∏(1-1/p)` en potencias de 10 hasta `10¹¹`.

Los checkpoints TTAO (`low_from_2`) usan recuentos fijos de primos hasta `x = 104729`.
Ambas fuentes son empíricas; aquí solo enlazamos consistencia de magnitud y tendencia.
-/

namespace ErdosReciprocals

open Real

/-!
### Tendencia hacia PNT+ `Δ → 0` (empírica criba)
-/

theorem criba_empirical_delta_toward_zero :
    cribaCp100000000000_delta < cribaCp1000_delta :=
  criba_delta_tightens_1e3_to_1e11

theorem criba_empirical_delta_micro_at_1e11 :
    cribaCp100000000000_delta < (1 / 1000000 : ℝ) :=
  cribaCp100000000000_delta_lt_micro

theorem criba_empirical_S_monotone_to_1e11 :
    cribaCp1000_S < cribaCp100000000000_S :=
  cribaCp100000000000_S_gt_cribaCp1000_S

/-!
### Cruce criba `n = 10⁵` vs TTAO `x = 104729` (misma escala baja)
-/

/-- `S(10⁵)` de la criba queda por debajo de la suma TTAO hasta el primo 10 000. -/
theorem cribaCp100000_S_lt_taoCp104729_sum :
    cribaCp100000_S < taoCp104729_sumOneOverP := by
  unfold cribaCp100000_S taoCp104729_sumOneOverP
  norm_num

/-- Ambos proxies `S - log log` son positivos y del mismo orden en escala baja. -/
theorem criba_and_tao_residual_proxy_positive_at_low_scale :
    (0 : ℝ) < cribaCp100000_delta ∧
      (0 : ℝ) < taoCp104729_residualProxy := by
  constructor
  · unfold cribaCp100000_delta
    norm_num
  · exact taoCp104729_residualProxy_pos

/-- La criba en `10⁵` ya tiene `Δ` criba < 10⁻³ (TTAO llega ahí en `x = 104729`). -/
theorem cribaCp100000_delta_lt_thousandth :
    cribaCp100000_delta < (1 / 1000 : ℝ) := by
  unfold cribaCp100000_delta
  norm_num

/-!
### Nota metodológica (no teorema PNT+)

`cribaCp*_delta` usa la misma aproximación `M ≈ mertensConstantApprox` que los
proxies TTAO; no identifica `mertensResidual n` con `partialSum n` salvo PNT+.
-/

end ErdosReciprocals

end


/-!
## Source file: `MertensPNT/Connections.lean`
-/

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


/-!
## Source file: `MertensPNT/PNTFrontier.lean`
-/

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
