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

set_option linter.style.setOption false
set_option maxHeartbeats 800000

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
  by_cases hp : Nat.Prime i <;> simp [hp, Set.mem_setOf_eq]

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
