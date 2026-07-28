/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import XiLogResidue.LocalResidue

/-!
# Divisor dictionary for `entireXi`

This file relates the meromorphic divisor of the entire Xi variant on the
critical box to the analytic multiplicity used by the zero-counting finset.
-/

@[expose] public section

open Complex Topology Filter Set

namespace RiemannLogResidue

/-- Boundary nonvanishing condition used by the divisor support dictionary. -/
def entireXi_ne_zero_on_box_boundary (T : ℝ) : Prop :=
  ∀ s ∈ criticalBoxBoundary T, entireXi s ≠ 0

lemma entireXi_meromorphicOn_criticalBox (T : ℝ) :
    MeromorphicOn entireXi (criticalBox T) :=
  fun s _ => (analyticAt_entireXi s).meromorphicAt

lemma entireXiLogDeriv_meromorphicOn_criticalBox (T : ℝ) :
    MeromorphicOn entireXiLogDeriv (criticalBox T) := by
  unfold entireXiLogDeriv
  exact (entireXi_meromorphicOn_criticalBox T).logDeriv

/-- The support of the divisor on a compact critical box is finite. -/
lemma divisor_support_criticalBox_finite (T : ℝ) :
    (MeromorphicOn.divisor entireXi (criticalBox T)).support.Finite :=
  (MeromorphicOn.divisor entireXi (criticalBox T)).finiteSupport (isCompact_criticalBox T)

lemma entireXi_meromorphicOrder_ne_top_on_criticalBox (T : ℝ) (p : ℂ)
    (_hp : p ∈ criticalBox T) :
    meromorphicOrderAt entireXi p ≠ ⊤ := by
  rw [(analyticAt_entireXi p).meromorphicOrderAt_eq]
  cases hO : analyticOrderAt entireXi p with
  | top =>
    exfalso
    have hs0 : entireXi p = 0 :=
      congr_fun
        ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero p (hf := analyticAt_entireXi)).mp hO) p
    exact entireXi_analyticOrderAt_ne_top hs0 hO
  | coe n =>
    simp [ENat.map_coe]

lemma mem_divisor_support_entireXi_zero {T : ℝ} {s : ℂ} (hs : s ∈ criticalBox T)
    (hmem : s ∈ (MeromorphicOn.divisor entireXi (criticalBox T)).support) :
    entireXi s = 0 := by
  rw [Function.mem_support, MeromorphicOn.divisor_apply (entireXi_meromorphicOn_criticalBox T) hs]
    at hmem
  have hA := analyticAt_entireXi s
  by_contra hne
  have h0 : analyticOrderAt entireXi s = 0 := (hA.analyticOrderAt_eq_zero).mpr hne
  have hzero : (meromorphicOrderAt entireXi s).untop₀ = 0 := by
    simp [hA.meromorphicOrderAt_eq, h0, ENat.map_zero, WithTop.untop₀_zero]
  exact absurd hzero hmem

/-- The divisor of `entireXi` on the critical box equals analytic multiplicity at a zero. -/
lemma entireXi_divisor_eq_multiplicity {T : ℝ} {s : ℂ} (hs : s ∈ criticalBox T)
    (hzero : entireXi s = 0) :
    (MeromorphicOn.divisor entireXi (criticalBox T) s : ℂ) =
      (entireXiZeroMultiplicity s : ℂ) := by
  rw [MeromorphicOn.divisor_apply (entireXi_meromorphicOn_criticalBox T) hs,
    (analyticAt_entireXi s).meromorphicOrderAt_eq, entireXiZeroMultiplicity]
  have htop := entireXi_analyticOrderAt_ne_top hzero
  rw [← Nat.cast_analyticOrderNatAt htop, ENat.map_coe, WithTop.untop₀_coe, Int.cast_natCast]

lemma mem_divisor_finset_zerosUpToIm {T : ℝ} (_hSafe : IsSafeHeight T)
    (hne : entireXi_ne_zero_on_box_boundary T) {p : ℂ}
    (hp : p ∈ (divisor_support_criticalBox_finite T).toFinset) :
    p ∈ zerosUpToImFinset T := by
  have hp_support : p ∈ (MeromorphicOn.divisor entireXi (criticalBox T)).support := by
    simpa [divisor_support_criticalBox_finite, Function.mem_support, MeromorphicOn.divisor] using hp
  have hpR : p ∈ criticalBox T :=
    (MeromorphicOn.divisor entireXi (criticalBox T)).supportWithinDomain hp_support
  have hzero := mem_divisor_support_entireXi_zero hpR hp_support
  rcases hpR with ⟨hre0, hre1, him0, himle⟩
  have hband : 0 < p.re ∧ p.re < 1 := by
    constructor
    · by_contra h
      push Not at h
      have hre_eq : p.re = 0 := le_antisymm h hre0
      have hleft : p ∈ criticalBoxLeftEdge T := by
        simp [criticalBoxLeftEdge, hre_eq, him0, himle]
      exact hne p (mem_criticalBoxBoundary_iff.mpr (Or.inr (Or.inr (Or.inl hleft)))) hzero
    · by_contra h
      push Not at h
      have hre_eq : p.re = 1 := le_antisymm hre1 h
      have hright : p ∈ criticalBoxRightEdge T := by
        simp [criticalBoxRightEdge, hre_eq, him0, himle]
      exact hne p (mem_criticalBoxBoundary_iff.mpr (Or.inr (Or.inr (Or.inr hright)))) hzero
  have himpos : 0 < p.im := by
    by_contra h
    push Not at h
    have him_eq : p.im = 0 := le_antisymm h him0
    have hbot : p ∈ criticalBoxBottomEdge := by
      simp [criticalBoxBottomEdge, him_eq, hre0, hre1]
    exact hne p (mem_criticalBoxBoundary_iff.mpr (Or.inr (Or.inl hbot))) hzero
  simpa [zerosUpToImFinset, zerosUpToIm, nontrivialZeros, Set.mem_setOf_eq,
    Set.Finite.mem_toFinset] using
    mem_zerosUpToIm_of_entireXi_zero hzero hband himpos himle

lemma mem_zerosUpToIm_finset_divisor_support {T : ℝ} (hSafe : IsSafeHeight T)
    {p : ℂ} (hp : p ∈ zerosUpToImFinset T) :
    p ∈ (divisor_support_criticalBox_finite T).toFinset := by
  simp only [zerosUpToImFinset, Set.Finite.mem_toFinset, zerosUpToIm, nontrivialZeros,
    Set.mem_setOf_eq] at hp
  have hzero := nontrivial_zero_implies_entireXi_zero p hp.1
  have hpbox : p ∈ criticalBoxInterior T := zerosUpToIm_subset_criticalBoxInterior hSafe hp
  have hpR : p ∈ criticalBox T := criticalBoxInterior_subset_criticalBox hpbox
  have hpdiv : p ∈ (MeromorphicOn.divisor entireXi (criticalBox T)).support := by
    rw [Function.mem_support, MeromorphicOn.divisor_apply (entireXi_meromorphicOn_criticalBox T) hpR]
    have hA := analyticAt_entireXi p
    rw [hA.meromorphicOrderAt_eq]
    have hord : analyticOrderAt entireXi p ≠ 0 := (hA.analyticOrderAt_ne_zero).mpr hzero
    cases hO : analyticOrderAt entireXi p with
    | top => exact absurd hO (entireXi_analyticOrderAt_ne_top hzero)
    | coe n =>
      have hn : n ≠ 0 := by
        intro hn0
        exact hord (by rw [hO, hn0, ENat.coe_zero])
      simp [ENat.map_coe]
      exact Nat.cast_ne_zero.mpr hn
  simpa [divisor_support_criticalBox_finite, Set.Finite.mem_toFinset, Function.mem_support,
    MeromorphicOn.divisor] using hpdiv

/-- The finite support of the divisor in the critical box is the zero finset. -/
lemma entireXi_divisor_finset_eq_zerosUpToImFinset (T : ℝ) (hSafe : IsSafeHeight T)
    (hne : entireXi_ne_zero_on_box_boundary T) :
    (divisor_support_criticalBox_finite T).toFinset = zerosUpToImFinset T :=
  Finset.ext fun _ => ⟨
    fun hp => mem_divisor_finset_zerosUpToIm hSafe hne hp,
    fun hp => mem_zerosUpToIm_finset_divisor_support hSafe hp⟩

end RiemannLogResidue
