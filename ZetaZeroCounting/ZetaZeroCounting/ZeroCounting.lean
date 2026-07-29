/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Tactic
public import Mathlib.Topology.DiscreteSubset
public import ZetaZeroCounting.Xi

/-!
# The zero-counting function N(T) of the Riemann zeta function

The zero-counting function of the Riemann–von Mangoldt theory, in two forms:

* `Riemann.distinctZeroCount T`: the cardinality of the set of nontrivial
  zeros with `0 < Im s ≤ T` (no multiplicity);
* `Riemann.zeroCountingFun T` — the canonical `N (T)` — the sum of the
  **analytic multiplicities** of those zeros, measured on `entireXi` through
  Mathlib's `analyticOrderNatAt`.  This is the quantity computed by the
  argument principle.

Finiteness of the counting domain is deduced from Mathlib's `ZetaZeros`
(compact sets meet the zeros of zeta in a finite set); discreteness of the
zeros of `entireXi` follows from the isolated-zeros principle for analytic
functions, anchored at `entireXi 0 ≠ 0`.  Every zero in the strip has
multiplicity at least one, whence `distinctZeroCount ≤ zeroCountingFun`, with
equality precisely under the classical simplicity hypothesis
(`AllEntireXiZerosSimple`).

## Main definitions

- `Riemann.criticalBox`, `Riemann.zerosUpToIm`, `Riemann.zerosUpToImFinset`.
- `Riemann.entireXiZeroMultiplicity`, `Riemann.zeroCountingFun`,
  `Riemann.distinctZeroCount`.
- `Riemann.AllEntireXiZerosSimple`.

## Main results

- `Riemann.zerosUpToIm_finite`: the counting domain is finite.
- `Riemann.isDiscrete_entireXiZeros`, `Riemann.entireXi_analyticOrderAt_ne_top`,
  `Riemann.analyticOrderNatAt_entireXi_ge_one`.
- `Riemann.distinctZeroCount_le_zeroCountingFun` and
  `Riemann.zeroCountingFun_eq_distinctZeroCount_of_all_simple`.
- Monotonicity and nonnegativity of both counting functions.

## Implementation notes

The critical box `[0,1] × [0,T]` is introduced here as the compact bounding
device for finiteness; the sibling contour package uses the same family and
the duplication is resolved at Mathlib-PR time (single shared PR).  The
counting functions are `ℝ`-valued (casts of naturals) because their asymptotic
theory (`ZetaZeroCounting.MainTerm`) lives in `ℝ`.

## Tags

Riemann zeta, zero counting, N(T), multiplicity, Riemann-von Mangoldt
-/

@[expose] public section

open Complex Set Topology

namespace Riemann

/-! ### The critical box -/

/-- The closed bounded box in the critical strip. -/
def criticalBox (T : ℝ) : Set ℂ :=
  {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}

/-- Top edge: `Im = T`, `0 ≤ Re ≤ 1`. -/
def criticalBoxTopEdge (T : ℝ) : Set ℂ :=
  {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im = T}

/-- Bottom edge: `Im = 0`, `0 ≤ Re ≤ 1`. -/
def criticalBoxBottomEdge : Set ℂ :=
  {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im = 0}

/-- Left edge: `Re = 0`, `0 ≤ Im ≤ T`. -/
def criticalBoxLeftEdge (T : ℝ) : Set ℂ :=
  {s : ℂ | s.re = 0 ∧ 0 ≤ s.im ∧ s.im ≤ T}

/-- Right edge: `Re = 1`, `0 ≤ Im ≤ T`. -/
def criticalBoxRightEdge (T : ℝ) : Set ℂ :=
  {s : ℂ | s.re = 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}

/-- Open interior of `criticalBox T` (strict in `Re` and `Im`). -/
def criticalBoxInterior (T : ℝ) : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im < T}

lemma mem_criticalBoxInterior_iff {T s} :
    s ∈ criticalBoxInterior T ↔
      0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im < T :=
  Iff.rfl

lemma criticalBoxInterior_subset_criticalBox {T : ℝ} :
    criticalBoxInterior T ⊆ criticalBox T := by
  intro s hs
  simp only [criticalBox, criticalBoxInterior, Set.mem_setOf_eq] at hs ⊢
  exact ⟨hs.1.le, hs.2.1.le, hs.2.2.1.le, hs.2.2.2.le⟩

lemma criticalBox_eq_Icc_reProdIm (T : ℝ) :
    criticalBox T = Set.Icc (0 : ℝ) (1 : ℝ) ×ℂ Set.Icc (0 : ℝ) T := by
  ext s
  simp only [criticalBox, mem_reProdIm, Set.mem_Icc, Set.mem_setOf_eq, and_assoc]

/-- The critical box is compact: continuous image of a product of two real
compact intervals. -/
lemma isCompact_criticalBox (T : ℝ) : IsCompact (criticalBox T) := by
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * I
  have h_cont : Continuous f :=
    (continuous_ofReal.comp continuous_fst).add
      ((continuous_ofReal.comp continuous_snd).mul continuous_const)
  have h_comp : IsCompact (Set.Icc (0 : ℝ) (1 : ℝ) ×ˢ Set.Icc (0 : ℝ) T) :=
    isCompact_Icc.prod isCompact_Icc
  have h_eq : f '' (Set.Icc (0 : ℝ) (1 : ℝ) ×ˢ Set.Icc (0 : ℝ) T) = criticalBox T := by
    ext s
    simp only [criticalBox, Set.mem_image, Set.mem_prod, Set.mem_Icc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨x, y⟩, ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩, rfl⟩
      simp only [f, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_zero,
        add_zero, mul_zero, add_im, mul_one, mul_im, zero_add]
      exact ⟨hx0, hx1, hy0, hy1⟩
    · intro hs
      refine ⟨(s.re, s.im), ⟨⟨hs.1, hs.2.1⟩, ⟨hs.2.2.1, hs.2.2.2⟩⟩, ?_⟩
      apply Complex.ext <;>
        simp only [f, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_zero,
          add_zero, mul_zero, add_im, mul_one, mul_im, zero_add]
  rw [← h_eq]
  exact IsCompact.image h_comp h_cont

lemma isClosed_criticalBox (T : ℝ) : IsClosed (criticalBox T) :=
  (isCompact_criticalBox T).isClosed

/-! ### The counting domain and its finiteness -/

/-- Bridge to Mathlib: nontrivial zeros are zeros of `riemannZeta`. -/
lemma nontrivialZeros_subset_riemannZetaZeros : nontrivialZeros ⊆ riemannZetaZeros := by
  intro s hs
  simpa [riemannZetaZeros, mem_riemannZetaZeros] using hs.1

/-- Nontrivial zeros with `0 < Im s ≤ T` (the von Mangoldt counting domain). -/
def zerosUpToIm (T : ℝ) : Set ℂ :=
  {s ∈ nontrivialZeros | 0 < s.im ∧ s.im ≤ T}

lemma zerosUpToIm_subset_nontrivialZeros (T : ℝ) :
    zerosUpToIm T ⊆ nontrivialZeros := by
  intro s hs
  exact hs.1

lemma zerosUpToIm_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    zerosUpToIm T₁ ⊆ zerosUpToIm T₂ := by
  intro s hs
  exact ⟨hs.1, hs.2.1, le_trans hs.2.2 h⟩

lemma mem_zerosUpToIm_of_entireXi_zero {T : ℝ} {s : ℂ} (hzero : entireXi s = 0)
    (hband : 0 < s.re ∧ s.re < 1) (him : 0 < s.im) (himle : s.im ≤ T) :
    s ∈ zerosUpToIm T :=
  ⟨mem_nontrivialZeros_of_entireXi_eq_zero hzero hband, him, himle⟩

/-- **Finiteness of the counting domain** (Mathlib `ZetaZeros`): the zeros
with `0 < Im ≤ T` form a finite set, as a subset of the intersection of a
compact box with the zeros of zeta. -/
theorem zerosUpToIm_finite (T : ℝ) : (zerosUpToIm T).Finite := by
  have h_subset : zerosUpToIm T ⊆ criticalBox T ∩ riemannZetaZeros := by
    intro s hs
    constructor
    · simp only [criticalBox, zerosUpToIm, Set.mem_setOf_eq] at hs ⊢
      have h_band := hs.1.2
      exact ⟨by linarith [h_band.1], by linarith [h_band.2], by linarith [hs.2.1], hs.2.2⟩
    · exact nontrivialZeros_subset_riemannZetaZeros hs.1
  exact (IsCompact.inter_riemannZetaZeros_finite (isCompact_criticalBox T)).subset h_subset

/-- The counting domain as a `Finset`. -/
noncomputable def zerosUpToImFinset (T : ℝ) : Finset ℂ :=
  (zerosUpToIm_finite T).toFinset

lemma zerosUpToImFinset_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    zerosUpToImFinset T₁ ⊆ zerosUpToImFinset T₂ := by
  intro s hs
  simp only [zerosUpToImFinset, Set.Finite.mem_toFinset] at hs ⊢
  exact zerosUpToIm_mono h hs

/-! ### Discreteness and multiplicities of the zeros of `entireXi` -/

/-- The zeros of `entireXi` form a discrete set (isolated-zeros principle). -/
lemma isDiscrete_entireXiZeros : IsDiscrete entireXiZeros := by
  have h_analytic : AnalyticOnNhd ℂ entireXi Set.univ :=
    (analyticOnNhd_univ_iff_differentiable).2 differentiable_entireXi
  have h_codisc : (entireXi ⁻¹' {0})ᶜ ∈ Filter.codiscrete ℂ :=
    h_analytic.preimage_zero_mem_codiscrete (x := 0) entireXi_ne_zero_at_zero
  simpa [entireXiZeros, Set.preimage, Set.mem_setOf_eq] using (mem_codiscrete'.mp h_codisc).2

/-- `entireXi` is not eventually constant at a zero: eventual constancy would
force `entireXi ≡ 0`, contradicting `entireXi 0 ≠ 0`. -/
lemma not_eventuallyConst_entireXi_at_zero {s : ℂ} (hs : entireXi s = 0) :
    ¬ Filter.EventuallyConst entireXi (𝓝 s) := by
  intro h
  have htop : analyticOrderAt entireXi s = ⊤ := by
    have htop := (eventuallyConst_iff_analyticOrderAt_sub_eq_top (f := entireXi) (z₀ := s)).mp h
    simpa [hs, sub_zero] using htop
  have hentire : entireXi = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s (hf := analyticAt_entireXi)).mp htop
  exact entireXi_ne_zero_at_zero (congr_fun hentire 0)

/-- Finite multiplicity at every zero of `entireXi`. -/
lemma entireXi_analyticOrderAt_ne_top {s : ℂ} (hs : entireXi s = 0) :
    analyticOrderAt entireXi s ≠ ⊤ := by
  intro htop
  exact not_eventuallyConst_entireXi_at_zero hs
    ((eventuallyConst_iff_analyticOrderAt_sub_eq_top (f := entireXi) (z₀ := s)).mpr
      (by simpa [hs, sub_zero] using htop))

/-- At a zero of `entireXi`, the algebraic multiplicity is at least one. -/
lemma analyticOrderNatAt_entireXi_ge_one {s : ℂ} (hs : entireXi s = 0) :
    1 ≤ analyticOrderNatAt entireXi s := by
  have htop := entireXi_analyticOrderAt_ne_top hs
  have hne : analyticOrderNatAt entireXi s ≠ 0 := by
    intro h0
    have hA := analyticAt_entireXi s
    have hord := hA.analyticOrderAt_ne_zero.mpr hs
    rw [← Nat.cast_analyticOrderNatAt htop, h0, ENat.coe_zero] at hord
    simp at hord
  omega

/-- The zeros of `entireXi` inside the critical box are isolated. -/
theorem discreteTopology_criticalBox_inter_entireXiZeros (T : ℝ) :
    DiscreteTopology (Set.inter (criticalBox T) {s : ℂ | entireXi s = 0}) :=
  (IsDiscrete.mono isDiscrete_entireXiZeros Set.inter_subset_right).to_subtype

/-! ### The two counting functions -/

/-- Algebraic multiplicity of a zero of `entireXi`. -/
noncomputable def entireXiZeroMultiplicity (s : ℂ) : ℕ :=
  analyticOrderNatAt entireXi s

/-- **The zero-counting function** `N (T)`: the sum of the multiplicities of
the nontrivial zeros with `0 < Im ≤ T`.  This is the quantity computed by the
argument principle. -/
noncomputable def zeroCountingFun (T : ℝ) : ℝ :=
  Nat.cast ((zerosUpToImFinset T).sum entireXiZeroMultiplicity)

lemma zeroCountingFun_eq_finset_sum (T : ℝ) :
    zeroCountingFun T = Nat.cast ((zerosUpToImFinset T).sum entireXiZeroMultiplicity) := rfl

/-- Classical cardinal count (no multiplicity). -/
noncomputable def distinctZeroCount (T : ℝ) : ℝ :=
  (Set.ncard (zerosUpToIm T) : ℝ)

lemma distinctZeroCount_eq_ncard (T : ℝ) :
    distinctZeroCount T = (Set.ncard (zerosUpToIm T) : ℝ) := rfl

lemma distinctZeroCount_nonneg (T : ℝ) : 0 ≤ distinctZeroCount T := by
  dsimp [distinctZeroCount]
  exact Nat.cast_nonneg _

lemma zeroCountingFun_nonneg (T : ℝ) : 0 ≤ zeroCountingFun T := by
  dsimp [zeroCountingFun]
  exact Nat.cast_nonneg _

lemma zeroCountingFun_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    zeroCountingFun T₁ ≤ zeroCountingFun T₂ := by
  dsimp [zeroCountingFun]
  exact Nat.cast_le.mpr (Finset.sum_le_sum_of_subset_of_nonneg (zerosUpToImFinset_mono h)
    fun _ _ _ => Nat.zero_le _)

lemma distinctZeroCount_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    distinctZeroCount T₁ ≤ distinctZeroCount T₂ := by
  dsimp [distinctZeroCount]
  exact mod_cast Set.ncard_le_ncard (zerosUpToIm_mono h) (zerosUpToIm_finite T₂)

lemma nontrivialZero_entireXiZeroMultiplicity_ge_one {s : ℂ} (hs : s ∈ nontrivialZeros) :
    1 ≤ entireXiZeroMultiplicity s := by
  dsimp [entireXiZeroMultiplicity]
  exact analyticOrderNatAt_entireXi_ge_one (entireXi_eq_zero_of_mem_nontrivialZeros s hs)

lemma mem_zerosUpToIm_entireXiZeroMultiplicity_ge_one {T : ℝ} {s : ℂ}
    (hs : s ∈ zerosUpToIm T) :
    1 ≤ entireXiZeroMultiplicity s :=
  nontrivialZero_entireXiZeroMultiplicity_ge_one hs.1

/-- Every counted zero has multiplicity at least one, hence the cardinal count
is dominated by the multiplicity count. -/
theorem distinctZeroCount_le_zeroCountingFun (T : ℝ) :
    distinctZeroCount T ≤ zeroCountingFun T := by
  dsimp only [zeroCountingFun, distinctZeroCount, entireXiZeroMultiplicity, zerosUpToImFinset]
  rw [Set.ncard_eq_toFinset_card _ (zerosUpToIm_finite T)]
  refine Nat.cast_le.mpr ?_
  rw [Finset.card_eq_sum_ones (zerosUpToIm_finite T).toFinset]
  exact Finset.sum_le_sum fun s hs => by
    have hs' : s ∈ zerosUpToIm T := (Set.Finite.mem_toFinset _).1 hs
    exact mem_zerosUpToIm_entireXiZeroMultiplicity_ge_one hs'

/-- Classical simplicity hypothesis: every nontrivial zero is simple. -/
def AllEntireXiZerosSimple : Prop :=
  ∀ s ∈ nontrivialZeros, entireXiZeroMultiplicity s = 1

/-- Under the simplicity hypothesis, the two counting functions agree. -/
theorem zeroCountingFun_eq_distinctZeroCount_of_all_simple
    (h : AllEntireXiZerosSimple) (T : ℝ) :
    zeroCountingFun T = distinctZeroCount T := by
  set F := (zerosUpToIm_finite T).toFinset
  have hsum : F.sum entireXiZeroMultiplicity = F.card := by
    rw [Finset.card_eq_sum_ones F]
    refine Finset.sum_congr rfl ?_
    intro s hs
    have hs' : s ∈ zerosUpToIm T := (Set.Finite.mem_toFinset _).1 hs
    simpa using h s hs'.1
  dsimp only [zeroCountingFun, distinctZeroCount, entireXiZeroMultiplicity, zerosUpToImFinset]
  rw [Set.ncard_eq_toFinset_card _ (zerosUpToIm_finite T), ← hsum]

end Riemann

end
