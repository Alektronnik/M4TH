/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.SetNotationForOrder

/-!
# ZetaZeroCounting live edition

Single-file live edition of the `ZetaZeroCounting` package for web
certification and study.  The mathematical content is the package source fused
in dependency order: `Xi`, `ZeroCounting`, `SafeHeights`, and `MainTerm`.
-/


/-!
## Source file: `ZetaZeroCounting/Xi.lean`
-/

/-!
# The Riemann Xi function, the entire Xi variant, and the nontrivial zeros

Two normalisations of the Riemann Xi function on top of Mathlib's completed
zeta:

* `Riemann.riemannXi s = (1/2) s (s-1) completedRiemannZeta s` — the classical
  Xi, vanishing at the corners `s = 0, 1` by construction;
* `Riemann.entireXi s = s (s-1) completedRiemannZeta₀ s + 1` — an entire
  variant built on Mathlib's `completedRiemannZeta₀`, **nonvanishing at the
  corners**, designed so that Cauchy contours around the critical box never
  cross artificial zeros.

The two agree with `s (s-1) completedRiemannZeta s` away from `s = 0, 1`
(`entireXi_eq_mul_completedRiemannZeta`), which yields the exact dictionary
between zeros of `entireXi` in the open critical strip and the nontrivial
zeros of `riemannZeta` (`entireXi_eq_zero_of_mem_nontrivialZeros`,
`mem_nontrivialZeros_of_entireXi_eq_zero`).

The symmetry `s ↦ 1 - s` of the nontrivial zeros is **proved** from Mathlib's
functional equation (`one_sub_mem_nontrivialZeros`), as is the functional
equation of `riemannXi` itself.

## Main definitions

- `Riemann.riemannXi`, `Riemann.entireXi`, `Riemann.nontrivialZeros`,
  `Riemann.entireXiZeros`.

## Main results

- `Riemann.completedRiemannZeta_zero_iff`: in the open strip, `ζ` and the
  completed zeta vanish together.
- `Riemann.one_sub_mem_nontrivialZeros`: symmetry of the nontrivial zeros.
- `Riemann.riemannXi_functional_equation`: `ξ (1 - s) = ξ (s)`.
- `Riemann.entireXi_eq_mul_completedRiemannZeta` and the two-way dictionary
  with `nontrivialZeros`.

## Implementation notes

`entireXi` is normalised with the additive constant `+1` so that
`entireXi 0 = entireXi 1 = 1 ≠ 0`; the algebraic identities with
`completedRiemannZeta` follow from Mathlib's `completedRiemannZeta_eq`.  The
glue lemmas on `completedRiemannZeta` nonvanishing at `Re = 0, 1` transport
Mathlib's zero-free region through the functional equation.

## References

- E. C. Titchmarsh, *The theory of the Riemann zeta-function*.

## Tags

Riemann zeta, Xi function, nontrivial zeros, functional equation
-/

@[expose] public section

open Complex Set

namespace Riemann

/-- The classical Riemann Xi function: the completed zeta multiplied by
`(1/2) s (s - 1)` to remove the poles at `s = 0` and `s = 1`. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 / 2) * s * (s - 1) * completedRiemannZeta s

/-- The set of nontrivial zeros of the Riemann zeta function, confined to the
open critical strip `0 < Re s < 1`. -/
def nontrivialZeros : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}

/-- In the open critical strip, `riemannZeta` and `completedRiemannZeta`
vanish together (the archimedean factor `Gammaℝ` does not vanish there). -/
lemma completedRiemannZeta_zero_iff (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    riemannZeta s = 0 ↔ completedRiemannZeta s = 0 := by
  have h_ne : s ≠ 0 := by
    intro hc
    rw [hc] at hs
    have : (0 : ℂ).re = 0 := rfl
    rw [this] at hs
    linarith
  rw [riemannZeta_def_of_ne_zero h_ne]
  have h_gamma_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs.1
  simp [div_eq_zero_iff, h_gamma_ne]

/-- **Symmetry of the nontrivial zeros** under `s ↦ 1 - s`, proved from
Mathlib's functional equation of the completed zeta. -/
theorem one_sub_mem_nontrivialZeros (s : ℂ) (hs : s ∈ nontrivialZeros) :
    (1 - s) ∈ nontrivialZeros := by
  have h_band : 0 < s.re ∧ s.re < 1 := hs.2
  have h_band2 : 0 < (1 - s).re ∧ (1 - s).re < 1 := by
    simp only [sub_re, one_re]
    constructor <;> linarith
  have h_zero : completedRiemannZeta s = 0 := by
    have h_zeta := hs.1
    rwa [completedRiemannZeta_zero_iff s h_band] at h_zeta
  have h_zero2 : completedRiemannZeta (1 - s) = 0 := by
    rwa [completedRiemannZeta_one_sub]
  have h_final : riemannZeta (1 - s) = 0 := by
    rwa [completedRiemannZeta_zero_iff (1 - s) h_band2]
  exact ⟨h_final, h_band2⟩

/-- **Functional equation of the Xi function**: `ξ (1 - s) = ξ (s)`, deduced
from the symmetry of Mathlib's completed zeta. -/
theorem riemannXi_functional_equation (s : ℂ) :
    riemannXi (1 - s) = riemannXi s := by
  have h_comp : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  unfold riemannXi
  rw [h_comp]
  ring

/-- In the open critical strip, `s` is neither `0` nor `1`. -/
lemma critical_strip_ne_zero_one (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    s ≠ 0 ∧ s ≠ 1 := by
  constructor
  · intro h
    rw [h] at hs
    have h_zero : (0 : ℂ).re = 0 := rfl
    rw [h_zero] at hs
    linarith
  · intro h
    rw [h] at hs
    have h_one : (1 : ℂ).re = 1 := rfl
    rw [h_one] at hs
    linarith

lemma xi_polynomial_factor_ne_zero_of_ne_zero_ne_one {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s * (s - 1) ≠ 0 :=
  mul_ne_zero hs0 (sub_ne_zero.mpr hs1)

/-- The polynomial factor of `ξ` does not vanish in the open critical strip. -/
lemma xi_polynomial_ne_zero (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
  rcases critical_strip_ne_zero_one s hs with ⟨hne_zero, hne_one⟩
  refine mul_ne_zero (mul_ne_zero ?_ hne_zero) (sub_ne_zero.mpr hne_one)
  norm_num

/-- The corners annihilate `ξ` through the polynomial factor. -/
lemma riemannXi_zero_at_zero : riemannXi 0 = 0 := by
  simp [riemannXi]

lemma riemannXi_zero_at_one : riemannXi 1 = 0 := by
  simp [riemannXi]

/-! ### Nonvanishing glue for the completed zeta on the vertical lines -/

lemma riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero {s : ℂ}
    (hs0 : s ≠ 0) (hγ : Gammaℝ s ≠ 0) :
    riemannZeta s = 0 ↔ completedRiemannZeta s = 0 := by
  rw [riemannZeta_def_of_ne_zero hs0]
  simp [div_eq_zero_iff, hγ]

lemma completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  intro h0
  have hzeta := riemannZeta_ne_zero_of_one_le_re hs
  rcases eq_or_ne s 0 with rfl | hs0
  · exfalso
    have : (1 : ℝ) ≤ 0 := by simpa using hs
    linarith
  · have hγ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (lt_of_lt_of_le zero_lt_one hs)
    exact hzeta ((riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero hs0 hγ).mpr h0)

lemma completedRiemannZeta_ne_zero_of_re_eq_one {s : ℂ} (hs : s.re = 1) :
    completedRiemannZeta s ≠ 0 :=
  completedRiemannZeta_ne_zero_of_one_le_re (by simp [hs])

lemma completedRiemannZeta_ne_zero_of_re_eq_zero {s : ℂ} (hs : s.re = 0) (_hs0 : s ≠ 0) :
    completedRiemannZeta s ≠ 0 := by
  rw [← completedRiemannZeta_one_sub s]
  exact completedRiemannZeta_ne_zero_of_re_eq_one (by simp [hs])

/-! ### The entire Xi variant -/

/-- The entire Riemann Xi function, built on Mathlib's pole-free
`completedRiemannZeta₀`.  Normalised with `+ 1` so that the corners `0, 1` are
**not** zeros. -/
noncomputable def entireXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

lemma continuous_entireXi : Continuous entireXi := by
  have h_cont_zeta0 : Continuous completedRiemannZeta₀ :=
    differentiable_completedZeta₀.continuous
  exact (continuous_id.mul (continuous_id.sub continuous_const)).mul h_cont_zeta0 |>.add
    continuous_const

/-- The zeros of the entire function form a closed subset of the plane. -/
lemma isClosed_entireXi_zeros : IsClosed {s : ℂ | entireXi s = 0} :=
  isClosed_eq continuous_entireXi continuous_const

lemma differentiable_entireXi : Differentiable ℂ entireXi := by
  unfold entireXi
  exact ((differentiable_id.mul (differentiable_id.sub (differentiable_const (1 : ℂ)))).mul
    differentiable_completedZeta₀).add (differentiable_const (1 : ℂ))

lemma entireXi_ne_zero_at_zero : entireXi 0 ≠ 0 := by
  simp [entireXi]

lemma entireXi_ne_zero_at_one : entireXi 1 ≠ 0 := by
  simp [entireXi]

/-- The zero set of `entireXi`. -/
def entireXiZeros : Set ℂ :=
  {z : ℂ | entireXi z = 0}

lemma mem_entireXiZeros_iff {z : ℂ} : z ∈ entireXiZeros ↔ entireXi z = 0 :=
  Iff.rfl

lemma analyticAt_entireXi (s : ℂ) : AnalyticAt ℂ entireXi s :=
  ((analyticOnNhd_univ_iff_differentiable).2 differentiable_entireXi) s (mem_univ s)

/-- Algebraic identity: away from the poles `s = 0, 1`, `entireXi` coincides
with the polynomial factor times `completedRiemannZeta` (the `+1` cancels
against the residue terms of Mathlib's `completedRiemannZeta_eq`). -/
lemma entireXi_eq_mul_completedRiemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireXi s = s * (s - 1) * completedRiemannZeta s := by
  have h_mathlib : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
    completedRiemannZeta_eq s
  have h_div1 : s * (s - 1) / s = s - 1 := by
    calc s * (s - 1) / s
      _ = (s - 1) * s / s := by ring
      _ = s - 1 := mul_div_cancel_right₀ (s - 1) hs0
  have h_div2 : s * (s - 1) / (1 - s) = -s := by
    have h_ne_one_sub : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
    calc s * (s - 1) / (1 - s)
      _ = -s * (1 - s) / (1 - s) := by ring
      _ = -s := mul_div_cancel_right₀ (-s) h_ne_one_sub
  calc
    entireXi s = s * (s - 1) * completedRiemannZeta₀ s + 1 := rfl
    _ = s * (s - 1) * completedRiemannZeta₀ s - (s - 1) + s := by ring
    _ = s * (s - 1) * completedRiemannZeta₀ s - s * (s - 1) / s - s * (s - 1) / (1 - s) := by
      rw [h_div1, h_div2]
      ring
    _ = s * (s - 1) * (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) := by ring
    _ = s * (s - 1) * completedRiemannZeta s := by rw [← h_mathlib]

/-- A nontrivial zero of zeta is a zero of `entireXi`. -/
lemma entireXi_eq_zero_of_mem_nontrivialZeros (s : ℂ) (hs : s ∈ nontrivialZeros) :
    entireXi s = 0 := by
  have h_band : 0 < s.re ∧ s.re < 1 := hs.2
  have h_ne_zero : s ≠ 0 := by
    intro h
    rw [h] at h_band
    have : (0 : ℂ).re = 0 := rfl
    rw [this] at h_band
    linarith [h_band.1]
  have h_ne_one : s ≠ 1 := by
    intro h
    rw [h] at h_band
    have : (1 : ℂ).re = 1 := rfl
    rw [this] at h_band
    linarith [h_band.2]
  have h_zeta_comp : completedRiemannZeta s = 0 :=
    (completedRiemannZeta_zero_iff s h_band).mp hs.1
  have heq := entireXi_eq_mul_completedRiemannZeta h_ne_zero h_ne_one
  rw [heq, h_zeta_comp, mul_zero]

/-- Converse dictionary: a zero of `entireXi` in the open strip is a
nontrivial zero of zeta. -/
lemma mem_nontrivialZeros_of_entireXi_eq_zero {s : ℂ} (hzero : entireXi s = 0)
    (hband : 0 < s.re ∧ s.re < 1) : s ∈ nontrivialZeros := by
  rcases critical_strip_ne_zero_one s hband with ⟨hs0, hs1⟩
  have hcomp : completedRiemannZeta s = 0 := by
    have heq := entireXi_eq_mul_completedRiemannZeta hs0 hs1
    rw [heq] at hzero
    rw [mul_eq_zero] at hzero
    cases hzero with
    | inl h => exact (xi_polynomial_factor_ne_zero_of_ne_zero_ne_one hs0 hs1 h).elim
    | inr h => exact h
  exact ⟨(completedRiemannZeta_zero_iff s hband).mpr hcomp, hband⟩

end Riemann

end

/-!
## Source file: `ZetaZeroCounting/ZeroCounting.lean`
-/

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
device for finiteness.  The counting functions are `ℝ`-valued (casts of
naturals) because their asymptotic theory lives in `ℝ`.

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


/-!
## Source file: `ZetaZeroCounting/SafeHeights.lean`
-/

/-!
# Safe heights for the critical box

A height `T` is **safe** when no nontrivial zero of zeta has imaginary part
exactly `T`: the top edge of the critical box does not pass through a zero.
Since the zeros with `0 < Im ≤ H` form a finite set, their imaginary parts are
a finite set of *forbidden heights*, and safe heights are dense above any
positive threshold: every interval `(T, T + ε]` contains one
(`exists_safe_height_in_interval`), so in particular safe heights exist above
`T` and within distance one of `T`.

This is the geometric input that makes contour arguments over the box
well-posed: at a safe height the Xi functions do not vanish on the top edge,
and — unconditionally, via Mathlib's zero-free region transported by the
functional equation — they do not vanish on the vertical edges away from the
corners either.  (Nonvanishing on the *bottom* edge requires the
nonvanishing of `ζ` on the real interval `(0,1)`, which belongs to the
Dirichlet-eta package.)

## Main definitions

- `Riemann.IsSafeHeight`, `Riemann.forbiddenHeights`.

## Main results

- `Riemann.exists_safe_height_in_interval`,
  `Riemann.exists_safe_height_above`,
  `Riemann.exists_safe_height_within_one`.
- `Riemann.zerosUpToIm_subset_criticalBoxInterior`: at a safe height, the
  counted zeros lie strictly inside the box.
- `Riemann.riemannXi_ne_zero_on_top_edge_of_safeHeight`,
  `Riemann.entireXi_ne_zero_on_top_edge_of_safeHeight`,
  `Riemann.riemannXi_ne_zero_on_right_edge`,
  `Riemann.riemannXi_ne_zero_on_left_edge`.

## Tags

Riemann zeta, safe height, critical strip, zero-free region
-/

@[expose] public section

open Complex Set

namespace Riemann

/-- Safe height: no nontrivial zero has `Im = T` (the top edge of the box does
not pass through a zero). -/
def IsSafeHeight (T : ℝ) : Prop :=
  ∀ s ∈ nontrivialZeros, s.im ≠ T

lemma isSafeHeight_iff_top_edge_no_nontrivial_zero {T : ℝ} :
    IsSafeHeight T ↔ ∀ s ∈ criticalBoxTopEdge T, s ∉ nontrivialZeros := by
  constructor
  · intro hT s hs hs_zero
    exact hT s hs_zero hs.2.2
  · intro h s hs_zero him
    have hs_top : s ∈ criticalBoxTopEdge T := by
      simp [criticalBoxTopEdge, hs_zero.2.1.le, hs_zero.2.2.le, him]
    exact h s hs_top hs_zero

/-- At a safe height, the counted zeros lie strictly in the interior of the
box. -/
theorem zerosUpToIm_subset_criticalBoxInterior {T : ℝ} (hSafe : IsSafeHeight T) :
    zerosUpToIm T ⊆ criticalBoxInterior T := by
  intro s hs
  simp only [criticalBoxInterior, zerosUpToIm, nontrivialZeros, Set.mem_setOf_eq] at hs ⊢
  rcases hs with ⟨⟨hzeta, hre₁, hre₂⟩, himpos, himle⟩
  have hz : s ∈ nontrivialZeros := ⟨hzeta, hre₁, hre₂⟩
  refine ⟨hre₁, hre₂, himpos, lt_of_le_of_ne himle (hSafe s hz)⟩

/-- `ξ` does not vanish on the top edge of a safe-height box (interior of the
strip). -/
lemma riemannXi_ne_zero_on_top_edge_of_safeHeight {T : ℝ} (_hT : 0 < T) (hSafe : IsSafeHeight T)
    {s : ℂ} (hs : s ∈ criticalBoxTopEdge T) (hs_re : 0 < s.re ∧ s.re < 1) :
    riemannXi s ≠ 0 := by
  intro hzero
  have hzeta : riemannZeta s = 0 := by
    dsimp [riemannXi] at hzero
    have hpoly : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
      xi_polynomial_ne_zero s hs_re
    have hcomp : completedRiemannZeta s = 0 := by
      rw [mul_eq_zero] at hzero
      cases hzero with
      | inl h => exact (hpoly h).elim
      | inr h => exact h
    exact (completedRiemannZeta_zero_iff s hs_re).mpr hcomp
  exact (isSafeHeight_iff_top_edge_no_nontrivial_zero.mp hSafe) s hs
    ⟨hzeta, hs_re⟩

/-- `entireXi` does not vanish on the top edge of a safe-height box (interior
of the strip, away from the corners). -/
lemma entireXi_ne_zero_on_top_edge_of_safeHeight {T : ℝ} (_hT : 0 < T) (hSafe : IsSafeHeight T)
    {s : ℂ} (hs : s ∈ criticalBoxTopEdge T) (hs_re : 0 < s.re ∧ s.re < 1)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireXi s ≠ 0 := by
  intro hzero
  have hpoly : s * (s - 1) ≠ 0 :=
    xi_polynomial_factor_ne_zero_of_ne_zero_ne_one hs0 hs1
  have hcomp : completedRiemannZeta s = 0 := by
    have heq := entireXi_eq_mul_completedRiemannZeta hs0 hs1
    rw [heq] at hzero
    rw [mul_eq_zero] at hzero
    cases hzero with
    | inl h => exact (hpoly h).elim
    | inr h => exact h
  have hzeta : riemannZeta s = 0 :=
    (completedRiemannZeta_zero_iff s hs_re).mpr hcomp
  exact (isSafeHeight_iff_top_edge_no_nontrivial_zero.mp hSafe) s hs ⟨hzeta, hs_re⟩

/-! ### Forbidden heights and density of safe heights -/

/-- The imaginary parts of the zeros with `0 < Im ≤ H`: a finite set of
forbidden heights. -/
noncomputable def forbiddenHeights (H : ℝ) : Finset ℝ :=
  (zerosUpToIm_finite H).toFinset.image (fun (s : ℂ) => s.im)

lemma mem_forbiddenHeights_iff {H t : ℝ} :
    t ∈ forbiddenHeights H ↔ ∃ s ∈ zerosUpToIm H, s.im = t := by
  simp [forbiddenHeights, Finset.mem_image, Set.Finite.mem_toFinset]

lemma nontrivialZero_im_mem_forbiddenHeights {H : ℝ} {s : ℂ}
    (hs : s ∈ nontrivialZeros) (hpos : 0 < s.im) (hle : s.im ≤ H) :
    s.im ∈ forbiddenHeights H := by
  rw [mem_forbiddenHeights_iff]
  exact ⟨s, ⟨hs, hpos, hle⟩, rfl⟩

/-- **Density of safe heights**: every interval `(T, T + ε]` contains a safe
height, because only finitely many heights are forbidden while the interval
is infinite. -/
theorem exists_safe_height_in_interval (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
    ∃ T', T < T' ∧ T' ≤ T + ε ∧ IsSafeHeight T' := by
  set F := forbiddenHeights (T + ε)
  have he : T < T + ε := by linarith
  have hInfinite : (Set.Ioo T (T + ε)).Infinite := Set.Ioo_infinite he
  have hExist : ∃ T', T' ∈ Set.Ioo T (T + ε) ∧ T' ∉ (F : Set ℝ) := by
    by_contra hall
    push Not at hall
    have hsub : Set.Ioo T (T + ε) ⊆ (F : Set ℝ) := fun x hx => hall x hx
    have hFin : (F : Set ℝ).Finite := F.finite_toSet
    exact hInfinite.not_finite (hFin.subset hsub)
  obtain ⟨T', hT', hT'not⟩ := hExist
  refine ⟨T', hT'.1, hT'.2.le, ?_⟩
  intro s hs him
  have him_in : T' ∈ forbiddenHeights (T + ε) := by
    rw [mem_forbiddenHeights_iff]
    refine ⟨s, ⟨hs, ?_, ?_⟩, him⟩
    · linarith [him, hT'.1]
    · linarith [him, hT'.2]
  exact hT'not him_in

/-- For every `T > 0` there is a safe height `T' ≥ T`. -/
theorem exists_safe_height_above (T : ℝ) (hT : 0 < T) :
    ∃ T', T ≤ T' ∧ IsSafeHeight T' := by
  obtain ⟨T', h₁, _, h₂⟩ := exists_safe_height_in_interval T 1 hT one_pos
  exact ⟨T', le_of_lt h₁, h₂⟩

/-- For every `T > 0` there is a safe height in `[T, T + 1]`.  The pinching
`T ≤ T' ≤ T + 1` is what the asymptotic layer of the counting formula needs. -/
theorem exists_safe_height_within_one (T : ℝ) (hT : 0 < T) :
    ∃ T', T ≤ T' ∧ T' ≤ T + 1 ∧ IsSafeHeight T' := by
  obtain ⟨T', hlt, hle, hSafe⟩ := exists_safe_height_in_interval T 1 hT one_pos
  exact ⟨T', le_of_lt hlt, hle, hSafe⟩

/-! ### Vertical edges: unconditional nonvanishing away from the corners

On `Re = 1` Mathlib's zero-free region applies directly; on `Re = 0` it is
transported by the functional equation.  Both edges are therefore zero-free
for `ξ` away from the corners, with no hypotheses on the height. -/

/-- Nontrivial zeros never lie on the vertical lines `Re = 0` or `Re = 1`. -/
lemma nontrivialZeros_not_on_vertical_edges {s : ℂ} (hs : s ∈ nontrivialZeros) :
    s ∉ criticalBoxLeftEdge 0 ∧ s ∉ criticalBoxRightEdge 0 := by
  constructor
  · intro h
    have : s.re = 0 := h.1
    linarith [hs.2.1, this]
  · intro h
    have : s.re = 1 := h.1
    linarith [hs.2.2, this]

theorem riemannXi_ne_zero_on_right_edge {T : ℝ} {s : ℂ}
    (hs : s ∈ criticalBoxRightEdge T) (him : s.im ≠ 0) :
    riemannXi s ≠ 0 := by
  have hs1 : s.re = 1 := hs.1
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h] at him
    simp at him
  have hs_ne_zero : s ≠ 0 := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  have hpoly : s * (s - 1) ≠ 0 :=
    xi_polynomial_factor_ne_zero_of_ne_zero_ne_one hs_ne_zero hs_ne_one
  have hcomp := completedRiemannZeta_ne_zero_of_re_eq_one hs1
  have hfactor : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
    simpa [mul_assoc] using mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) hpoly
  dsimp [riemannXi]
  exact mul_ne_zero hfactor hcomp

theorem riemannXi_ne_zero_on_left_edge {T : ℝ} {s : ℂ}
    (hs : s ∈ criticalBoxLeftEdge T) (hs0 : s ≠ 0) :
    riemannXi s ≠ 0 := by
  have hr : s.re = 0 := hs.1
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h] at hr
    simp at hr
  have hpoly : s * (s - 1) ≠ 0 :=
    xi_polynomial_factor_ne_zero_of_ne_zero_ne_one hs0 hs_ne_one
  have hcomp := completedRiemannZeta_ne_zero_of_re_eq_zero hr hs0
  have hfactor : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
    simpa [mul_assoc] using mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) hpoly
  dsimp [riemannXi]
  exact mul_ne_zero hfactor hcomp

end Riemann

end


/-!
## Source file: `ZetaZeroCounting/MainTerm.lean`
-/

/-!
# The von Mangoldt main term and its asymptotic theory

The main term of the Riemann–von Mangoldt counting formula,

  `vonMangoldtMainTerm T = (T / 2π) (log (T / 2π) - 1)`,

together with its simplified form `(T / 2π) log T`, and the complete
unconditional asymptotic theory: the two forms are asymptotically equivalent,
the main term tends to infinity, is eventually nonzero, and dominates both
`T` and `log T` (`T_isLittleO_vonMangoldtMainTerm`,
`log_isLittleO_vonMangoldtMainTerm`).

The Riemann–von Mangoldt counting theorem itself,

  `distinctZeroCount ~ vonMangoldtMainTerm`  (at `atTop`),

is stated here as the typed `Prop` `RiemannVonMangoldtCounting`.  It is **not**
an axiom of this package: its proof belongs to the argument-principle series
(the contour packages), and every consequence in this file takes it as an
explicit hypothesis (`riemannVonMangoldtCounting_simplified`).

## Main definitions

- `Riemann.vonMangoldtMainTerm`, `Riemann.vonMangoldtMainTermSimplified`.
- `Riemann.RiemannVonMangoldtCounting` (the typed counting statement).

## Main results

- `Riemann.vonMangoldt_mainTerm_simplified_equiv_classical`.
- `Riemann.vonMangoldtMainTerm_tendsto_atTop`.
- `Riemann.T_isLittleO_vonMangoldtMainTerm`,
  `Riemann.log_isLittleO_vonMangoldtMainTerm`.
- `Riemann.riemannVonMangoldtCounting_simplified` (conditional transfer).

## Implementation notes

The name `vonMangoldtMainTerm` lives inside the `Riemann` namespace and does
not collide with `ArithmeticFunction.vonMangoldt`; the final global name is a
review decision.  All lemmas in this file are unconditional; the only
statement about the actual zero count is the `Prop` definition and its
hypothesis-guarded corollary.

## Tags

Riemann-von Mangoldt, zero counting, main term, asymptotics
-/

@[expose] public section

open Complex Set Filter Topology Asymptotics

namespace Riemann

/-- Classical main term: `(T / 2π) (log (T / 2π) - 1)`. -/
noncomputable def vonMangoldtMainTerm (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1)

/-- Simplified form used in asymptotic equivalences: `(T / 2π) log T`. -/
noncomputable def vonMangoldtMainTermSimplified (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * Real.log T

lemma vonMangoldtMainTerm_sub_simplified {T : ℝ} (hT : 0 < T) :
    vonMangoldtMainTermSimplified T - vonMangoldtMainTerm T =
      (T / (2 * Real.pi)) * (Real.log (2 * Real.pi) + 1) := by
  dsimp [vonMangoldtMainTermSimplified, vonMangoldtMainTerm]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [Real.log_div hT.ne' hpi.ne']
  field_simp
  ring_nf

/-- The two forms of the main term are asymptotically equivalent. -/
theorem vonMangoldt_mainTerm_simplified_equiv_classical :
    IsEquivalent atTop vonMangoldtMainTermSimplified vonMangoldtMainTerm := by
  rw [isEquivalent_iff_tendsto_one]
  · have hpi : 0 < 2 * Real.pi := by positivity
    have h_ratio : (fun T => vonMangoldtMainTermSimplified T / vonMangoldtMainTerm T) =ᶠ[atTop]
        fun T => 1 + (Real.log (2 * Real.pi) + 1) / (Real.log (T / (2 * Real.pi)) - 1) := by
      filter_upwards [eventually_gt_atTop (2 * Real.pi * Real.exp 1)] with T hT
      have hTpos : 0 < T := lt_trans (by positivity) hT
      have hsub := vonMangoldtMainTerm_sub_simplified hTpos
      have hsum : vonMangoldtMainTermSimplified T =
          vonMangoldtMainTerm T + (T / (2 * Real.pi)) * (Real.log (2 * Real.pi) + 1) := by
        linarith
      have hden_ne : Real.log (T / (2 * Real.pi)) - 1 ≠ 0 := by
        have hpi' : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
        have hlog : 1 < Real.log (T / (2 * Real.pi)) := by
          have hgt : Real.exp 1 < T / (2 * Real.pi) := by
            rw [lt_div_iff₀ hpi, mul_comm]
            exact hT
          rw [← Real.log_exp 1]
          exact (Real.log_lt_log_iff (Real.exp_pos 1) hpi').2 hgt
        linarith
      have hmain_ne : vonMangoldtMainTerm T ≠ 0 := by
        dsimp [vonMangoldtMainTerm]
        exact mul_ne_zero (div_ne_zero hTpos.ne' hpi.ne') hden_ne
      calc
        vonMangoldtMainTermSimplified T / vonMangoldtMainTerm T
            = (vonMangoldtMainTerm T + (T / (2 * Real.pi)) * (Real.log (2 * Real.pi) + 1)) /
                vonMangoldtMainTerm T := by rw [hsum]
        _ = 1 + ((T / (2 * Real.pi)) * (Real.log (2 * Real.pi) + 1)) / vonMangoldtMainTerm T := by
          rw [add_div, div_self hmain_ne]
        _ = 1 + (Real.log (2 * Real.pi) + 1) / (Real.log (T / (2 * Real.pi)) - 1) := by
          dsimp [vonMangoldtMainTerm]
          field_simp [hmain_ne, hTpos.ne', hpi.ne', Real.log_div hTpos.ne' hpi.ne', hden_ne]
    have hden_top : Tendsto (fun T => Real.log (T / (2 * Real.pi)) - 1) atTop atTop := by
      have hlog : Tendsto (fun T => Real.log (T / (2 * Real.pi))) atTop atTop := by
        have hdiv : Tendsto (fun T => T / (2 * Real.pi)) atTop atTop := by
          rw [tendsto_atTop_atTop]
          intro b
          use max (b * (2 * Real.pi)) 0
          intro T hT
          have hT' : b * (2 * Real.pi) ≤ T := le_trans (le_max_left _ _) hT
          calc b = (b * (2 * Real.pi)) / (2 * Real.pi) := by field_simp
            _ ≤ T / (2 * Real.pi) := div_le_div_of_nonneg_right hT' (by positivity)
        exact Real.tendsto_log_atTop.comp hdiv
      rw [tendsto_atTop_atTop]
      intro b
      rcases (tendsto_atTop_atTop.mp hlog) (b + 1) with ⟨a, ha⟩
      use a
      intro T hT
      linarith [ha T hT]
    have h_err :
        Tendsto
          (fun T => (Real.log (2 * Real.pi) + 1) /
            (Real.log (T / (2 * Real.pi)) - 1))
          atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden_top
    refine Tendsto.congr' h_ratio.symm ?_
    simpa [add_zero] using Filter.Tendsto.const_add 1 h_err
  · filter_upwards [eventually_gt_atTop (2 * Real.pi * Real.exp 1)] with T hT
    dsimp [vonMangoldtMainTerm]
    have hTpos : 0 < T := lt_trans (by positivity) hT
    have hpi : 0 < 2 * Real.pi := by positivity
    refine mul_ne_zero (div_ne_zero hTpos.ne' hpi.ne') ?_
    have hlog : 1 < Real.log (T / (2 * Real.pi)) := by
      have hpi' : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
      have hgt : Real.exp 1 < T / (2 * Real.pi) := by
        rw [lt_div_iff₀ hpi]
        linarith
      rw [← Real.log_exp 1]
      exact (Real.log_lt_log_iff (Real.exp_pos 1) hpi').2 hgt
    linarith

/-! ### Unconditional asymptotics of the main term -/

lemma vonMangoldtMainTerm_eventually_ne_zero :
    ∀ᶠ T in atTop, vonMangoldtMainTerm T ≠ 0 := by
  filter_upwards [eventually_gt_atTop (Real.exp 1 * (2 * Real.pi))] with T hT
  dsimp [vonMangoldtMainTerm]
  have hTpos : 0 < T := lt_trans (by positivity) hT
  have hpi : 0 < 2 * Real.pi := by positivity
  refine mul_ne_zero (div_ne_zero hTpos.ne' hpi.ne') ?_
  have hlog : 1 < Real.log (T / (2 * Real.pi)) := by
    have hpi' : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
    have hgt : Real.exp 1 < T / (2 * Real.pi) := by
      rw [lt_div_iff₀ hpi]
      linarith
    rw [← Real.log_exp 1]
    exact (Real.log_lt_log_iff (Real.exp_pos 1) hpi').2 hgt
  linarith

lemma vonMangoldtMainTerm_log_den_tendsto_atTop :
    Tendsto (fun T => Real.log (T / (2 * Real.pi)) - 1) atTop atTop := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hdiv : Tendsto (fun T => T / (2 * Real.pi)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    use max (b * (2 * Real.pi)) 0
    intro T hT
    have hT' : b * (2 * Real.pi) ≤ T := le_trans (le_max_left _ _) hT
    calc b = (b * (2 * Real.pi)) / (2 * Real.pi) := by field_simp
      _ ≤ T / (2 * Real.pi) := div_le_div_of_nonneg_right hT' (by positivity)
  have hlog : Tendsto (fun T => Real.log (T / (2 * Real.pi))) atTop atTop :=
    Real.tendsto_log_atTop.comp hdiv
  rw [tendsto_atTop_atTop]
  intro b
  rcases (tendsto_atTop_atTop.mp hlog) (b + 1) with ⟨a, ha⟩
  use a
  intro T hT
  linarith [ha T hT]

/-- Numeric bound: `π > 3` gives `2π ≥ 1`. -/
lemma one_le_two_mul_pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]

/-- Numeric bound for the von Mangoldt threshold: `e > 2` and `π > 3`. -/
lemma one_le_exp_one_mul_two_pi : (1 : ℝ) ≤ Real.exp 1 * (2 * Real.pi) := by
  nlinarith [Real.pi_gt_three, Real.exp_one_gt_two]

lemma vonMangoldtMainTerm_tendsto_atTop : Tendsto vonMangoldtMainTerm atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  rcases (tendsto_atTop_atTop.mp vonMangoldtMainTerm_log_den_tendsto_atTop) (b + 1) with
    ⟨a, ha_den⟩
  use max (Real.exp 1 * (2 * Real.pi) * max a 0) (Real.exp 1 * (2 * Real.pi))
  intro T hT
  have hT_ge_exp : Real.exp 1 * (2 * Real.pi) ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T :=
    lt_of_lt_of_le (by positivity : 0 < Real.exp 1 * (2 * Real.pi)) hT_ge_exp
  have hT' : a ≤ T := by
    rcases lt_or_ge 0 a with ha_pos | ha_nonpos
    · have hmax : max a 0 = a := max_eq_left ha_pos.le
      have hscale : a ≤ Real.exp 1 * (2 * Real.pi) * a := by
        exact le_mul_of_one_le_left (le_of_lt ha_pos) one_le_exp_one_mul_two_pi
      have hmid : Real.exp 1 * (2 * Real.pi) * a ≤
          max (Real.exp 1 * (2 * Real.pi) * max a 0) (Real.exp 1 * (2 * Real.pi)) := by
        rw [hmax]
        exact le_max_left _ _
      exact le_trans hscale (le_trans hmid hT)
    · have hmax : max a 0 = 0 := max_eq_right ha_nonpos
      have hstep : max a 0 ≤
          max (Real.exp 1 * (2 * Real.pi) * max a 0) (Real.exp 1 * (2 * Real.pi)) := by
        rw [hmax]
        simp only [mul_zero]
        exact le_max_left (0 : ℝ) (Real.exp 1 * (2 * Real.pi))
      exact le_trans (le_max_left a 0) (le_trans hstep hT)
  have hlog : Real.log (T / (2 * Real.pi)) - 1 ≥ b + 1 := by
    simpa using ha_den T hT'
  have hpi : 0 < 2 * Real.pi := by positivity
  dsimp [vonMangoldtMainTerm]
  have hpos : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
  have hlog_nonneg : 0 ≤ Real.log (T / (2 * Real.pi)) - 1 := by
    have hle : Real.exp 1 ≤ T / (2 * Real.pi) := by rwa [le_div_iff₀ (by positivity)]
    have hlog_ge_one : 1 ≤ Real.log (T / (2 * Real.pi)) := (Real.le_log_iff_exp_le hpos).mpr hle
    linarith
  have hcoef : 1 ≤ T / (2 * Real.pi) := by
    have h2pi_le : (2 : ℝ) * Real.pi ≤ T := by
      have hle : (2 : ℝ) * Real.pi ≤ Real.exp 1 * (2 * Real.pi) := by
        nlinarith [Real.pi_pos, Real.add_one_le_exp 1]
      exact le_trans hle hT_ge_exp
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      (by simpa [one_mul] using h2pi_le)
  calc
    b ≤ b + 1 := by linarith
    _ ≤ Real.log (T / (2 * Real.pi)) - 1 := by linarith [hlog]
    _ ≤ (T / (2 * Real.pi)) *
        (Real.log (T / (2 * Real.pi)) - 1) := by
      nlinarith [hlog_nonneg, hcoef]

lemma vonMangoldtMainTerm_log_den_ne_zero {T : ℝ} (hmain : vonMangoldtMainTerm T ≠ 0) :
    Real.log (T / (2 * Real.pi)) - 1 ≠ 0 := by
  intro h
  have hz : vonMangoldtMainTerm T = 0 := by
    show (T / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1) = 0
    rw [h, mul_zero]
  exact hmain hz

/-- The identity `T` is negligible against the main term. -/
lemma T_isLittleO_vonMangoldtMainTerm :
    (fun T : ℝ => T) =o[atTop] vonMangoldtMainTerm := by
  have hgf : ∀ᶠ T in atTop, vonMangoldtMainTerm T = 0 → T = 0 :=
    vonMangoldtMainTerm_eventually_ne_zero.mono fun T hT h0 => absurd h0 hT
  refine (isLittleO_iff_tendsto' hgf).2 ?_
  have h_main_div_T : Tendsto (fun T => vonMangoldtMainTerm T / T) atTop atTop := by
    have h_eq : (fun T => vonMangoldtMainTerm T / T) =ᶠ[atTop]
        fun T => (1 / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1) := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      dsimp [vonMangoldtMainTerm]
      field_simp [hT.ne']
    have hscaled :
        Tendsto
          (fun T => (1 / (2 * Real.pi)) *
            (Real.log (T / (2 * Real.pi)) - 1))
          atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) vonMangoldtMainTerm_log_den_tendsto_atTop
    exact Tendsto.congr' h_eq.symm hscaled
  have h_congr : (fun T => T / vonMangoldtMainTerm T) =ᶠ[atTop]
      fun T => (vonMangoldtMainTerm T / T)⁻¹ := by
    filter_upwards [vonMangoldtMainTerm_eventually_ne_zero] with T hT
    field_simp [hT]
  exact Tendsto.congr' h_congr.symm (tendsto_inv_atTop_zero.comp h_main_div_T)

/-- `log` is negligible against the main term. -/
lemma log_isLittleO_vonMangoldtMainTerm :
    (fun T : ℝ => Real.log T) =o[atTop] vonMangoldtMainTerm := by
  have hgf : ∀ᶠ T in atTop, vonMangoldtMainTerm T = 0 → Real.log T = 0 :=
    vonMangoldtMainTerm_eventually_ne_zero.mono fun T hT h0 => absurd h0 hT
  refine (isLittleO_iff_tendsto' hgf).2 ?_
  have h_eq : (fun T => Real.log T / vonMangoldtMainTerm T) =ᶠ[atTop]
      fun T => (2 * Real.pi / T) * (Real.log T / (Real.log (T / (2 * Real.pi)) - 1)) := by
    filter_upwards [eventually_gt_atTop 1, vonMangoldtMainTerm_eventually_ne_zero] with T hT hmain
    have hTpos : 0 < T := lt_trans zero_lt_one hT
    have hpi : 0 < 2 * Real.pi := by positivity
    have hden_ne := vonMangoldtMainTerm_log_den_ne_zero hmain
    have hlogpos : 0 < Real.log T := Real.log_pos hT
    dsimp [vonMangoldtMainTerm]
    field_simp [hTpos.ne', hpi.ne', hden_ne, hlogpos.ne']
  have h_inv_T : Tendsto (fun T => (2 * Real.pi) / T) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (2 * Real.pi)
  have h_ratio :
      Tendsto (fun T => Real.log T / (Real.log (T / (2 * Real.pi)) - 1))
        atTop (𝓝 1) := by
    have h_factor : (fun T => Real.log T / (Real.log (T / (2 * Real.pi)) - 1)) =ᶠ[atTop]
        fun T => 1 + (Real.log (2 * Real.pi) + 1) / (Real.log (T / (2 * Real.pi)) - 1) := by
      filter_upwards [eventually_gt_atTop (2 * Real.pi * Real.exp 1)] with T hT
      have hTpos : 0 < T := lt_trans (by positivity) hT
      have hpi : 0 < 2 * Real.pi := by positivity
      have hsum : Real.log T = Real.log (T / (2 * Real.pi)) + Real.log (2 * Real.pi) := by
        have hpi' : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
        calc
          Real.log T = Real.log ((T / (2 * Real.pi)) * (2 * Real.pi)) := by
            congr 1; field_simp [hTpos.ne', hpi.ne']
          _ = Real.log (T / (2 * Real.pi)) + Real.log (2 * Real.pi) :=
              Real.log_mul hpi'.ne' hpi.ne'
      have hden_ne : Real.log (T / (2 * Real.pi)) - 1 ≠ 0 := by
        have hpi' : 0 < T / (2 * Real.pi) := div_pos hTpos hpi
        have hlog : 1 < Real.log (T / (2 * Real.pi)) := by
          have hgt : Real.exp 1 < T / (2 * Real.pi) := by
            rw [lt_div_iff₀ hpi]
            linarith
          rw [← Real.log_exp 1]
          exact (Real.log_lt_log_iff (Real.exp_pos 1) hpi').2 hgt
        linarith
      rw [hsum]
      field_simp [hden_ne]
      ring
    have h_err :
        Tendsto
          (fun T => (Real.log (2 * Real.pi) + 1) /
            (Real.log (T / (2 * Real.pi)) - 1))
          atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop vonMangoldtMainTerm_log_den_tendsto_atTop
    have h_add := Filter.Tendsto.const_add 1 h_err
    simpa [add_zero] using Tendsto.congr' h_factor.symm h_add
  simpa using Tendsto.congr' h_eq.symm (h_inv_T.mul h_ratio)

/-! ### The typed counting statement -/

/-- **The Riemann–von Mangoldt counting theorem, as a typed statement.**
Its proof belongs to the argument-principle series over the critical box; no
result in this package assumes it except as an explicit hypothesis. -/
def RiemannVonMangoldtCounting : Prop :=
  IsEquivalent atTop distinctZeroCount vonMangoldtMainTerm

/-- Conditional transfer: the counting statement in classical form yields the
simplified form `(T / 2π) log T`. -/
theorem riemannVonMangoldtCounting_simplified (h : RiemannVonMangoldtCounting) :
    IsEquivalent atTop distinctZeroCount vonMangoldtMainTermSimplified :=
  h.trans vonMangoldt_mainTerm_simplified_equiv_classical.symm

/-! ### Certificates

Concrete instances checked by the kernel.  After `lake build`, running

  `#print axioms Riemann.zerosUpToIm_finite`
  `#print axioms Riemann.T_isLittleO_vonMangoldtMainTerm`

must report only the foundational axioms `propext`, `Classical.choice`,
`Quot.sound`. -/

section Certificates

/-- Monotonicity instance of the counting function. -/
example : zeroCountingFun 1 ≤ zeroCountingFun 2 :=
  zeroCountingFun_mono (by norm_num : (1 : ℝ) ≤ 2)

/-- Nonnegativity instance. -/
example : 0 ≤ zeroCountingFun 100 :=
  zeroCountingFun_nonneg 100

/-- A safe height exists above `100`. -/
example : ∃ T', 100 ≤ T' ∧ IsSafeHeight T' :=
  exists_safe_height_above 100 (by norm_num)

end Certificates

end Riemann

end
