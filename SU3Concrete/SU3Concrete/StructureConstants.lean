/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import SU3Concrete.LieAlgebra

/-!
# Structure constants for the concrete Gell-Mann basis of `su(3)`

This file defines the real constants `f^{abc}` for the anti-Hermitian basis
`Tᵃ = iλₐ`, together with finite computational certificates for antisymmetry,
cyclic symmetry, the Jacobi identity, and the adjoint Casimir contraction.

## Main definitions

- `Physics.YangMills.structureConstant`: the explicit `su(3)` constants.
- `Physics.YangMills.commutatorStructureCoeff`: the coefficients in
  `[Tᵃ, Tᵇ] = -2 f^{abc} Tᶜ`.

## Main results

- `Physics.YangMills.structureConstant_antisymm`.
- `Physics.YangMills.structureConstant_cyclic`.
- `Physics.YangMills.structureConstant_jacobi`.
- `Physics.YangMills.structureConstant_casimir`.

## Implementation notes

The four certificates are exhaustive finite checks over `Fin 8`.  They replace
the former non-public placeholders.  If these proofs are too slow for CI, the
review path is to replace them with optimized decidable reflection, not new assumptions.

## Tags

su(3), structure constants, Gell-Mann matrices, computational certificate
-/

@[expose] public section

namespace Physics.YangMills

open BigOperators

@[simp] private lemma sqrt3_sq_R : (Real.sqrt 3) ^ 2 = 3 := by
  exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)

@[simp] private lemma sqrt3_mul_sqrt3_R : (Real.sqrt 3) * (Real.sqrt 3) = 3 := by
  rw [← sq, sqrt3_sq_R]

def structureConstantRatNum : Fin 8 → Fin 8 → Fin 8 → ℤ
  | a, b, c =>
    match (a, b, c) with
    | (0, 1, 2) => 2
    | (0, 2, 1) => -2
    | (0, 3, 6) => 1
    | (0, 4, 5) => -1
    | (0, 5, 4) => 1
    | (0, 6, 3) => -1
    | (1, 0, 2) => -2
    | (1, 2, 0) => 2
    | (1, 3, 5) => 1
    | (1, 4, 6) => 1
    | (1, 5, 3) => -1
    | (1, 6, 4) => -1
    | (2, 0, 1) => 2
    | (2, 1, 0) => -2
    | (2, 3, 4) => 1
    | (2, 4, 3) => -1
    | (2, 5, 6) => -1
    | (2, 6, 5) => 1
    | (3, 0, 6) => -1
    | (3, 1, 5) => -1
    | (3, 2, 4) => -1
    | (3, 4, 2) => 1
    | (3, 5, 1) => 1
    | (3, 6, 0) => 1
    | (4, 0, 5) => 1
    | (4, 1, 6) => -1
    | (4, 2, 3) => 1
    | (4, 3, 2) => -1
    | (4, 5, 0) => -1
    | (4, 6, 1) => 1
    | (5, 0, 4) => -1
    | (5, 1, 3) => 1
    | (5, 2, 6) => 1
    | (5, 3, 1) => -1
    | (5, 4, 0) => 1
    | (5, 6, 2) => -1
    | (6, 0, 3) => 1
    | (6, 1, 4) => 1
    | (6, 2, 5) => -1
    | (6, 3, 0) => -1
    | (6, 4, 1) => -1
    | (6, 5, 2) => 1
    | _ => 0

def structureConstantSqrtCoeffNum : Fin 8 → Fin 8 → Fin 8 → ℤ
  | a, b, c =>
    match (a, b, c) with
    | (3, 4, 7) => 1
    | (3, 7, 4) => -1
    | (4, 3, 7) => -1
    | (4, 7, 3) => 1
    | (5, 6, 7) => 1
    | (5, 7, 6) => -1
    | (6, 5, 7) => -1
    | (6, 7, 5) => 1
    | (7, 3, 4) => 1
    | (7, 4, 3) => -1
    | (7, 5, 6) => 1
    | (7, 6, 5) => -1
    | _ => 0

def structureConstantRat (a b c : Fin 8) : ℚ :=
  structureConstantRatNum a b c / 2

def structureConstantSqrtCoeff (a b c : Fin 8) : ℚ :=
  structureConstantSqrtCoeffNum a b c / 2

/-- Explicit structure constants for the anti-Hermitian basis `Tᵃ = iλₐ`. -/
noncomputable def structureConstant (a b c : Fin 8) : ℝ :=
  structureConstantRat a b c + structureConstantSqrtCoeff a b c * Real.sqrt 3

private def scProductRatNum (a b c d e f : Fin 8) : ℤ :=
  structureConstantRatNum a b c * structureConstantRatNum d e f +
    3 * structureConstantSqrtCoeffNum a b c * structureConstantSqrtCoeffNum d e f

private def scProductSqrtCoeffNum (a b c d e f : Fin 8) : ℤ :=
  structureConstantRatNum a b c * structureConstantSqrtCoeffNum d e f +
    structureConstantSqrtCoeffNum a b c * structureConstantRatNum d e f

private def scProductRat (a b c d e f : Fin 8) : ℚ :=
  scProductRatNum a b c d e f / 4

private def scProductSqrtCoeff (a b c d e f : Fin 8) : ℚ :=
  scProductSqrtCoeffNum a b c d e f / 4

@[simp] private theorem scProductRat_comm (a b c d e f : Fin 8) :
    scProductRat a b c d e f = scProductRat d e f a b c := by
  unfold scProductRat scProductRatNum
  ring_nf

@[simp] private theorem scProductSqrtCoeff_comm (a b c d e f : Fin 8) :
    scProductSqrtCoeff a b c d e f = scProductSqrtCoeff d e f a b c := by
  unfold scProductSqrtCoeff scProductSqrtCoeffNum
  ring_nf

private def jacobiRatNum (a b c d : Fin 8) : ℤ :=
  ∑ e : Fin 8, (scProductRatNum a b e c d e + scProductRatNum b c e a d e +
    scProductRatNum c a e b d e)

private def jacobiSqrtCoeffNum (a b c d : Fin 8) : ℤ :=
  ∑ e : Fin 8, (scProductSqrtCoeffNum a b e c d e + scProductSqrtCoeffNum b c e a d e +
    scProductSqrtCoeffNum c a e b d e)

private def casimirRatNum (c d : Fin 8) : ℤ :=
  ∑ a : Fin 8, ∑ b : Fin 8,
    scProductRatNum a b c a b d

private def casimirSqrtCoeffNum (c d : Fin 8) : ℤ :=
  ∑ a : Fin 8, ∑ b : Fin 8,
    scProductSqrtCoeffNum a b c a b d

private def jacobiRat (a b c d : Fin 8) : ℚ :=
  ∑ e : Fin 8, (scProductRat a b e c d e + scProductRat b c e a d e +
    scProductRat c a e b d e)

private def jacobiSqrtCoeff (a b c d : Fin 8) : ℚ :=
  ∑ e : Fin 8, (scProductSqrtCoeff a b e c d e + scProductSqrtCoeff b c e a d e +
    scProductSqrtCoeff c a e b d e)

private def casimirRat (c d : Fin 8) : ℚ :=
  ∑ a : Fin 8, ∑ b : Fin 8,
    scProductRat a b c a b d

private def casimirSqrtCoeff (c d : Fin 8) : ℚ :=
  ∑ a : Fin 8, ∑ b : Fin 8,
    scProductSqrtCoeff a b c a b d

private lemma jacobiRat_eq_num (a b c d : Fin 8) :
    jacobiRat a b c d = jacobiRatNum a b c d / 4 := by
  unfold jacobiRat jacobiRatNum scProductRat
  simp only [Int.cast_sum, Int.cast_add, div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  ring

private lemma jacobiSqrtCoeff_eq_num (a b c d : Fin 8) :
    jacobiSqrtCoeff a b c d = jacobiSqrtCoeffNum a b c d / 4 := by
  unfold jacobiSqrtCoeff jacobiSqrtCoeffNum scProductSqrtCoeff
  simp only [Int.cast_sum, Int.cast_add, div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  ring

private lemma casimirRat_eq_num (c d : Fin 8) :
    casimirRat c d = casimirRatNum c d / 4 := by
  unfold casimirRat casimirRatNum scProductRat
  simp only [Int.cast_sum, div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]

private lemma casimirSqrtCoeff_eq_num (c d : Fin 8) :
    casimirSqrtCoeff c d = casimirSqrtCoeffNum c d / 4 := by
  unfold casimirSqrtCoeff casimirSqrtCoeffNum scProductSqrtCoeff
  simp only [Int.cast_sum, div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]

private theorem jacobiRatNum_zero :
    ∀ a b c d : Fin 8, jacobiRatNum a b c d = 0 := by
  decide

private theorem jacobiSqrtCoeffNum_zero :
    ∀ a b c d : Fin 8, jacobiSqrtCoeffNum a b c d = 0 := by
  decide

private theorem casimirRatNum_eq :
    ∀ c d : Fin 8, casimirRatNum c d = if c = d then 12 else 0 := by
  decide

private theorem casimirSqrtCoeffNum_zero :
    ∀ c d : Fin 8, casimirSqrtCoeffNum c d = 0 := by
  decide

private theorem jacobiRat_zero : ∀ a b c d : Fin 8, jacobiRat a b c d = 0 := by
  intro a b c d
  rw [jacobiRat_eq_num]
  simp [jacobiRatNum_zero a b c d]

private theorem jacobiSqrtCoeff_zero :
    ∀ a b c d : Fin 8, jacobiSqrtCoeff a b c d = 0 := by
  intro a b c d
  rw [jacobiSqrtCoeff_eq_num]
  simp [jacobiSqrtCoeffNum_zero a b c d]

private theorem casimirRat_eq : ∀ c d : Fin 8, casimirRat c d = if c = d then 3 else 0 := by
  intro c d
  rw [casimirRat_eq_num]
  rw [casimirRatNum_eq c d]
  split <;> norm_num

private theorem casimirSqrtCoeff_zero : ∀ c d : Fin 8, casimirSqrtCoeff c d = 0 := by
  intro c d
  rw [casimirSqrtCoeff_eq_num]
  simp [casimirSqrtCoeffNum_zero c d]

private theorem structureConstantRatNum_antisymm :
    ∀ a b c : Fin 8, structureConstantRatNum a b c = -structureConstantRatNum b a c := by
  decide

private theorem structureConstantSqrtCoeffNum_antisymm :
    ∀ a b c : Fin 8,
      structureConstantSqrtCoeffNum a b c = -structureConstantSqrtCoeffNum b a c := by
  decide

private theorem structureConstantRatNum_cyclic :
    ∀ a b c : Fin 8, structureConstantRatNum a b c = structureConstantRatNum b c a := by
  decide

private theorem structureConstantSqrtCoeffNum_cyclic :
    ∀ a b c : Fin 8,
      structureConstantSqrtCoeffNum a b c = structureConstantSqrtCoeffNum b c a := by
  decide

private theorem structureConstantRat_antisymm :
    ∀ a b c : Fin 8, structureConstantRat a b c = -structureConstantRat b a c := by
  intro a b c
  unfold structureConstantRat
  rw [structureConstantRatNum_antisymm]
  simp only [Int.cast_neg]
  ring_nf

private theorem structureConstantSqrtCoeff_antisymm :
    ∀ a b c : Fin 8,
      structureConstantSqrtCoeff a b c = -structureConstantSqrtCoeff b a c := by
  intro a b c
  unfold structureConstantSqrtCoeff
  rw [structureConstantSqrtCoeffNum_antisymm]
  simp only [Int.cast_neg]
  ring_nf

private theorem structureConstantRat_cyclic :
    ∀ a b c : Fin 8, structureConstantRat a b c = structureConstantRat b c a := by
  intro a b c
  unfold structureConstantRat
  rw [structureConstantRatNum_cyclic]

private theorem structureConstantSqrtCoeff_cyclic :
    ∀ a b c : Fin 8,
      structureConstantSqrtCoeff a b c = structureConstantSqrtCoeff b c a := by
  intro a b c
  unfold structureConstantSqrtCoeff
  rw [structureConstantSqrtCoeffNum_cyclic]

private lemma structureConstant_mul (a b c d e f : Fin 8) :
    structureConstant a b c * structureConstant d e f =
      scProductRat a b c d e f + scProductSqrtCoeff a b c d e f * Real.sqrt 3 := by
  unfold structureConstant scProductRat scProductSqrtCoeff
  unfold structureConstantRat structureConstantSqrtCoeff scProductRatNum scProductSqrtCoeffNum
  ring_nf
  rw [sqrt3_sq_R]
  norm_num
  ring_nf

/-- Coefficient in `[Tᵃ, Tᵇ] = -2 f^{abc} Tᶜ`. -/
noncomputable def commutatorStructureCoeff (a b c : Fin 8) : ℝ :=
  -2 * structureConstant a b c

theorem structureConstant_antisymm (a b c : Fin 8) :
    structureConstant a b c = -structureConstant b a c := by
  have hRat := structureConstantRat_antisymm a b c
  have hSqrt := structureConstantSqrtCoeff_antisymm a b c
  unfold structureConstant
  rw [hRat, hSqrt]
  norm_num
  ring_nf

theorem structureConstant_cyclic (a b c : Fin 8) :
    structureConstant a b c = structureConstant b c a := by
  have hRat := structureConstantRat_cyclic a b c
  have hSqrt := structureConstantSqrtCoeff_cyclic a b c
  unfold structureConstant
  rw [hRat, hSqrt]

/-- Jacobi identity for the explicit `su(3)` structure constants. -/
theorem structureConstant_jacobi (a b c d : Fin 8) :
    (∑ e : Fin 8, (structureConstant a b e * structureConstant c d e +
      structureConstant b c e * structureConstant a d e +
      structureConstant c a e * structureConstant b d e)) = 0 := by
  have hRat := jacobiRat_zero a b c d
  have hSqrt := jacobiSqrtCoeff_zero a b c d
  calc
    (∑ e : Fin 8, (structureConstant a b e * structureConstant c d e +
      structureConstant b c e * structureConstant a d e +
      structureConstant c a e * structureConstant b d e))
        = (jacobiRat a b c d : ℝ) + jacobiSqrtCoeff a b c d * Real.sqrt 3 := by
      simp [jacobiRat, jacobiSqrtCoeff, structureConstant_mul, Finset.sum_add_distrib,
        Finset.mul_sum, add_assoc, add_left_comm, mul_add, mul_comm]
    _ = 0 := by
      norm_num [hRat, hSqrt]

/-- Quadratic Casimir contraction for the explicit `su(3)` structure constants. -/
theorem structureConstant_casimir (c d : Fin 8) :
    (∑ a : Fin 8, ∑ b : Fin 8, structureConstant a b c * structureConstant a b d) =
      if c = d then (3 : ℝ) else 0 := by
  have hRat := casimirRat_eq c d
  have hSqrt := casimirSqrtCoeff_zero c d
  calc
    (∑ a : Fin 8, ∑ b : Fin 8, structureConstant a b c * structureConstant a b d)
        = (casimirRat c d : ℝ) + casimirSqrtCoeff c d * Real.sqrt 3 := by
      simp [casimirRat, casimirSqrtCoeff, structureConstant_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_comm]
    _ = if c = d then (3 : ℝ) else 0 := by
      rw [hSqrt]
      simp
      rw [hRat]
      by_cases h : c = d <;> simp [h]

/-- Full antisymmetry `f^{abc} = -f^{acb}` derived from cyclicity and first-two
antisymmetry. -/
theorem structureConstant_antisymm_full (a b c : Fin 8) :
    structureConstant a b c = -structureConstant a c b := by
  rw [structureConstant_cyclic a b c]
  rw [structureConstant_cyclic b c a]
  rw [structureConstant_antisymm c a b]

/-- Coefficients in the canonical relation `[Tᵃ, Tᵇ] = -2 f^{abc} Tᶜ`. -/
abbrev gellMann_commutator_relation (a b c : Fin 8) :
    commutatorStructureCoeff a b c = -2 * structureConstant a b c := rfl

end Physics.YangMills

end
