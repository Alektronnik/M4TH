/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# SU3Concrete live edition

Single-file live edition of the `SU3Concrete` package for web certification and
study.  The mathematical content is the package source fused in dependency
order: `GellMann`, `LieAlgebra`, `StructureConstants`, `Commutator`, and
`Representation`.
-/


/-!
## Source file: `SU3Concrete/GellMann.lean`
-/

/-!
# Concrete Gell-Mann generators for `su(3)`

This file defines the eight Hermitian Gell-Mann matrices, the anti-Hermitian
physics generators `Tᵃ = iλₐ`, and the concrete real Lie algebra `su(3)` as
anti-Hermitian trace-zero `3 × 3` complex matrices.

## Main definitions

- `Physics.YangMills.Matrix3x3`: complex `3 × 3` matrices.
- `Physics.YangMills.gellMannHermitian`: the eight matrices `λ₁, …, λ₈`.
- `Physics.YangMills.gellMannGenerator`: the anti-Hermitian generators
  `Tᵃ = iλₐ`.
- `Physics.YangMills.LieAlgebraSU3`: anti-Hermitian trace-zero matrices.

## Main results

- `Physics.YangMills.gellMannGenerator_antiHermitian`.
- `Physics.YangMills.gellMannGenerator_trace_zero`.
- `Physics.YangMills.gellMannLieAlgebra`: every generator lies in `su(3)`.

## Implementation notes

The normalization is the anti-Hermitian physics convention `Tᵃ = iλₐ`, hence
`[Tᵃ, Tᵇ] = -2 f^{abc} Tᶜ`.

## Tags

su(3), Gell-Mann matrices, Lie algebra
-/

@[expose] public section

namespace Physics.YangMills

abbrev Matrix3x3 := Matrix (Fin 3) (Fin 3) ℂ

open Matrix Complex

/-- The diagonal Gell-Mann matrix `diag(1, 1, -2)` before `λ₈` normalization. -/
noncomputable def gellMannLambda8 : Matrix3x3 :=
  !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, -2]

theorem gellMannLambda8_trace_zero : gellMannLambda8.trace = 0 := by
  simp [gellMannLambda8, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  ring

private theorem gellMannLambda8_hermitian :
    gellMannLambda8.conjTranspose = gellMannLambda8 := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [gellMannLambda8, Matrix.conjTranspose_apply]

/-- The eight Hermitian Gell-Mann matrices `λ₁, …, λ₈` in the physics convention. -/
noncomputable def gellMannHermitian : Fin 8 → Matrix3x3
  | 0 => !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  | 1 => !![0, -I, 0; I, 0, 0; 0, 0, 0]
  | 2 => !![1, 0, 0; 0, -1, 0; 0, 0, 0]
  | 3 => !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  | 4 => !![0, 0, -I; 0, 0, 0; I, 0, 0]
  | 5 => !![0, 0, 0; 0, 0, 1; 0, 1, 0]
  | 6 => !![0, 0, 0; 0, 0, -I; 0, I, 0]
  | 7 => (Real.sqrt 3 / 3) • gellMannLambda8

/-- Anti-Hermitian `su(3)` generators `Tᵃ = i λₐ`. -/
noncomputable def gellMannGenerator (i : Fin 8) : Matrix3x3 :=
  I • gellMannHermitian i

private lemma gellMannHermitian_hermitian (i : Fin 8) :
    (gellMannHermitian i).conjTranspose = gellMannHermitian i := by
  fin_cases i
  · ext r c; fin_cases r <;> fin_cases c <;>
      simp [Matrix.conjTranspose_apply, gellMannHermitian]
  · ext r c; fin_cases r <;> fin_cases c <;>
      simp [Matrix.conjTranspose_apply, gellMannHermitian]
  · ext r c; fin_cases r <;> fin_cases c <;>
      simp [Matrix.conjTranspose_apply, gellMannHermitian]
  · ext r c; fin_cases r <;> fin_cases c <;>
      simp [Matrix.conjTranspose_apply, gellMannHermitian]
  · ext r c; fin_cases r <;> fin_cases c <;>
      simp [Matrix.conjTranspose_apply, gellMannHermitian]
  · ext r c; fin_cases r <;> fin_cases c <;>
      simp [Matrix.conjTranspose_apply, gellMannHermitian]
  · ext r c; fin_cases r <;> fin_cases c <;>
      simp [Matrix.conjTranspose_apply, gellMannHermitian]
  · simp [gellMannHermitian, conjTranspose_smul, gellMannLambda8_hermitian]

theorem gellMannHermitian_trace_zero (i : Fin 8) :
    (gellMannHermitian i).trace = 0 := by
  fin_cases i
  · simp [gellMannHermitian, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  · simp [gellMannHermitian, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  · simp [gellMannHermitian, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  · simp [gellMannHermitian, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  · simp [gellMannHermitian, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  · simp [gellMannHermitian, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  · simp [gellMannHermitian, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  · simp [gellMannHermitian, trace_smul, gellMannLambda8_trace_zero]

theorem gellMannGenerator_antiHermitian (i : Fin 8) :
    (gellMannGenerator i).conjTranspose = -(gellMannGenerator i) := by
  rw [gellMannGenerator, conjTranspose_smul, gellMannHermitian_hermitian i]
  suffices star I = -I by rw [this, neg_smul]
  simp [conj_I]

theorem gellMannGenerator_trace_zero (i : Fin 8) :
    (gellMannGenerator i).trace = 0 := by
  simp [gellMannGenerator, trace_smul, gellMannHermitian_trace_zero]

/-- The concrete Lie algebra `su(3)` as anti-Hermitian trace-zero matrices. -/
def LieAlgebraSU3 := { M : Matrix3x3 // M.conjTranspose = -M ∧ M.trace = 0 }

/-- The `i`-th Gell-Mann generator as an element of `su(3)`. -/
noncomputable def gellMannLieAlgebra (i : Fin 8) : LieAlgebraSU3 :=
  ⟨gellMannGenerator i,
    ⟨gellMannGenerator_antiHermitian i, gellMannGenerator_trace_zero i⟩⟩

/-- Backward-compatible natural-number lookup on `{0, …, 7}`. -/
noncomputable def gellMannMatrices (i : Nat) : LieAlgebraSU3 :=
  if h : i < 8 then gellMannLieAlgebra ⟨i, h⟩ else gellMannLieAlgebra 0

theorem gellMannMatrices_fin (i : Fin 8) :
    gellMannMatrices i = gellMannLieAlgebra i := by
  simp [gellMannMatrices, Fin.is_lt]

end Physics.YangMills

end


/-!
## Source file: `SU3Concrete/LieAlgebra.lean`
-/

/-!
# The concrete Lie algebra structure on `su(3)`

This file equips anti-Hermitian trace-zero `3 × 3` complex matrices with their
real vector-space structure and the matrix commutator Lie bracket.

## Main definitions

- `Physics.YangMills.lieCommutator`: the bracket `AB - BA`.
- `Physics.YangMills.lieAlgebraSU3Submodule`: `su(3)` as a real submodule.

## Main results

- `Physics.YangMills.lieCommutator_antiHermitian`.
- `Physics.YangMills.lieCommutator_trace_zero`.
- `LieRing` and `LieAlgebra ℝ` instances on `LieAlgebraSU3`.

## Tags

su(3), Lie algebra, matrix commutator
-/

@[expose] public section

namespace Physics.YangMills

open Matrix Complex

theorem lieAdd_antiHermitian (A B : LieAlgebraSU3) :
    (A.val + B.val).conjTranspose = -(A.val + B.val) := by
  rw [conjTranspose_add, A.property.1, B.property.1]
  simp [neg_add_rev, add_comm]

theorem lieAdd_trace_zero (A B : LieAlgebraSU3) :
    (A.val + B.val).trace = 0 := by
  simp [trace_add, A.property.2, B.property.2]

/-- Matrix addition, certified to stay inside `su(3)`. -/
def lieAdd (A B : LieAlgebraSU3) : LieAlgebraSU3 :=
  ⟨A.val + B.val, ⟨lieAdd_antiHermitian A B, lieAdd_trace_zero A B⟩⟩

theorem lieAdd_val (A B : LieAlgebraSU3) : (lieAdd A B).val = A.val + B.val := rfl

theorem lieCommutator_antiHermitian (A B : LieAlgebraSU3) :
    (A.val * B.val - B.val * A.val).conjTranspose =
      -(A.val * B.val - B.val * A.val) := by
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, A.property.1, B.property.1]
  ext i j
  simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply]

theorem lieCommutator_trace_zero (A B : LieAlgebraSU3) :
    (A.val * B.val - B.val * A.val).trace = 0 := by
  rw [trace_sub, trace_mul_comm, sub_self]

/-- Matrix commutator `[A, B] = AB - BA`, certified to stay inside `su(3)`. -/
noncomputable def lieCommutator (A B : LieAlgebraSU3) : LieAlgebraSU3 :=
  ⟨A.val * B.val - B.val * A.val,
    ⟨lieCommutator_antiHermitian A B, lieCommutator_trace_zero A B⟩⟩

theorem lieCommutator_val (A B : LieAlgebraSU3) :
    (lieCommutator A B).val = A.val * B.val - B.val * A.val := rfl

/-- Equality of Lie algebra elements, retained as a named replacement for the
source monolith's former equality postulate. -/
abbrev lieEq (X Y : LieAlgebraSU3) : Prop := X = Y

theorem lieEqTrans {X Y Z : LieAlgebraSU3} : lieEq X Y → lieEq Y Z → lieEq X Z :=
  Eq.trans

theorem smulGenerator_antiHermitian (r : ℝ) (i : Fin 8) :
    (r • gellMannGenerator i).conjTranspose = -(r • gellMannGenerator i) := by
  simp [conjTranspose_smul, gellMannGenerator_antiHermitian]

theorem smulGenerator_trace_zero (r : ℝ) (i : Fin 8) :
    (r • gellMannGenerator i).trace = 0 := by
  simp [trace_smul, gellMannGenerator_trace_zero]

/-- A real multiple of a Gell-Mann generator, certified in `su(3)`. -/
noncomputable def smulGellMannLie (r : ℝ) (i : Fin 8) : LieAlgebraSU3 :=
  ⟨r • gellMannGenerator i,
    ⟨smulGenerator_antiHermitian r i, smulGenerator_trace_zero r i⟩⟩

/-- The zero element of `su(3)`. -/
def zeroLieAlgebra : LieAlgebraSU3 :=
  ⟨0, by constructor <;> simp⟩

/-- `su(3)` as a real submodule of complex matrices. -/
noncomputable def lieAlgebraSU3Submodule : Submodule ℝ Matrix3x3 where
  carrier := {M | M.conjTranspose = -M ∧ M.trace = 0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro A B hA hB
    constructor
    · rw [conjTranspose_add, hA.1, hB.1]
      simp [neg_add_rev, add_comm]
    · simp [trace_add, hA.2, hB.2]
  smul_mem' := by
    intro r A hA
    constructor
    · simp [conjTranspose_smul, hA.1]
    · simp [trace_smul, hA.2]

noncomputable instance : AddCommGroup LieAlgebraSU3 := by
  unfold LieAlgebraSU3
  exact inferInstanceAs (AddCommGroup lieAlgebraSU3Submodule)

noncomputable instance : Module ℝ LieAlgebraSU3 := by
  unfold LieAlgebraSU3
  exact inferInstanceAs (Module ℝ lieAlgebraSU3Submodule)

/-- Lie bracket `[A, B] = AB - BA` on `su(3)`. -/
noncomputable instance : Bracket LieAlgebraSU3 LieAlgebraSU3 where
  bracket A B := lieCommutator A B

noncomputable instance : LieRing LieAlgebraSU3 where
  bracket := fun A B => lieCommutator A B
  add_lie A B C := by
    apply Subtype.ext
    change (A.val + B.val) * C.val - C.val * (A.val + B.val) =
      (A.val * C.val - C.val * A.val) + (B.val * C.val - C.val * B.val)
    noncomm_ring
  lie_add A B C := by
    apply Subtype.ext
    change A.val * (B.val + C.val) - (B.val + C.val) * A.val =
      (A.val * B.val - B.val * A.val) + (A.val * C.val - C.val * A.val)
    noncomm_ring
  lie_self A := by
    apply Subtype.ext
    change A.val * A.val - A.val * A.val = 0
    simp
  leibniz_lie A B C := by
    apply Subtype.ext
    change A.val * (B.val * C.val - C.val * B.val) -
        (B.val * C.val - C.val * B.val) * A.val =
      ((A.val * B.val - B.val * A.val) * C.val -
          C.val * (A.val * B.val - B.val * A.val)) +
        (B.val * (A.val * C.val - C.val * A.val) -
          (A.val * C.val - C.val * A.val) * B.val)
    noncomm_ring

noncomputable instance : LieAlgebra ℝ LieAlgebraSU3 where
  lie_smul r A B := by
    apply Subtype.ext
    change A.val * (r • B.val) - (r • B.val) * A.val =
      r • (A.val * B.val - B.val * A.val)
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]

@[simp] theorem add_val (A B : LieAlgebraSU3) : (A + B).val = A.val + B.val := rfl
@[simp] theorem zero_val : (0 : LieAlgebraSU3).val = 0 := rfl
@[simp] theorem bracket_val (A B : LieAlgebraSU3) :
    (⁅A, B⁆).val = A.val * B.val - B.val * A.val := rfl
@[simp] theorem neg_val (A : LieAlgebraSU3) : (-A).val = -A.val := rfl
@[simp] theorem sub_val (A B : LieAlgebraSU3) : (A - B).val = A.val - B.val := rfl
@[simp] theorem smul_val (r : ℝ) (A : LieAlgebraSU3) : (r • A).val = r • A.val := rfl

end Physics.YangMills

end


/-!
## Source file: `SU3Concrete/StructureConstants.lean`
-/

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


/-!
## Source file: `SU3Concrete/Commutator.lean`
-/

/-!
# The Gell-Mann commutator

This file packages the concrete matrix commutator `[Tᵃ, Tᵇ]` and its closure in
the concrete `su(3)` Lie algebra.

## Main definitions

- `Physics.YangMills.gellMannCommutatorMatrix`: the concrete matrix commutator.
- `Physics.YangMills.gellMannCommutatorLie`: the same commutator as an element of
  `LieAlgebraSU3`.
- `Physics.YangMills.gellMannCommutatorCombination`: the packaged commutator
  endpoint.

## Main results

- `Physics.YangMills.generator_commutator_matrix`.
- `Physics.YangMills.gellMann_commutator`.
- `Physics.YangMills.gellMannCommutatorMatrix_jacobi`.

## Tags

su(3), Gell-Mann matrices, commutator
-/

@[expose] public section

namespace Physics.YangMills

open Matrix Complex BigOperators

@[simp] private lemma sqrt3_sq_C : (↑(Real.sqrt 3) : ℂ) ^ 2 = 3 := by
  simp [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

@[simp] private lemma sqrt3_mul_sqrt3_C :
    (↑(Real.sqrt 3) : ℂ) * (↑(Real.sqrt 3) : ℂ) = 3 := by
  have : (↑(Real.sqrt 3) : ℂ) * (↑(Real.sqrt 3) : ℂ) =
      (↑(Real.sqrt 3) : ℂ) ^ 2 := by
    ring
  rw [this, sqrt3_sq_C]

/-- The concrete matrix commutator `[Tᵃ,Tᵇ]`. -/
noncomputable def gellMannCommutatorMatrix (a b : Fin 8) : Matrix3x3 :=
  gellMannGenerator a * gellMannGenerator b - gellMannGenerator b * gellMannGenerator a

/-- The concrete commutator definition unfolds to the matrix commutator. -/
theorem generator_commutator_matrix (a b : Fin 8) :
    gellMannGenerator a * gellMannGenerator b - gellMannGenerator b * gellMannGenerator a =
      gellMannCommutatorMatrix a b := by
  rfl

/-- The commutator table as an element of `su(3)`. -/
noncomputable def gellMannCommutatorLie (a b : Fin 8) : LieAlgebraSU3 :=
  ⟨gellMannCommutatorMatrix a b, by
    rw [← generator_commutator_matrix a b]
    constructor
    · simpa [lieCommutator_val, gellMannLieAlgebra, gellMannGenerator] using
        lieCommutator_antiHermitian (gellMannLieAlgebra a) (gellMannLieAlgebra b)
    · simpa [lieCommutator_val, gellMannLieAlgebra, gellMannGenerator] using
        lieCommutator_trace_zero (gellMannLieAlgebra a) (gellMannLieAlgebra b)⟩

theorem gellMannCommutatorLie_val (a b : Fin 8) :
    (gellMannCommutatorLie a b).val = gellMannCommutatorMatrix a b := rfl

theorem gellMann_commutator (a b : Fin 8) :
    lieCommutator (gellMannLieAlgebra a) (gellMannLieAlgebra b) =
      gellMannCommutatorLie a b := by
  apply Subtype.ext
  simp [lieCommutator_val, gellMannCommutatorLie_val, gellMannLieAlgebra,
    generator_commutator_matrix]

/-- A linear combination of Gell-Mann generators. -/
noncomputable def gellMannLieCombination (coeff : Fin 8 → ℝ) : LieAlgebraSU3 :=
  ⟨∑ i : Fin 8, coeff i • gellMannGenerator i, by
    constructor
    · simp [conjTranspose_sum, conjTranspose_smul, gellMannGenerator_antiHermitian]
    · simp [trace_sum, trace_smul, gellMannGenerator_trace_zero]⟩

/-- Packaged endpoint for the certified commutator. -/
noncomputable def gellMannCommutatorCombination (a b : Fin 8) : LieAlgebraSU3 :=
  gellMannCommutatorLie a b

/-- The certified commutator agrees with its packaged endpoint. -/
theorem gellMann_commutator_structure (a b : Fin 8) :
    gellMannCommutatorLie a b = gellMannCommutatorCombination a b := by
  rfl

theorem gellMannCommutatorMatrix_antisymm (a b : Fin 8) :
    gellMannCommutatorMatrix a b = -gellMannCommutatorMatrix b a := by
  calc
    gellMannCommutatorMatrix a b
        = gellMannGenerator a * gellMannGenerator b -
            gellMannGenerator b * gellMannGenerator a := by
      rw [← generator_commutator_matrix a b]
    _ = -(gellMannGenerator b * gellMannGenerator a -
            gellMannGenerator a * gellMannGenerator b) := by
      abel
    _ = -gellMannCommutatorMatrix b a := by
      rw [generator_commutator_matrix b a]

/-- Jacobi identity for the matrix commutator `[A, B] = AB - BA`. -/
theorem matrixCommutator_jacobi (A B C : Matrix3x3) :
    (A * B - B * A) * C - C * (A * B - B * A) +
      (B * C - C * B) * A - A * (B * C - C * B) +
      (C * A - A * C) * B - B * (C * A - A * C) = 0 := by
  noncomm_ring

/-- Jacobi identity for Gell-Mann commutator matrices. -/
theorem gellMannCommutatorMatrix_jacobi (a b c : Fin 8) :
    (gellMannCommutatorMatrix a b * gellMannGenerator c -
      gellMannGenerator c * gellMannCommutatorMatrix a b) +
      (gellMannCommutatorMatrix b c * gellMannGenerator a -
        gellMannGenerator a * gellMannCommutatorMatrix b c) +
      (gellMannCommutatorMatrix c a * gellMannGenerator b -
        gellMannGenerator b * gellMannCommutatorMatrix c a) = 0 := by
  repeat rw [← generator_commutator_matrix]
  noncomm_ring

end Physics.YangMills

end


/-!
## Source file: `SU3Concrete/Representation.lean`
-/

/-!
# Adjoint, Killing form, Cartan generators and fundamental Casimir for `su(3)`

This file contains the representation-theoretic consequences of the concrete
Gell-Mann presentation: adjoint matrices, the adjoint Casimir, the Killing form
on the basis, the Cartan pair, and the fundamental trace/Casimir identities.

## Main definitions

- `Physics.YangMills.adjointMatrix`.
- `Physics.YangMills.adjointCasimir`.
- `Physics.YangMills.killingFormBasis`.
- `Physics.YangMills.fundamentalCasimir`.

## Main results

- `Physics.YangMills.adjointCasimir_diagonal`.
- `Physics.YangMills.killingFormBasis_diagonal`.
- `Physics.YangMills.cartanGenerators_commute`.
- `Physics.YangMills.generator_trace_fundamental`.
- `Physics.YangMills.fundamentalCasimir_diagonal`.

## Tags

su(3), adjoint representation, Killing form, Cartan subalgebra, Casimir
-/

@[expose] public section

namespace Physics.YangMills

open Matrix BigOperators

/-- The adjoint representation matrix: `(ad Tᵃ)_{bc} = f^{abc}`. -/
noncomputable def adjointMatrix (a : Fin 8) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun b c => structureConstant a b c

theorem adjointMatrix_antisymm (a : Fin 8) :
    (adjointMatrix a)ᵀ = -adjointMatrix a := by
  ext b c
  simp [adjointMatrix, Matrix.transpose_apply, Matrix.neg_apply]
  rw [structureConstant_antisymm_full a c b]

theorem adjointMatrix_trace_zero (a : Fin 8) : (adjointMatrix a).trace = 0 := by
  simp [adjointMatrix, Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  have hcyc := structureConstant_cyclic a x x
  have hanti := structureConstant_antisymm x x a
  linarith

/-- Commutation relation for the adjoint representation. -/
theorem adjointMatrix_commutator (a b : Fin 8) :
    adjointMatrix a * adjointMatrix b - adjointMatrix b * adjointMatrix a =
      -(∑ e : Fin 8, structureConstant a b e • adjointMatrix e) := by
  ext c d
  simp [adjointMatrix, Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply]
  have jacobi := structureConstant_jacobi a b c d
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at jacobi
  calc
    (∑ e : Fin 8, structureConstant a c e * structureConstant b e d) -
        (∑ e : Fin 8, structureConstant b c e * structureConstant a e d)
        = ∑ e : Fin 8, (structureConstant a c e * structureConstant b e d -
            structureConstant b c e * structureConstant a e d) := by
      simp [Finset.sum_sub_distrib]
    _ = ∑ e : Fin 8, ((-structureConstant c a e) * (-structureConstant b d e) -
            structureConstant b c e * (-structureConstant a d e)) := by
      refine Finset.sum_congr rfl (fun e _ => ?_)
      have h1 : structureConstant a c e = -structureConstant c a e :=
        structureConstant_antisymm a c e
      have h2 : structureConstant b e d = -structureConstant b d e :=
        structureConstant_antisymm_full b e d
      have h3 : structureConstant a e d = -structureConstant a d e :=
        structureConstant_antisymm_full a e d
      simp [h1, h2, h3]
    _ = ∑ e : Fin 8, (structureConstant c a e * structureConstant b d e +
            structureConstant b c e * structureConstant a d e) := by
      refine Finset.sum_congr rfl (fun e _ => ?_)
      ring
    _ = (∑ e : Fin 8, structureConstant c a e * structureConstant b d e) +
        (∑ e : Fin 8, structureConstant b c e * structureConstant a d e) := by
      simp [Finset.sum_add_distrib]
    _ = -∑ e : Fin 8, structureConstant a b e * structureConstant c d e := by
      linarith
    _ = -(∑ e : Fin 8, structureConstant a b e * structureConstant c d e) := by
      simp
    _ = -(∑ e : Fin 8, structureConstant a b e * structureConstant e c d) := by
      simp [structureConstant_cyclic]

theorem adjoint_isLieHomomorphism (a b : Fin 8) :
    -(∑ e : Fin 8, structureConstant a b e • adjointMatrix e) =
      adjointMatrix a * adjointMatrix b - adjointMatrix b * adjointMatrix a :=
  (adjointMatrix_commutator a b).symm

/-- Casimir operator `C = ∑ₐ (ad Tᵃ)^2` in the adjoint representation. -/
noncomputable def adjointCasimir : Matrix (Fin 8) (Fin 8) ℝ :=
  ∑ a : Fin 8, adjointMatrix a * adjointMatrix a

/-- The adjoint quadratic Casimir is `-3 I` in the anti-Hermitian convention. -/
theorem adjointCasimir_diagonal :
    adjointCasimir = (-3) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  ext c d
  simp [adjointCasimir, Matrix.smul_apply, Matrix.one_apply]
  have hcas := structureConstant_casimir c d
  calc
    ∑ a : Fin 8, ∑ e : Fin 8, structureConstant a c e * structureConstant a e d
        = ∑ a : Fin 8, ∑ e : Fin 8,
            (-structureConstant a e c) * structureConstant a e d := by
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun e _ => ?_))
      simp [structureConstant_antisymm_full a c e]
    _ = -∑ a : Fin 8, ∑ e : Fin 8, structureConstant a e c * structureConstant a e d := by
      simp [Finset.sum_neg_distrib]
    _ = -∑ a : Fin 8, ∑ b : Fin 8, structureConstant a b c * structureConstant a b d := by
      simp
    _ = -(if c = d then (3 : ℝ) else 0) := by rw [hcas]
    _ = (if c = d then (-3 : ℝ) else 0) := by
      split <;> simp

/-- Killing form evaluated on Gell-Mann basis elements: `κ(a,b) = Tr(ad Tᵃ ad Tᵇ)`. -/
noncomputable def killingFormBasis (a b : Fin 8) : ℝ :=
  (adjointMatrix a * adjointMatrix b).trace

theorem killingFormBasis_symm (a b : Fin 8) :
    killingFormBasis a b = killingFormBasis b a := by
  unfold killingFormBasis
  rw [Matrix.trace_mul_comm (adjointMatrix a) (adjointMatrix b)]

/-- `κ(Tᵃ,Tᵇ) = -3 δᵃᵇ` in the anti-Hermitian convention. -/
theorem killingFormBasis_diagonal (a b : Fin 8) :
    killingFormBasis a b = -3 * (if a = b then (1 : ℝ) else 0) := by
  unfold killingFormBasis
  simp [adjointMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  calc
    (∑ i : Fin 8, ∑ j : Fin 8, structureConstant a i j * structureConstant b j i)
        = (∑ i : Fin 8, ∑ j : Fin 8,
            structureConstant a i j * (-structureConstant b i j)) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [structureConstant_antisymm_full b j i]
    _ = -(∑ i : Fin 8, ∑ j : Fin 8, structureConstant a i j * structureConstant b i j) := by
      simp [Finset.sum_neg_distrib, mul_neg]
    _ = -(∑ i : Fin 8, ∑ j : Fin 8, structureConstant i j a * structureConstant i j b) := by
      refine congrArg (fun x => -x) (Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ => ?_)))
      rw [structureConstant_cyclic a i j, structureConstant_cyclic b i j]
    _ = -(if a = b then (3 : ℝ) else 0) := by rw [structureConstant_casimir a b]
    _ = (if a = b then (-3 : ℝ) else 0) := by
      split <;> simp

theorem killingFormBasis_neg_definite (a : Fin 8) : killingFormBasis a a < 0 := by
  rw [killingFormBasis_diagonal a a]
  have : (if a = a then (1 : ℝ) else 0) = 1 := by simp
  rw [this]
  norm_num

theorem killingFormBasis_nondeg (a : Fin 8) : killingFormBasis a a ≠ 0 := by
  linarith [killingFormBasis_neg_definite a]

/-- Cartan generator index for `T² = iλ₃`. -/
def cartanIndex1 : Fin 8 := 2

/-- Cartan generator index for `T⁷ = iλ₈`. -/
def cartanIndex2 : Fin 8 := 7

/-- The two standard Cartan generators commute. -/
theorem cartanGenerators_commute :
    ⁅gellMannLieAlgebra cartanIndex1, gellMannLieAlgebra cartanIndex2⁆ =
      (0 : LieAlgebraSU3) := by
  unfold cartanIndex1 cartanIndex2
  show lieCommutator (gellMannLieAlgebra 2) (gellMannLieAlgebra 7) =
    (0 : LieAlgebraSU3)
  rw [gellMann_commutator 2 7]
  apply Subtype.ext
  change gellMannCommutatorMatrix 2 7 = 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMannCommutatorMatrix, gellMannGenerator, gellMannHermitian,
      gellMannLambda8, Matrix.sub_apply] <;>
    ring

theorem cartanSubalgebra_abelian :
    lieCommutator (gellMannLieAlgebra cartanIndex1)
      (gellMannLieAlgebra cartanIndex2) = 0 :=
  cartanGenerators_commute

/-- The two Cartan generator indices. -/
def cartanGeneratorSet : Finset (Fin 8) := {cartanIndex1, cartanIndex2}

theorem cartanIndices_ne : cartanIndex1 ≠ cartanIndex2 := by
  unfold cartanIndex1 cartanIndex2
  decide

set_option linter.unnecessarySeqFocus false in
/-- Fundamental trace identity: `Tr(TᵃTᵇ) = -2 δᵃᵇ`. -/
theorem generator_trace_fundamental (a b : Fin 8) :
    (gellMannGenerator a * gellMannGenerator b).trace =
      if a = b then (-2 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [gellMannGenerator, gellMannHermitian, gellMannLambda8,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;>
    simp [Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] <;>
    norm_num

theorem generator_trace_symm (a b : Fin 8) :
    (gellMannGenerator a * gellMannGenerator b).trace =
      (gellMannGenerator b * gellMannGenerator a).trace := by
  rw [Matrix.trace_mul_comm (gellMannGenerator a) (gellMannGenerator b)]

theorem generator_trace_sq (a : Fin 8) :
    (gellMannGenerator a * gellMannGenerator a).trace = (-2 : ℂ) := by
  rw [generator_trace_fundamental a a]
  simp

theorem generator_trace_offdiag (a b : Fin 8) (h : a ≠ b) :
    (gellMannGenerator a * gellMannGenerator b).trace = (0 : ℂ) := by
  rw [generator_trace_fundamental a b]
  simp [h]

/-- Quadratic Casimir in the fundamental representation: `C_F = ∑ₐ TᵃTᵃ`. -/
noncomputable def fundamentalCasimir : Matrix3x3 :=
  ∑ a : Fin 8, gellMannGenerator a * gellMannGenerator a

/-- `C_F = -(16/3)·I₃`. -/
theorem fundamentalCasimir_diagonal :
    fundamentalCasimir = (-(16/3 : ℂ)) • (1 : Matrix3x3) := by
  unfold fundamentalCasimir
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMannGenerator, gellMannHermitian, gellMannLambda8,
      Matrix.smul_apply, Matrix.add_apply, Fin.sum_univ_eight] <;>
    ring_nf <;>
    simp [Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] <;>
    norm_num

theorem fundamentalCasimir_trace : fundamentalCasimir.trace = (-16 : ℂ) := by
  rw [fundamentalCasimir_diagonal]
  simp [Matrix.trace, Matrix.diag, Matrix.smul_apply]
  ring

theorem sum_trace_sq_eq_casimir_trace :
    (∑ a : Fin 8, (gellMannGenerator a * gellMannGenerator a).trace) =
      fundamentalCasimir.trace := by
  rw [fundamentalCasimir]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply]
  exact Finset.sum_comm

end Physics.YangMills

end
