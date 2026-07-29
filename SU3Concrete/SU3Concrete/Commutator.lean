/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import SU3Concrete.StructureConstants

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
    · simpa [gellMannLieAlgebra, gellMannGenerator] using
        lieCommutator_antiHermitian (gellMannLieAlgebra a) (gellMannLieAlgebra b)
    · simpa [gellMannLieAlgebra, gellMannGenerator] using
        lieCommutator_trace_zero (gellMannLieAlgebra a) (gellMannLieAlgebra b)⟩

theorem gellMannCommutatorLie_val (a b : Fin 8) :
    (gellMannCommutatorLie a b).val = gellMannCommutatorMatrix a b := rfl

theorem gellMann_commutator (a b : Fin 8) :
    lieCommutator (gellMannLieAlgebra a) (gellMannLieAlgebra b) =
      gellMannCommutatorLie a b := by
  apply Subtype.ext
  calc
    (lieCommutator (gellMannLieAlgebra a) (gellMannLieAlgebra b)).val
        = (gellMannLieAlgebra a).val * (gellMannLieAlgebra b).val -
          (gellMannLieAlgebra b).val * (gellMannLieAlgebra a).val := by
      rw [lieCommutator_val]
    _ = gellMannGenerator a * gellMannGenerator b -
        gellMannGenerator b * gellMannGenerator a := by
      simp [gellMannLieAlgebra]
    _ = gellMannCommutatorMatrix a b := by
      rw [generator_commutator_matrix]
    _ = (gellMannCommutatorLie a b).val := by
      rw [gellMannCommutatorLie_val]

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
