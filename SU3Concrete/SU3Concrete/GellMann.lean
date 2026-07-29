/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.BigOperators.Fin

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
