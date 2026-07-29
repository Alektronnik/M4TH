/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# The concrete group `SU(3)` and its trace bound

This file defines `SU(3)` as the subtype of `3 x 3` complex matrices satisfying
`U U^* = 1` and `det U = 1`, equips it with a group structure, and proves the
algebraic trace bound used by Wilson plaquette positivity:

`-1 <= Re(Tr U) / 3 <= 1`.

## Main definitions

- `Physics.YangMills.WilsonMatrix3x3`: complex `3 x 3` matrices.
- `Physics.YangMills.SU3`: special unitary matrices in dimension 3.
- `Physics.YangMills.matrixTraceSU3`: trace of an `SU3` element.

## Main results

- `Physics.YangMills.instGroupSU3`: group structure on `SU3`.
- `Physics.YangMills.matrixTraceSU3_one`.
- `Physics.YangMills.su3_trace_re_bound`.

## Implementation notes

The trace bound avoids the spectral theorem.  It uses only the row norm
identities from `U U^* = 1` and elementary real inequalities on matrix entries.

## Tags

SU(3), unitary matrix, trace bound, Wilson action
-/

@[expose] public section

namespace Physics.YangMills

abbrev WilsonMatrix3x3 := Matrix (Fin 3) (Fin 3) ℂ

open Matrix Complex

/-- The special unitary group `SU(3)` as a matrix subtype. -/
def SU3 := { M : WilsonMatrix3x3 // M * M.conjTranspose = 1 ∧ M.det = 1 }

namespace SU3

lemma unitary_condition (U : SU3) : U.val * U.val.conjTranspose = 1 := U.2.1

lemma det_condition (U : SU3) : U.val.det = 1 := U.2.2

/-- For square matrices over a field, `M * M^* = 1` implies `M^* * M = 1`. -/
lemma conjTranspose_mul_self (U : SU3) : U.val.conjTranspose * U.val = 1 :=
  (mul_eq_one_comm.mp U.unitary_condition)

/-- The product of two `SU3` matrices is again in `SU3`. -/
lemma mul_mem (U V : SU3) :
    U.1 * V.1 * (U.1 * V.1).conjTranspose = 1 ∧ (U.1 * V.1).det = 1 := by
  constructor
  · calc
      U.1 * V.1 * (U.1 * V.1).conjTranspose
          = U.1 * V.1 * (V.1.conjTranspose * U.1.conjTranspose) := by
        simp [Matrix.conjTranspose_mul]
      _ = U.1 * (V.1 * V.1.conjTranspose) * U.1.conjTranspose := by
        simp [Matrix.mul_assoc]
      _ = U.1 * 1 * U.1.conjTranspose := by rw [V.unitary_condition]
      _ = U.1 * U.1.conjTranspose := by simp
      _ = 1 := U.unitary_condition
  · simp [Matrix.det_mul, U.det_condition, V.det_condition]

/-- The identity matrix belongs to `SU3`. -/
lemma one_mem : (1 : WilsonMatrix3x3) * (1 : WilsonMatrix3x3).conjTranspose = 1 ∧
    (1 : WilsonMatrix3x3).det = 1 := by
  simp

/-- The conjugate transpose of an `SU3` matrix belongs to `SU3`. -/
lemma inv_mem (U : SU3) :
    U.val.conjTranspose * U.val.conjTranspose.conjTranspose = 1 ∧
      U.val.conjTranspose.det = 1 := by
  constructor
  · simp [Matrix.conjTranspose_conjTranspose, U.conjTranspose_mul_self]
  · rw [Matrix.det_conjTranspose, U.det_condition]
    simp

end SU3

noncomputable instance instGroupSU3 : Group SU3 where
  mul U V := ⟨U.1 * V.1, SU3.mul_mem U V⟩
  mul_assoc U V W := Subtype.ext (Matrix.mul_assoc _ _ _)
  one := ⟨1, SU3.one_mem⟩
  one_mul U := Subtype.ext (Matrix.one_mul _)
  mul_one U := Subtype.ext (Matrix.mul_one _)
  inv U := ⟨U.1.conjTranspose, SU3.inv_mem U⟩
  inv_mul_cancel U := Subtype.ext (SU3.conjTranspose_mul_self U)

/-- Trace of an `SU3` matrix. -/
noncomputable def matrixTraceSU3 (A : SU3) : ℂ :=
  A.val.trace

/-- Identity element of `SU3`. -/
noncomputable def oneSU3 : SU3 := 1

@[simp] theorem oneSU3_val : oneSU3.val = (1 : WilsonMatrix3x3) := rfl

@[simp] theorem matrixTraceSU3_one : matrixTraceSU3 oneSU3 = (3 : ℂ) := by
  rw [matrixTraceSU3, oneSU3_val]
  simp [Matrix.trace, Matrix.diag]

/-- For any `U` in `SU(3)`, `Re(Tr U) / 3` lies in `[-1, 1]`. -/
theorem su3_trace_re_bound (U : SU3) :
    -1 ≤ (matrixTraceSU3 U).re / 3 ∧ (matrixTraceSU3 U).re / 3 ≤ 1 := by
  unfold matrixTraceSU3
  rcases U.property with ⟨h_unit, _h_det⟩
  set M := U.val
  have h_row_norm_sq (i : Fin 3) :
      Complex.normSq (M i 0) + Complex.normSq (M i 1) + Complex.normSq (M i 2) = 1 := by
    have h := congrArg (fun N : WilsonMatrix3x3 => N i i) h_unit
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three] at h
    apply_fun Complex.re at h
    simpa [Complex.add_re, Complex.mul_conj, Complex.ofReal_re, Complex.one_re] using h
  have h_entry_re_abs_le_one (i j : Fin 3) : |(M i j).re| ≤ 1 := by
    have h_nonneg0 : 0 ≤ Complex.normSq (M i 0) := Complex.normSq_nonneg _
    have h_nonneg1 : 0 ≤ Complex.normSq (M i 1) := Complex.normSq_nonneg _
    have h_nonneg2 : 0 ≤ Complex.normSq (M i 2) := Complex.normSq_nonneg _
    have h_sum := h_row_norm_sq i
    have h_norm_sq_le : Complex.normSq (M i j) ≤ 1 := by
      have h_le_sum : Complex.normSq (M i j) ≤
          Complex.normSq (M i 0) + Complex.normSq (M i 1) + Complex.normSq (M i 2) := by
        fin_cases j
        · have h_nonneg_sum : 0 ≤ Complex.normSq (M i 1) + Complex.normSq (M i 2) :=
            add_nonneg h_nonneg1 h_nonneg2
          calc
            Complex.normSq (M i 0) ≤
                Complex.normSq (M i 0) + (Complex.normSq (M i 1) + Complex.normSq (M i 2)) :=
              le_add_of_nonneg_right h_nonneg_sum
            _ = Complex.normSq (M i 0) + Complex.normSq (M i 1) + Complex.normSq (M i 2) := by
              ring
        · have h_nonneg_sum : 0 ≤ Complex.normSq (M i 0) + Complex.normSq (M i 2) :=
            add_nonneg h_nonneg0 h_nonneg2
          calc
            Complex.normSq (M i 1) ≤
                Complex.normSq (M i 1) + (Complex.normSq (M i 0) + Complex.normSq (M i 2)) :=
              le_add_of_nonneg_right h_nonneg_sum
            _ = Complex.normSq (M i 0) + Complex.normSq (M i 1) + Complex.normSq (M i 2) := by
              ring
        · have h_nonneg_sum : 0 ≤ Complex.normSq (M i 0) + Complex.normSq (M i 1) :=
            add_nonneg h_nonneg0 h_nonneg1
          calc
            Complex.normSq (M i 2) ≤
                Complex.normSq (M i 2) + (Complex.normSq (M i 0) + Complex.normSq (M i 1)) :=
              le_add_of_nonneg_right h_nonneg_sum
            _ = Complex.normSq (M i 0) + Complex.normSq (M i 1) + Complex.normSq (M i 2) := by
              ring
      rw [h_sum] at h_le_sum
      exact h_le_sum
    have h_norm_sq_eq :
        Complex.normSq (M i j) = ((M i j).re) ^ 2 + ((M i j).im) ^ 2 := by
      rw [Complex.normSq_apply]
      ring
    have h_re_sq_le_one : ((M i j).re) ^ 2 ≤ 1 := by
      have h_im_sq_nonneg : 0 ≤ ((M i j).im) ^ 2 := pow_two_nonneg _
      have : ((M i j).re) ^ 2 ≤ Complex.normSq (M i j) := by
        rw [h_norm_sq_eq]
        nlinarith
      nlinarith
    have h_re_le_one : (M i j).re ≤ 1 := by nlinarith
    have h_re_ge_neg_one : -1 ≤ (M i j).re := by nlinarith
    exact abs_le.mpr ⟨h_re_ge_neg_one, h_re_le_one⟩
  have h_re_trace_bound : |(M.trace).re| ≤ 3 := by
    have h_trace_re : (M.trace).re = (M 0 0).re + (M 1 1).re + (M 2 2).re := by
      simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three]
    rw [h_trace_re]
    have h_le_one (i j : Fin 3) : (M i j).re ≤ 1 := by
      exact (abs_le.mp (h_entry_re_abs_le_one i j)).2
    have h_ge_neg_one (i j : Fin 3) : -1 ≤ (M i j).re := by
      exact (abs_le.mp (h_entry_re_abs_le_one i j)).1
    have h_sum_le_three : (M 0 0).re + (M 1 1).re + (M 2 2).re ≤ 3 := by
      linarith [h_le_one 0 0, h_le_one 1 1, h_le_one 2 2]
    have h_sum_ge_neg_three : -3 ≤ (M 0 0).re + (M 1 1).re + (M 2 2).re := by
      linarith [h_ge_neg_one 0 0, h_ge_neg_one 1 1, h_ge_neg_one 2 2]
    exact abs_le.mpr ⟨h_sum_ge_neg_three, h_sum_le_three⟩
  have h_bound : -(3 : ℝ) ≤ (M.trace).re ∧ (M.trace).re ≤ (3 : ℝ) :=
    abs_le.mp h_re_trace_bound
  constructor <;> linarith

end Physics.YangMills

end
