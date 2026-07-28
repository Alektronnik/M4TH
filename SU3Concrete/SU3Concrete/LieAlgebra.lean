/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Lie.Basic
public import SU3Concrete.GellMann

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
