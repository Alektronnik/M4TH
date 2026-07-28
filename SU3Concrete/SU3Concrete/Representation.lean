/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import SU3Concrete.Commutator

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
