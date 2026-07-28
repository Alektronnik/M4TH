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
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# SU3Wilson live edition

Single-file live edition of the `SU3Wilson` package for web certification and
study.  The mathematical content is the package source fused in dependency
order: `SU3`, `Wilson`, and `Lattice4D`.
-/


/-!
## Source file: `SU3Wilson/SU3.lean`
-/

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


/-!
## Source file: `SU3Wilson/Wilson.lean`
-/

/-!
# Wilson plaquette terms on a finite lattice

This file gives a finite-lattice interface for Wilson action
positivity.  A `LatticeGaugeField V` contains explicit link and plaquette data,
including the diagonal plaquette law.  The Wilson term and action are then
ordinary definitions, and their positivity follows from the `SU(3)` trace bound.

## Main definitions

- `Physics.YangMills.Lattice`: the finite site set `Fin V`.
- `Physics.YangMills.Direction`: natural-number directions.
- `Physics.YangMills.LatticeGaugeField`: explicit link and plaquette data.
- `Physics.YangMills.latticeSum`, `wilsonTerm`, `WilsonAction`.

## Main results

- `Physics.YangMills.wilsonTerm_nonneg`.
- `Physics.YangMills.wilsonTerm_le_two`.
- `Physics.YangMills.wilsonTerm_diagonal`.
- `Physics.YangMills.WilsonAction_nonneg`.

## Tags

Wilson action, lattice gauge theory, SU(3), positivity
-/

@[expose] public section

namespace Physics.YangMills

open BigOperators

/-- A finite lattice of `V` sites. -/
def Lattice (V : Nat) : Type := Fin V

/-- Direction labels.  The finite Wilson sum below uses the four directions
`0, 1, 2, 3` via `Fin 4`, while this type keeps compatibility with the source
corpus' `Direction := Nat` convention. -/
abbrev Direction := Nat

/-- A finite lattice gauge field with explicit link and plaquette data. -/
structure LatticeGaugeField (V : Nat) where
  link : Lattice V → Direction → SU3
  plaquette : Lattice V → Direction → Direction → SU3
  plaquette_diagonal : ∀ x μ, plaquette x μ μ = oneSU3

/-- Normalized lattice sum `(1/V) * sum_x sum_mu sum_nu f x mu nu`. -/
noncomputable def latticeSum {V : Nat} (_field : LatticeGaugeField V)
    (f : Fin V → Direction → Direction → ℝ) : ℝ :=
  (1 / (V : ℝ)) * ∑ x : Fin V, ∑ μ : Fin 4, ∑ ν : Fin 4, f x μ ν

/-- `latticeSum` is nonnegative when the integrand is pointwise nonnegative. -/
theorem latticeSum_nonneg {V : Nat} (field : LatticeGaugeField V)
    (f : Fin V → Direction → Direction → ℝ) (hf : ∀ x μ ν, 0 ≤ f x μ ν) :
    0 ≤ latticeSum field f := by
  unfold latticeSum
  refine mul_nonneg ?_ ?_
  · exact div_nonneg zero_le_one (Nat.cast_nonneg V)
  · refine Finset.sum_nonneg fun x _ => ?_
    refine Finset.sum_nonneg fun μ _ => ?_
    refine Finset.sum_nonneg fun ν _ => hf x μ ν

/-- `latticeSum` is additive in the integrand. -/
theorem latticeSum_add {V : Nat} (field : LatticeGaugeField V)
    (f g : Fin V → Direction → Direction → ℝ) :
    latticeSum field (f + g) = latticeSum field f + latticeSum field g := by
  unfold latticeSum
  simp [Finset.sum_add_distrib, mul_add, Pi.add_apply]

/-- `latticeSum` commutes with scalar multiplication. -/
theorem latticeSum_smul {V : Nat} (field : LatticeGaugeField V) (c : ℝ)
    (f : Fin V → Direction → Direction → ℝ) :
    latticeSum field (c • f) = c * latticeSum field f := by
  unfold latticeSum
  simp [Pi.smul_apply, Finset.mul_sum, mul_assoc, mul_comm]

/-- The Wilson term for a single plaquette interaction. -/
noncomputable def wilsonTerm {V : Nat} (field : LatticeGaugeField V)
    (x : Fin V) (μ ν : Direction) : ℝ :=
  1 - (matrixTraceSU3 (field.plaquette x μ ν)).re / 3

/-- Each Wilson plaquette term is nonnegative. -/
theorem wilsonTerm_nonneg {V : Nat} (field : LatticeGaugeField V)
    (x : Fin V) (μ ν : Direction) : 0 ≤ wilsonTerm field x μ ν := by
  unfold wilsonTerm
  rcases su3_trace_re_bound (field.plaquette x μ ν) with ⟨_, h⟩
  linarith

/-- Each Wilson plaquette term is at most `2`. -/
theorem wilsonTerm_le_two {V : Nat} (field : LatticeGaugeField V)
    (x : Fin V) (μ ν : Direction) : wilsonTerm field x μ ν ≤ 2 := by
  unfold wilsonTerm
  rcases su3_trace_re_bound (field.plaquette x μ ν) with ⟨h, _⟩
  linarith

/-- The Wilson term for a diagonal plaquette vanishes. -/
@[simp] theorem wilsonTerm_diagonal {V : Nat} (field : LatticeGaugeField V)
    (x : Fin V) (μ : Direction) : wilsonTerm field x μ μ = 0 := by
  unfold wilsonTerm
  rw [field.plaquette_diagonal x μ, matrixTraceSU3_one]
  simp

/-- The total Euclidean Wilson action on the finite lattice. -/
noncomputable def WilsonAction {V : Nat} (β : ℝ) (field : LatticeGaugeField V) : ℝ :=
  β * latticeSum field (wilsonTerm field)

/-- `WilsonAction` is nonnegative when the coupling `β` is nonnegative. -/
theorem WilsonAction_nonneg {V : Nat} (β : ℝ) (field : LatticeGaugeField V)
    (hβ : 0 ≤ β) : 0 ≤ WilsonAction β field := by
  unfold WilsonAction
  refine mul_nonneg hβ ?_
  apply latticeSum_nonneg field (wilsonTerm field)
  intro x μ ν
  exact wilsonTerm_nonneg field x μ ν

/-- `WilsonAction` is homogeneous in `β`. -/
theorem WilsonAction_mul {V : Nat} (c β : ℝ) (field : LatticeGaugeField V) :
    WilsonAction (c * β) field = c * WilsonAction β field := by
  unfold WilsonAction
  ring

/-- `WilsonAction` is additive in `β`. -/
theorem WilsonAction_add {V : Nat} (β₁ β₂ : ℝ) (field : LatticeGaugeField V) :
    WilsonAction (β₁ + β₂) field = WilsonAction β₁ field + WilsonAction β₂ field := by
  unfold WilsonAction
  ring

@[simp] theorem WilsonAction_zero {V : Nat} (field : LatticeGaugeField V) :
    WilsonAction 0 field = 0 := by
  unfold WilsonAction
  simp

@[simp] theorem WilsonAction_one {V : Nat} (field : LatticeGaugeField V) :
    WilsonAction 1 field = latticeSum field (wilsonTerm field) := by
  unfold WilsonAction
  simp

theorem WilsonAction_nonneg_of_pos {V : Nat} (β : ℝ) (field : LatticeGaugeField V)
    (hβ : 0 < β) : 0 ≤ WilsonAction β field :=
  WilsonAction_nonneg β field (le_of_lt hβ)

theorem WilsonAction_congr {V : Nat} (β : ℝ) (field : LatticeGaugeField V) :
    WilsonAction β field = β * latticeSum field (wilsonTerm field) := rfl

end Physics.YangMills

end


/-!
## Source file: `SU3Wilson/Lattice4D.lean`
-/

/-!
# Constructive four-dimensional SU(3) lattice Wilson action

This file constructs plaquettes directly from four-dimensional SU(3) link
variables.  It proves the diagonal plaquette law, the Wilson term bounds, and
nonnegativity of the four-dimensional Wilson action.

## Main definitions

- `Physics.YangMills.Lattice4D`: a finite Euclidean four-dimensional lattice.
- `Physics.YangMills.Dir4`: the four coordinate directions.
- `Physics.YangMills.LinkVars4D`: SU(3)-valued link variables.
- `Physics.YangMills.plaquette4D`, `wilsonTerm4D`, `WilsonAction4D`.

## Main results

- `Physics.YangMills.plaquette4D_diagonal`.
- `Physics.YangMills.plaquette4D_trace_re_symm`.
- `Physics.YangMills.wilsonTerm4D_nonneg`.
- `Physics.YangMills.WilsonAction4D_nonneg`.

## Tags

Wilson action, lattice gauge theory, SU(3), four-dimensional lattice
-/

@[expose] public section

namespace Physics.YangMills

open Matrix Complex BigOperators

/-- Euclidean 4D lattice with temporal and three spatial extents. -/
abbrev Lattice4D (Lt Lx Ly Lz : ℕ) := Fin Lt × Fin Lx × Fin Ly × Fin Lz

/-- The four positive coordinate directions. -/
abbrev Dir4 := Fin 4

def dirT : Dir4 := 0
def dirX : Dir4 := 1
def dirY : Dir4 := 2
def dirZ : Dir4 := 3

/-- Cyclic successor in `Fin n`. -/
def wrapSucc {n : ℕ} (i : Fin n) : Fin n :=
  if hn : n = 0 then
    i
  else
    let npos : 0 < n := Nat.pos_of_ne_zero hn
    ⟨(i.val + 1) % n, Nat.mod_lt _ npos⟩

/-- Reversal of a `Fin n` index. -/
def finRev {n : ℕ} (i : Fin n) : Fin n :=
  if hn : n = 0 then
    i
  else
    let m := n - 1
    ⟨m - i.val, by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have h_lt : i.val < n := i.is_lt
      have hm_lt_n : m < n := by omega
      have hsub : m - i.val ≤ m := Nat.sub_le _ _
      exact lt_of_le_of_lt hsub hm_lt_n⟩

/-- Time reflection reverses the temporal coordinate and preserves space. -/
def timeReflection4D {Lt Lx Ly Lz : ℕ}
    (site : Lattice4D Lt Lx Ly Lz) : Lattice4D Lt Lx Ly Lz :=
  (finRev site.1, site.2.1, site.2.2.1, site.2.2.2)

/-- Shift by one in direction `mu`, with periodic boundary conditions. -/
def shift4D {Lt Lx Ly Lz : ℕ} (site : Lattice4D Lt Lx Ly Lz)
    (μ : Dir4) : Lattice4D Lt Lx Ly Lz :=
  match μ with
  | 0 => (wrapSucc site.1, site.2.1, site.2.2.1, site.2.2.2)
  | 1 => (site.1, wrapSucc site.2.1, site.2.2.1, site.2.2.2)
  | 2 => (site.1, site.2.1, wrapSucc site.2.2.1, site.2.2.2)
  | 3 => (site.1, site.2.1, site.2.2.1, wrapSucc site.2.2.2)

/-- Four-dimensional link configurations assign an `SU3` element to each directed link. -/
def LinkVars4D (Lt Lx Ly Lz : ℕ) : Type :=
  Lattice4D Lt Lx Ly Lz → Dir4 → SU3

variable {Lt Lx Ly Lz : ℕ}

/-- Plaquette at `site` in the `(mu, nu)` plane as an ordered four-link product. -/
noncomputable def plaquette4D (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) : SU3 :=
  U site μ *
    U (shift4D site μ) ν *
    (U (shift4D site ν) μ)⁻¹ *
    (U site ν)⁻¹

/-- The diagonal plaquette is the identity. -/
theorem plaquette4D_diagonal (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ : Dir4) :
    plaquette4D U site μ μ = 1 := by
  unfold plaquette4D
  have h : U (shift4D site μ) μ * (U (shift4D site μ) μ)⁻¹ = 1 := by
    simp
  calc
    U site μ * U (shift4D site μ) μ * (U (shift4D site μ) μ)⁻¹ * (U site μ)⁻¹
        = U site μ * (U (shift4D site μ) μ * (U (shift4D site μ) μ)⁻¹) *
            (U site μ)⁻¹ := by
      simp [mul_assoc]
    _ = U site μ * 1 * (U site μ)⁻¹ := by rw [h]
    _ = U site μ * (U site μ)⁻¹ := by simp
    _ = 1 := by simp

/-- The real trace of a plaquette is invariant under swapping its directions. -/
theorem plaquette4D_trace_re_symm (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) :
    (matrixTraceSU3 (plaquette4D U site μ ν)).re =
      (matrixTraceSU3 (plaquette4D U site ν μ)).re := by
  unfold plaquette4D
  have h_inv :
      (U site μ * U (shift4D site μ) ν * (U (shift4D site ν) μ)⁻¹ *
          (U site ν)⁻¹)⁻¹ =
        U site ν * U (shift4D site ν) μ * (U (shift4D site μ) ν)⁻¹ *
          (U site μ)⁻¹ := by
    simp [mul_assoc]
  have h_re_trace_inv (A : SU3) :
      (matrixTraceSU3 (A⁻¹ : SU3)).re = (matrixTraceSU3 A).re := by
    have h_val : (A⁻¹ : SU3).val = A.val.conjTranspose := rfl
    rw [matrixTraceSU3, h_val]
    have h_tr : (A.val.conjTranspose).trace = star (A.val.trace) := by
      calc
        (A.val.conjTranspose).trace = ∑ i : Fin 3, (A.val.conjTranspose) i i := by
          simp [Matrix.trace, Matrix.diag]
        _ = ∑ i : Fin 3, star (A.val i i) := by
          simp [Matrix.conjTranspose_apply]
        _ = star (∑ i : Fin 3, A.val i i) := by simp
        _ = star (A.val.trace) := by simp [Matrix.trace, Matrix.diag]
    rw [h_tr, matrixTraceSU3]
    simp
  rw [← h_inv]
  rw [h_re_trace_inv]

/-- Normalized sum over all 4D sites and direction pairs. -/
noncomputable def latticeSum4D
    (f : Lattice4D Lt Lx Ly Lz → Dir4 → Dir4 → ℝ) : ℝ :=
  let V := Lt * Lx * Ly * Lz
  (1 / (V : ℝ)) * ∑ site : Lattice4D Lt Lx Ly Lz,
    ∑ μ : Dir4, ∑ ν : Dir4, f site μ ν

/-- `latticeSum4D` is nonnegative for pointwise nonnegative inputs. -/
theorem latticeSum4D_nonneg (f : Lattice4D Lt Lx Ly Lz → Dir4 → Dir4 → ℝ)
    (hf : ∀ site μ ν, 0 ≤ f site μ ν) : 0 ≤ latticeSum4D f := by
  unfold latticeSum4D
  refine mul_nonneg ?_ ?_
  · refine div_nonneg zero_le_one (Nat.cast_nonneg _)
  · refine Finset.sum_nonneg (fun site _ => ?_)
    refine Finset.sum_nonneg (fun μ _ => ?_)
    refine Finset.sum_nonneg (fun ν _ => hf site μ ν)

/-- Wilson term for a constructive 4D plaquette. -/
noncomputable def wilsonTerm4D (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) : ℝ :=
  1 - (matrixTraceSU3 (plaquette4D U site μ ν)).re / 3

/-- Each 4D Wilson term is nonnegative. -/
theorem wilsonTerm4D_nonneg (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) :
    0 ≤ wilsonTerm4D U site μ ν := by
  unfold wilsonTerm4D
  rcases su3_trace_re_bound (plaquette4D U site μ ν) with ⟨_, h⟩
  linarith

/-- Each 4D Wilson term is at most `2`. -/
theorem wilsonTerm4D_le_two (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) :
    wilsonTerm4D U site μ ν ≤ 2 := by
  unfold wilsonTerm4D
  rcases su3_trace_re_bound (plaquette4D U site μ ν) with ⟨h, _⟩
  linarith

/-- Diagonal 4D Wilson terms vanish. -/
theorem wilsonTerm4D_diagonal (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ : Dir4) :
    wilsonTerm4D U site μ μ = 0 := by
  unfold wilsonTerm4D
  rw [plaquette4D_diagonal U site μ]
  have h : matrixTraceSU3 (1 : SU3) = (3 : ℂ) := by
    simpa [oneSU3] using matrixTraceSU3_one
  rw [h]
  simp

/-- Constructive four-dimensional Wilson action. -/
noncomputable def WilsonAction4D (β : ℝ) (U : LinkVars4D Lt Lx Ly Lz) : ℝ :=
  β * latticeSum4D (wilsonTerm4D U)

/-- `WilsonAction4D` is nonnegative for `β >= 0`. -/
theorem WilsonAction4D_nonneg (β : ℝ) (U : LinkVars4D Lt Lx Ly Lz)
    (hβ : 0 ≤ β) : 0 ≤ WilsonAction4D β U := by
  unfold WilsonAction4D
  refine mul_nonneg hβ ?_
  apply latticeSum4D_nonneg (wilsonTerm4D U)
  intro site μ ν
  exact wilsonTerm4D_nonneg U site μ ν

/-- Time reflection on link configurations. Temporal links invert orientation;
spatial links are preserved after reflecting the site. -/
noncomputable def timeReflection4D_on_links
    (U : LinkVars4D Lt Lx Ly Lz) : LinkVars4D Lt Lx Ly Lz :=
  fun site μ =>
    let siteReversed := timeReflection4D site
    match μ with
    | 0 => (U siteReversed 0)⁻¹
    | _ => U siteReversed μ

end Physics.YangMills

end
