/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import SU3Wilson.SU3

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
