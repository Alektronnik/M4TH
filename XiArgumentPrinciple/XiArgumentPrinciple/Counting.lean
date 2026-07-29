/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import XiArgumentPrinciple.Contour

/-!
# Argument-principle counting chain

This file packages the critical-box argument-principle chain without adding any
trusted constants.  The genuinely external analytic ingredient is represented
by explicit hypotheses in `ArgumentPrincipleBridge`.
-/

@[expose] public section

open Complex Topology Filter

namespace RiemannArgumentPrinciple

/-- Cauchy kernel centered at `w`. -/
noncomputable def contourCauchyKernel (w : ℂ) (z : ℂ) : ℂ :=
  1 / (z - w)

/-- Cauchy-index integral over the critical-box boundary. -/
noncomputable def contourCauchyIndexIntegral (w : ℂ) (T : ℝ) : ℂ :=
  criticalBoxRectangleIntegral (contourCauchyKernel w) T

/-- The index of the contour around `w` equals `k`. -/
def ContourWindingIndexEq (T : ℝ) (w : ℂ) (k : ℤ) : Prop :=
  contourCauchyIndexIntegral w T = (k : ℂ) * (2 * Real.pi * I)

/-- The full winding-index statement for a safe critical box. -/
def ContourWindingIndexOne (T : ℝ) : Prop :=
  0 < T ∧
    IsSafeHeight T ∧
      (∀ {w : ℂ}, w ∈ criticalBoxInterior T → ContourWindingIndexEq T w 1) ∧
        (∀ {w : ℂ}, w ∉ criticalBox T → ContourWindingIndexEq T w 0)

/-- Local residue sum over the finite zero set in the critical box. -/
noncomputable def entireXiCriticalBoxResidueSum (T : ℝ) : ℂ :=
  Nat.cast ((zerosUpToImFinset T).sum entireXiZeroMultiplicity)

/-- External analytic bridge for the rectangular argument principle.

In the monolithic research file these statements are supplied by the rectangular
residue theorem infrastructure.  In this package they are explicit
hypotheses, not axioms.
-/
structure ArgumentPrincipleBridge (T : ℝ) : Prop where
  index_one :
    ∀ {w : ℂ}, w ∈ criticalBoxInterior T →
      contourCauchyIndexIntegral w T = 2 * Real.pi * I
  index_zero :
    ∀ {w : ℂ}, w ∉ criticalBox T →
      contourCauchyIndexIntegral w T = 0
  residue_sum :
    entireXiContourIntegral T / (2 * Real.pi * I) = entireXiCriticalBoxResidueSum T

theorem contour_winding_index_one_of_safe {T : ℝ} (hT : 0 < T)
    (hSafe : IsSafeHeight T) (hBridge : ArgumentPrincipleBridge T) :
    ContourWindingIndexOne T := by
  refine ⟨hT, hSafe, ?_, ?_⟩
  · intro w hw
    dsimp [ContourWindingIndexEq]
    simpa [one_mul] using hBridge.index_one hw
  · intro w hw
    dsimp [ContourWindingIndexEq]
    simpa using hBridge.index_zero hw

theorem contour_winding_index_eq_one_iff (T : ℝ) (w : ℂ) :
    ContourWindingIndexEq T w 1 ↔
      contourCauchyIndexIntegral w T = 2 * Real.pi * I := by
  simp [ContourWindingIndexEq, one_mul]

theorem contour_winding_index_eq_zero_iff (T : ℝ) (w : ℂ) :
    ContourWindingIndexEq T w 0 ↔ contourCauchyIndexIntegral w T = 0 := by
  simp [ContourWindingIndexEq, zero_mul]

/-- Every zero counted by `zerosUpToIm T` has winding index `+1`. -/
theorem contour_winding_index_one_on_zerosUpToIm {T : ℝ}
    (hSafe : IsSafeHeight T) (hBridge : ArgumentPrincipleBridge T) :
    ∀ {s : ℂ}, s ∈ zerosUpToIm T → ContourWindingIndexEq T s 1 := by
  intro s hs
  dsimp [ContourWindingIndexEq]
  simpa [one_mul] using hBridge.index_one (zerosUpToIm_subset_criticalBoxInterior hSafe hs)

/-- Residue sum equals multiplicity count under the explicit bridge. -/
def ContourResidueSumEqualsN (T : ℝ) : Prop :=
  ∃ (_hT : 0 < T) (_hSafe : IsSafeHeight T), ∃ (resSum : ℂ),
    resSum = entireXiCriticalBoxResidueSum T ∧
      resSum = entireXiContourIntegral T / (2 * Real.pi * I)

theorem contour_residue_sum_equals_N_of_safe {T : ℝ} (hT : 0 < T)
    (hSafe : IsSafeHeight T) (hBridge : ArgumentPrincipleBridge T) :
    ContourResidueSumEqualsN T := by
  refine ⟨hT, hSafe, entireXiCriticalBoxResidueSum T, rfl, ?_⟩
  exact hBridge.residue_sum.symm

/-- Argument-principle count: the contour integral is `2πi * N(T)`. -/
def ContourWindingEqualsCount (T : ℝ) : Prop :=
  ∃ (_hT : 0 < T) (_hSafe : IsSafeHeight T),
    entireXiContourIntegral T = 2 * Real.pi * I * zeroCountingWithMultiplicity T

theorem contour_winding_equals_count_of_safe {T : ℝ} (hT : 0 < T)
    (hSafe : IsSafeHeight T) (hBridge : ArgumentPrincipleBridge T) :
    ContourWindingEqualsCount T := by
  refine ⟨hT, hSafe, ?_⟩
  have h2pi_ne : (2 * Real.pi * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hdiv :
      entireXiContourIntegral T / (2 * Real.pi * I) =
        (zeroCountingWithMultiplicity T : ℂ) := by
    rw [hBridge.residue_sum]
    simp [entireXiCriticalBoxResidueSum, zeroCountingWithMultiplicity]
  calc
    entireXiContourIntegral T
        = (2 * Real.pi * I) * (entireXiContourIntegral T / (2 * Real.pi * I)) := by
          field_simp [h2pi_ne]
    _ = (2 * Real.pi * I) * (zeroCountingWithMultiplicity T : ℂ) := by rw [hdiv]
    _ = 2 * Real.pi * I * zeroCountingWithMultiplicity T := by ring

/-- Global existence form used by later contour packages. -/
def ContourWindingEqualsCountEventually : Prop :=
  ∀ T > 0, ∃ T' ≥ T, IsSafeHeight T' ∧
    ArgumentPrincipleBridge T' ∧ ContourWindingEqualsCount T'

theorem contour_winding_equals_count_forall
    (h : ∀ T > 0, ∃ T' ≥ T, IsSafeHeight T' ∧ ArgumentPrincipleBridge T') :
    ContourWindingEqualsCountEventually := by
  intro T hT
  obtain ⟨T', hle, hSafe, hBridge⟩ := h T hT
  have hT' : 0 < T' := hT.trans_le hle
  exact ⟨T', hle, hSafe, hBridge, contour_winding_equals_count_of_safe hT' hSafe hBridge⟩

end RiemannArgumentPrinciple
