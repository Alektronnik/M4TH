/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import ConservationLaws.ShockReduction

/-!
# The Burgers equation: Lax entropy condition and admissibility

The inviscid Burgers equation is the scalar conservation law with flux
`f (u) = u ^ 2 / 2`.  This file instantiates the general theory at this flux and
develops what is genuinely specific to it:

* the Rankine–Hugoniot speed is the arithmetic mean of the two states, and it is
  the unique admissible speed when the states differ;
* the Lax entropy condition `uL > s > uR` (the characteristics `f' (u) = u`
  impinge on the shock from both sides), equivalent to compression;
* the Lax entropy pair `η (u) = u ^ 2 / 2`, `q (u) = u ^ 3 / 6` and the sign of
  the entropy dissipation across the jump.

The headline results exhibit, inside the same formal framework, both the
physically admissible solution and the classical **non-uniqueness pathology** of
weak solutions:

* `compression_midpoint_is_physical_weak_solution`: the compression step at
  midpoint speed is an admissible weak solution;
* `expansion_midpoint_is_weak_but_not_entropic`: the expansion step at midpoint
  speed is a genuine weak solution that violates the Lax condition and produces
  strictly positive entropy dissipation.

## Main definitions

- `ConservationLaw.burgersFlux`: the Burgers flux `u ↦ u ^ 2 / 2`.
- `ConservationLaw.LaxEntropyCondition`: `uL > s ∧ s > uR`.
- `ConservationLaw.entropy`, `ConservationLaw.entropyFlux`,
  `ConservationLaw.entropyDissipation`: the Lax entropy pair and the jump
  dissipation.

## Main results

- `ConservationLaw.rankineHugoniot_midpoint`,
  `ConservationLaw.rankineHugoniot_speed_unique`.
- `ConservationLaw.laxEntropy_iff_compression`.
- `ConservationLaw.compression_entropy_dissipation_nonpos`,
  `ConservationLaw.expansion_entropy_dissipation_pos`.
- `ConservationLaw.expansion_midpoint_is_weak_but_not_entropic`
  (formalised non-uniqueness of weak solutions).

## Implementation notes

`LaxEntropyCondition` is stated in the Burgers-specific form `uL > s > uR`; via
`deriv_burgersFlux` this is definitionally the general Lax condition
`f' (uL) > s > f' (uR)` for this flux.  The entropy results are stated for
nonnegative states, which is the regime where the explicit quadratic form of the
dissipation has a sign; the general convex-flux theory is future work.

## Tags

Burgers equation, entropy condition, Lax condition, shock wave, non-uniqueness
-/

open MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ConservationLaw

/-- The Burgers flux `f (u) = u ^ 2 / 2`. -/
noncomputable def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2

@[simp] lemma burgersFlux_zero : burgersFlux 0 = 0 := by
  simp [burgersFlux]

/-- The identically zero function is a weak solution of Burgers. -/
theorem isWeakSolution_zero_burgers (T : ℝ) :
    IsWeakSolution burgersFlux T (fun _ _ => 0) :=
  isWeakSolution_zero burgersFlux_zero T

/-- For the Burgers flux, the Rankine–Hugoniot speed is the arithmetic mean of
the left and right states. -/
theorem rankineHugoniot_midpoint (uL uR : ℝ) :
    RankineHugoniot burgersFlux uL uR ((uL + uR) / 2) := by
  unfold RankineHugoniot burgersFlux
  ring

/-- The shock speed is unique when the states differ. -/
theorem rankineHugoniot_speed_unique {uL uR s : ℝ} (hne : uL ≠ uR)
    (h : RankineHugoniot burgersFlux uL uR s) : s = (uL + uR) / 2 := by
  unfold RankineHugoniot burgersFlux at h
  have hfactor : (uL - uR) * (2 * s - (uL + uR)) = 0 := by
    nlinarith
  have hsecond : 2 * s - (uL + uR) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
  linarith

/-- The travelling step at midpoint speed is a weak solution of Burgers,
unconditionally. -/
theorem isWeakSolution_shockProfile_midpoint (T uL uR : ℝ) :
    IsWeakSolution burgersFlux T (shockProfile uL uR ((uL + uR) / 2)) :=
  isWeakSolution_shockProfile_of_rankineHugoniot T uL uR ((uL + uR) / 2)
    (rankineHugoniot_midpoint uL uR)

/-! ### The Lax criterion -/

/-- Lax entropy condition for Burgers (`f' (u) = u`): the characteristics enter
the shock from both sides. -/
def LaxEntropyCondition (uL uR s : ℝ) : Prop :=
  uL > s ∧ s > uR

/-- The derivative of the Burgers flux is the characteristic speed. -/
lemma deriv_burgersFlux (u : ℝ) : deriv burgersFlux u = u := by
  unfold burgersFlux
  simp [deriv_div_const]

/-- With the Rankine–Hugoniot speed and distinct states, Lax ⟺ compression. -/
theorem laxEntropy_iff_compression {uL uR s : ℝ}
    (hRH : RankineHugoniot burgersFlux uL uR s) (hne : uL ≠ uR) :
    LaxEntropyCondition uL uR s ↔ IsCompressionShock uL uR := by
  have hs : s = (uL + uR) / 2 := rankineHugoniot_speed_unique hne hRH
  constructor
  · intro ⟨hL, hR⟩
    unfold IsCompressionShock
    linarith
  · intro hcomp
    rw [hs]
    unfold IsCompressionShock at hcomp
    constructor <;> linarith

/-- An expansion shock violates Lax even though it satisfies Rankine–Hugoniot. -/
theorem expansion_violates_lax {uL uR : ℝ} (hexp : IsExpansionShock uL uR)
    (_hRH : RankineHugoniot burgersFlux uL uR ((uL + uR) / 2)) :
    ¬ LaxEntropyCondition uL uR ((uL + uR) / 2) := by
  intro ⟨hL, hR⟩
  unfold IsExpansionShock at hexp
  linarith

/-! ### The Oleinik entropy criterion -/

/-- Lax entropy for Burgers: `η (u) = u ^ 2 / 2`. -/
noncomputable def entropy (u : ℝ) : ℝ :=
  u ^ 2 / 2

/-- Associated entropy flux: `q (u) = u ^ 3 / 6`. -/
noncomputable def entropyFlux (u : ℝ) : ℝ :=
  u ^ 3 / 6

/--
Entropy dissipation across the jump `(uL, uR)` with speed `s`.
It is `≤ 0` on compression shocks with nonnegative states.
-/
noncomputable def entropyDissipation (uL uR s : ℝ) : ℝ :=
  s * (entropy uR - entropy uL) + entropyFlux uL - entropyFlux uR

/-- Explicit formula at the Rankine–Hugoniot speed. -/
lemma entropyDissipation_midpoint_eq (uL uR : ℝ) :
    entropyDissipation uL uR ((uL + uR) / 2) =
      (uL - uR) * (-uL ^ 2 - 4 * uL * uR - uR ^ 2) / 12 := by
  unfold entropyDissipation entropy entropyFlux
  ring

private lemma entropy_quadratic_nonpos_of_nonneg {uL uR : ℝ}
    (h0 : 0 ≤ uR) (hle : uR ≤ uL) :
    -uL ^ 2 - 4 * uL * uR - uR ^ 2 ≤ 0 := by
  have hL : 0 ≤ uL := le_trans h0 hle
  nlinarith [sq_nonneg (uL + uR), mul_nonneg hL h0]

/-- Compression with nonnegative states: nonpositive entropy dissipation. -/
theorem compression_entropy_dissipation_nonpos {uL uR : ℝ}
    (h0 : 0 ≤ uR) (hcomp : IsCompressionShock uL uR) :
    entropyDissipation uL uR ((uL + uR) / 2) ≤ 0 := by
  rw [entropyDissipation_midpoint_eq]
  unfold IsCompressionShock at hcomp
  have hle : uR ≤ uL := hcomp.le
  have hquad := entropy_quadratic_nonpos_of_nonneg h0 hle
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [hquad]
  · norm_num

/-- Expansion with nonnegative states: strictly positive entropy dissipation. -/
theorem expansion_entropy_dissipation_pos {uL uR : ℝ}
    (h0 : 0 ≤ uL) (hexp : IsExpansionShock uL uR) :
    0 < entropyDissipation uL uR ((uL + uR) / 2) := by
  rw [entropyDissipation_midpoint_eq]
  unfold IsExpansionShock at hexp
  have hlt : uL < uR := hexp
  have hRpos : 0 < uR := by
    by_contra h
    push Not at h
    linarith [h0]
  have hquad : -uL ^ 2 - 4 * uL * uR - uR ^ 2 < 0 := by
    nlinarith [sq_nonneg (uL + uR), mul_nonneg h0 (le_of_lt hRpos), sq_pos_of_pos hRpos]
  have hpos : 0 < (uL - uR) * (-uL ^ 2 - 4 * uL * uR - uR ^ 2) / 12 := by
    apply div_pos
    · nlinarith [hquad]
    · norm_num
  linarith

/-! ### Packaging: physical shock = admissible weak solution -/

/--
Main physical theorem: the compression shock at the mean speed
`(uL + uR) / 2` is an admissible weak solution.
-/
theorem compression_midpoint_is_physical_weak_solution (T uL uR : ℝ)
    (hcomp : IsCompressionShock uL uR) :
    IsWeakSolution burgersFlux T (shockProfile uL uR ((uL + uR) / 2)) :=
  isWeakSolution_of_physicalShock T uL uR ((uL + uR) / 2)
    ⟨hcomp, rankineHugoniot_midpoint uL uR⟩
    (hasShockIntegralReduction burgersFlux T uL uR ((uL + uR) / 2))

/-- Explicit version with the Lax condition. -/
theorem compression_midpoint_satisfies_lax {uL uR : ℝ}
    (hcomp : IsCompressionShock uL uR) :
    LaxEntropyCondition uL uR ((uL + uR) / 2) := by
  have hne : uL ≠ uR := ne_of_gt hcomp
  exact (laxEntropy_iff_compression (rankineHugoniot_midpoint uL uR) hne).mpr hcomp

/--
**Non-uniqueness of weak solutions, formalised.**  The expansion shock is a
weak solution but violates Lax and (with nonnegative states) produces positive
entropy dissipation.
-/
theorem expansion_midpoint_is_weak_but_not_entropic (T uL uR : ℝ)
    (hexp : IsExpansionShock uL uR) (h0 : 0 ≤ uL) :
    IsWeakSolution burgersFlux T (shockProfile uL uR ((uL + uR) / 2)) ∧
      ¬ LaxEntropyCondition uL uR ((uL + uR) / 2) ∧
      0 < entropyDissipation uL uR ((uL + uR) / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact isWeakSolution_shockProfile_midpoint T uL uR
  · exact expansion_violates_lax hexp (rankineHugoniot_midpoint uL uR)
  · exact expansion_entropy_dissipation_pos h0 hexp

/-! ### Certificates

Concrete instances checked by the kernel.  After `lake build`, running

  `#print axioms ConservationLaw.hasShockIntegralReduction`

must report only the foundational axioms `propext`, `Classical.choice`,
`Quot.sound`. -/

section Certificates

/-- The zero solution on `(0, 1) × ℝ`. -/
example : IsWeakSolution burgersFlux 1 (fun _ _ => 0) :=
  isWeakSolution_zero_burgers 1

/-- The step from `2` down to `0` moving at speed `1` satisfies
Rankine–Hugoniot. -/
example : RankineHugoniot burgersFlux 2 0 1 := by
  unfold RankineHugoniot burgersFlux
  norm_num

/-- That step is a weak solution on `(0, 1) × ℝ`. -/
example : IsWeakSolution burgersFlux 1 (shockProfile 2 0 1) :=
  isWeakSolution_shockProfile_of_rankineHugoniot 1 2 0 1
    (by unfold RankineHugoniot burgersFlux; norm_num)

/-- It satisfies the Lax entropy condition. -/
example : LaxEntropyCondition 2 0 1 := by
  unfold LaxEntropyCondition
  norm_num

/-- The expansion step from `0` up to `2`: a weak solution that violates Lax
and dissipates entropy with the wrong sign — the classical non-uniqueness
pathology, certified. -/
example :
    IsWeakSolution burgersFlux 1 (shockProfile 0 2 ((0 + 2) / 2)) ∧
      ¬ LaxEntropyCondition 0 2 ((0 + 2) / 2) ∧
      0 < entropyDissipation 0 2 ((0 + 2) / 2) :=
  expansion_midpoint_is_weak_but_not_entropic 1 0 2
    (by unfold IsExpansionShock; norm_num) (by norm_num)

end Certificates

end ConservationLaw

end
