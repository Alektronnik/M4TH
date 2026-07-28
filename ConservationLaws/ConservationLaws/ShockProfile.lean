/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import ConservationLaws.WeakSolution

/-!
# Travelling shock profiles and the Rankine–Hugoniot condition

The elementary discontinuous candidate solution of a scalar conservation law:
the step profile `u (t, x) = uL` for `x < s t`, `uR` otherwise, travelling with
speed `s`, and the algebraic Rankine–Hugoniot condition
`s (uL - uR) = f uL - f uR` that a speed must satisfy for the step to be a weak
solution.

## Main definitions

- `ConservationLaw.shockProfile`: the moving step.
- `ConservationLaw.RankineHugoniot`: the jump condition for a flux `f`.
- `ConservationLaw.HasShockIntegralReduction`: the precise statement that the
  distributional residual of the step collapses to a boundary integral along the
  moving interface.  It is a property, not an axiom: it is proved without any
  hypotheses in `ConservationLaws.ShockReduction`.
- `ConservationLaw.IsCompressionShock`, `ConservationLaw.IsExpansionShock`,
  `ConservationLaw.PhysicalShock`: the classification of shocks.

## Main results

- `ConservationLaw.integral_spatial_split`: away from the null interface point,
  the spatial integral splits into the two constant states.
- `ConservationLaw.locallyIntegrableOn_shockProfile`,
  `ConservationLaw.locallyIntegrableOn_comp_shockProfile`: the step and its flux
  are locally integrable.
- `ConservationLaw.weakResidual_eq_zero_of_rankineHugoniot`,
  `ConservationLaw.isWeakSolution_shockProfile`: Rankine–Hugoniot kills the
  interface term once the integral reduction is available.

## Implementation notes

The sign convention in `HasShockIntegralReduction` comes from

  `d/dt ∫_{x < s t} φ (t, x) dx = ∫_{x < s t} ∂ₜφ (t, x) dx + s φ (t, s t)`.

Everything in this file is stated for an arbitrary flux `f : ℝ → ℝ`; the flux
only appears evaluated at the two states.

## Tags

shock wave, Rankine-Hugoniot, weak solution, conservation law
-/

open MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ConservationLaw

/-- Elementary discontinuous profile: a shock travelling with speed `s`. -/
noncomputable def shockProfile (uL uR s : ℝ) (t x : ℝ) : ℝ :=
  if x < s * t then uL else uR

/-- Rankine–Hugoniot condition for a shock of speed `s` and flux `f`. -/
def RankineHugoniot (f : ℝ → ℝ) (uL uR s : ℝ) : Prop :=
  s * (uL - uR) = f uL - f uR

/-- Any function commutes with the step: `f ∘ shockProfile` is the step between
the flux values. -/
lemma comp_shockProfile (f : ℝ → ℝ) (uL uR s t x : ℝ) :
    f (shockProfile uL uR s t x) =
      shockProfile (f uL) (f uR) s t x := by
  by_cases h : x < s * t <;> simp [shockProfile, h]

/-- Up to the null interface point, the spatial integral splits into the left
and right constant states. -/
lemma integral_spatial_split {f : ℝ → ℝ} {T : ℝ} (φ : TestFunction T)
    (uL uR s t : ℝ) :
    (∫ x, weakIntegrand f (shockProfile uL uR s) φ t x) =
      (∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) +
      (∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) := by
  let b := s * t
  let fL := fun x => weakIntegrand f (fun _ _ => uL) φ t x
  let fR := fun x => weakIntegrand f (fun _ _ => uR) φ t x
  have hL : Integrable fL := integrable_weakIntegrand_const_spaceSlice φ uL t
  have hR : Integrable fR := integrable_weakIntegrand_const_spaceSlice φ uR t
  have hne : ∀ᵐ x : ℝ, x ≠ b := by
    simp [ae_iff, measure_singleton]
  have hAE :
      (fun x => weakIntegrand f (shockProfile uL uR s) φ t x) =ᵐ[volume]
        (Iic b).piecewise fL fR := by
    filter_upwards [hne] with x hx
    by_cases hxb : x ≤ b
    · have hlt : x < b := lt_of_le_of_ne hxb hx
      have hu : shockProfile uL uR s t x = uL := by
        rw [shockProfile, if_pos]
        simpa [b] using hlt
      have hxmem : x ∈ Iic b := hxb
      simp only [Set.piecewise, hxmem, if_true, fL, weakIntegrand]
      rw [hu]
    · have hgt : b < x := lt_of_not_ge hxb
      have hu : shockProfile uL uR s t x = uR := by
        rw [shockProfile, if_neg]
        exact not_lt_of_ge (by simpa [b] using hgt.le)
      have hxmem : x ∉ Iic b := hxb
      simp only [Set.piecewise, hxmem, if_false, fR, weakIntegrand]
      rw [hu]
  calc
    (∫ x, weakIntegrand f (shockProfile uL uR s) φ t x) =
        ∫ x, (Iic b).piecewise fL fR x := integral_congr_ae hAE
    _ = (∫ x in Iic b, fL x) + (∫ x in (Iic b)ᶜ, fR x) :=
      integral_piecewise measurableSet_Iic hL.integrableOn hR.integrableOn
    _ = (∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) +
        (∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) := by
      simp only [compl_Iic, b, fL, fR]

private lemma shockRegion_measurable (s : ℝ) :
    MeasurableSet {p : ℝ × ℝ | p.2 < s * p.1} := by
  exact (isOpen_lt continuous_snd (continuous_const.mul continuous_fst)).measurableSet

/-- The moving step is locally integrable: it is the sum of a constant and the
measurable indicator of an open half-plane. -/
theorem locallyIntegrableOn_shockProfile (T uL uR s : ℝ) :
    LocallyIntegrableOn
      (fun p : ℝ × ℝ => shockProfile uL uR s p.1 p.2)
      (spacetimeDomain T) := by
  let A : Set (ℝ × ℝ) := {p | p.2 < s * p.1}
  have hA : MeasurableSet A := shockRegion_measurable s
  have hconst : LocallyIntegrable (fun _ : ℝ × ℝ => uR) :=
    locallyIntegrable_const uR
  have hind : LocallyIntegrable (A.indicator (fun _ : ℝ × ℝ => uL - uR)) :=
    (locallyIntegrable_const (uL - uR)).indicator hA
  have hsum := hconst.add hind
  have hfun :
      (fun p : ℝ × ℝ => shockProfile uL uR s p.1 p.2) =
        (fun _ : ℝ × ℝ => uR) + A.indicator (fun _ : ℝ × ℝ => uL - uR) := by
    funext p
    simp only [Pi.add_apply]
    by_cases hp : p ∈ A
    · change p.2 < s * p.1 at hp
      simp [A, shockProfile, hp]
    · have hp' : ¬p.2 < s * p.1 := by simpa [A] using hp
      simp [A, shockProfile, hp']
  rw [hfun]
  exact hsum.locallyIntegrableOn (spacetimeDomain T)

/-- The flux of the step is also locally integrable. -/
theorem locallyIntegrableOn_comp_shockProfile (f : ℝ → ℝ) (T uL uR s : ℝ) :
    LocallyIntegrableOn
      (fun p : ℝ × ℝ => f (shockProfile uL uR s p.1 p.2))
      (spacetimeDomain T) := by
  simpa only [comp_shockProfile] using
    locallyIntegrableOn_shockProfile T (f uL) (f uR) s

/--
Precise statement of the reduction of the residual to the moving boundary.  The
sign comes from

  `d/dt ∫_{x < s t} φ (t, x) dx = ∫_{x < s t} ∂ₜφ (t, x) dx + s φ (t, s t)`.

Defined as a property (not an axiom), so that the possible analytic proofs can
supply it without weakening the theory.  It is proved, with no hypotheses on
`f`, in `ConservationLaws.ShockReduction`.
-/
def HasShockIntegralReduction (f : ℝ → ℝ) (T uL uR s : ℝ) : Prop :=
  ∀ φ : TestFunction T,
    weakResidual f (shockProfile uL uR s) φ =
      ∫ t in Ioo 0 T,
        ((f uL - f uR) - s * (uL - uR)) * φ t (s * t)

/-- Rankine–Hugoniot kills the interface term once the analytic reduction to
the moving boundary is available. -/
theorem weakResidual_eq_zero_of_rankineHugoniot {f : ℝ → ℝ}
    (T uL uR s : ℝ) (hreduction : HasShockIntegralReduction f T uL uR s)
    (hRH : RankineHugoniot f uL uR s) (φ : TestFunction T) :
    weakResidual f (shockProfile uL uR s) φ = 0 := by
  rw [hreduction φ]
  unfold RankineHugoniot at hRH
  rw [hRH]
  simp

/-- Rigorous packaging of the shock theorem: integrability is already proved and
the weak identity follows from the boundary reduction and Rankine–Hugoniot. -/
theorem isWeakSolution_shockProfile {f : ℝ → ℝ}
    (T uL uR s : ℝ) (hreduction : HasShockIntegralReduction f T uL uR s)
    (hRH : RankineHugoniot f uL uR s) :
    IsWeakSolution f T (shockProfile uL uR s) := by
  refine ⟨locallyIntegrableOn_shockProfile T uL uR s,
    locallyIntegrableOn_comp_shockProfile f T uL uR s, ?_⟩
  intro φ
  exact weakResidual_eq_zero_of_rankineHugoniot T uL uR s hreduction hRH φ

/-! ### Classification of shocks -/

/-- Compression shock: the fluid decelerates across the interface. -/
def IsCompressionShock (uL uR : ℝ) : Prop :=
  uL > uR

/-- Expansion shock: mathematically weak, physically inadmissible. -/
def IsExpansionShock (uL uR : ℝ) : Prop :=
  uL < uR

/-- Physically admissible profile: compression + Rankine–Hugoniot speed. -/
structure PhysicalShock (f : ℝ → ℝ) (uL uR s : ℝ) : Prop where
  /-- The states compress across the interface. -/
  compression : IsCompressionShock uL uR
  /-- The speed satisfies the Rankine–Hugoniot condition. -/
  rankine : RankineHugoniot f uL uR s

/-- A compression shock with Rankine–Hugoniot speed is a weak solution. -/
theorem isWeakSolution_of_physicalShock {f : ℝ → ℝ} (T uL uR s : ℝ)
    (hphys : PhysicalShock f uL uR s)
    (hreduction : HasShockIntegralReduction f T uL uR s) :
    IsWeakSolution f T (shockProfile uL uR s) :=
  isWeakSolution_shockProfile T uL uR s hreduction hphys.rankine

end ConservationLaw

end
