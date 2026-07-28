/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import ConservationLaws.TestFunction

/-!
# Weak solutions of scalar conservation laws

The distributional formulation of the scalar conservation law

  `∂ₜ u + ∂ₓ (f (u)) = 0`  on `(0, T) × ℝ`,

for an arbitrary flux `f : ℝ → ℝ`.  A weak solution needs no derivatives of its
own: all derivatives fall on the smooth compactly supported test functions of
`ConservationLaws.TestFunction`, and the solution itself is only required to be
locally integrable together with its flux.

## Main definitions

- `ConservationLaw.weakIntegrand`: the integrand `u ∂ₜφ + f (u) ∂ₓφ`.
- `ConservationLaw.weakResidual`: the distributional residual
  `∫_{(0,T)} ∫_ℝ (u ∂ₜφ + f (u) ∂ₓφ)`.
- `ConservationLaw.IsWeakSolution`: local integrability of `u` and `f ∘ u` on
  the cylinder, together with the vanishing of the residual against every test
  function.

## Main results

- `ConservationLaw.isWeakSolution_zero`: the zero function is a weak solution
  whenever the flux vanishes at the origin.

## Implementation notes

The flux is a completely arbitrary function `ℝ → ℝ` here.  No regularity of `f`
is used anywhere in this file, nor in the shock-reduction theory built on top of
it: the flux only ever appears evaluated at fixed states.  Structure and
regularity hypotheses on `f` (continuity, convexity, `f 0 = 0`) enter only in
the results that genuinely need them, stated as explicit hypotheses.

## Tags

conservation law, weak solution, distributional solution
-/

open MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ConservationLaw

/-- The integrand of the weak formulation for the flux `f`. -/
noncomputable def weakIntegrand (f : ℝ → ℝ) {T : ℝ} (u : ℝ → ℝ → ℝ)
    (φ : TestFunction T) (t x : ℝ) : ℝ :=
  u t x * φ.dt t x + f (u t x) * φ.dx t x

/--
Distributional residual for the flux `f`.  The outer integral is restricted to
`(0, T)`; the test function controls the integral over the whole line.
-/
noncomputable def weakResidual (f : ℝ → ℝ) {T : ℝ} (u : ℝ → ℝ → ℝ)
    (φ : TestFunction T) : ℝ :=
  ∫ t in Ioo 0 T, ∫ x : ℝ, weakIntegrand f u φ t x

/-- For a constant state, the weak integrand is integrable in the spatial
variable for every time. -/
lemma integrable_weakIntegrand_const_spaceSlice {f : ℝ → ℝ} {T : ℝ}
    (φ : TestFunction T) (a t : ℝ) :
    Integrable (fun x => weakIntegrand f (fun _ _ => a) φ t x) := by
  change Integrable
    ((fun x => a * φ.dt t x) + fun x => f a * φ.dx t x)
  apply Integrable.add
  · exact (φ.integrable_dt_spaceSlice t).const_mul a
  · exact (φ.integrable_dx t).const_mul (f a)

/--
Weak-solution predicate for the flux `f` on `(0, T) × ℝ`.

The first two conditions express `u, f ∘ u ∈ L¹_loc`, which is the minimal
regularity needed to interpret the flux.  The last is the distributional
identity against every test function.
-/
structure IsWeakSolution (f : ℝ → ℝ) (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  /-- The solution is locally integrable on the cylinder. -/
  locallyIntegrable :
    LocallyIntegrableOn (fun p : ℝ × ℝ => u p.1 p.2) (spacetimeDomain T)
  /-- The flux of the solution is locally integrable on the cylinder. -/
  fluxLocallyIntegrable :
    LocallyIntegrableOn (fun p : ℝ × ℝ => f (u p.1 p.2)) (spacetimeDomain T)
  /-- The distributional identity against every test function. -/
  weak_identity : ∀ φ : TestFunction T, weakResidual f u φ = 0

/-- The weak integrand of the zero function vanishes pointwise when the flux
vanishes at the origin. -/
@[simp] lemma weakIntegrand_zero {f : ℝ → ℝ} (hf0 : f 0 = 0) {T : ℝ}
    (φ : TestFunction T) (t x : ℝ) :
    weakIntegrand f (fun _ _ => 0) φ t x = 0 := by
  simp [weakIntegrand, hf0]

/-- The distributional residual of the zero function is zero when the flux
vanishes at the origin. -/
@[simp] theorem weakResidual_zero {f : ℝ → ℝ} (hf0 : f 0 = 0) {T : ℝ}
    (φ : TestFunction T) :
    weakResidual f (fun _ _ => 0) φ = 0 := by
  simp [weakResidual, weakIntegrand, hf0]

/-- The identically zero function is a weak solution for every `T`, provided
the flux vanishes at the origin. -/
theorem isWeakSolution_zero {f : ℝ → ℝ} (hf0 : f 0 = 0) (T : ℝ) :
    IsWeakSolution f T (fun _ _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact integrableOn_zero.locallyIntegrableOn
  · simpa [hf0] using
      (integrableOn_zero.locallyIntegrableOn :
        LocallyIntegrableOn (fun _ : ℝ × ℝ => (0 : ℝ)) (spacetimeDomain T))
  · intro φ
    exact weakResidual_zero hf0 φ

end ConservationLaw

end
