/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Tactic.SetNotationForOrder
import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# ConservationLaws live edition

Single-file live edition of the `ConservationLaws` package for web
certification and study.  The mathematical content is the package source fused
in dependency order: `TestFunction`, `WeakSolution`, `Galilean`, `ShockProfile`,
`ShockReduction`, and `Burgers`.
-/


/-!
## Source file: `ConservationLaws/TestFunction.lean`
-/

/-!
# Test functions on the space-time cylinder

This file introduces the class of test functions used in the weak (distributional)
formulation of one-dimensional scalar conservation laws
`∂ₜ u + ∂ₓ (f (u)) = 0` on the open cylinder `(0, T) × ℝ`.

A test function is a jointly smooth, compactly supported function `φ : ℝ → ℝ → ℝ`
whose topological support is contained in the open cylinder.  The last condition
makes all boundary terms at `t = 0`, `t = T` and at spatial infinity vanish, which
is what allows integration by parts against merely locally integrable solutions.

## Main definitions

- `ConservationLaw.spacetimeDomain`: the open cylinder `(0, T) × ℝ`.
- `ConservationLaw.TestFunction`: smooth compactly supported functions with
  support inside the cylinder.
- `ConservationLaw.TestFunction.dt`, `ConservationLaw.TestFunction.dx`: the two
  partial derivatives of a test function.

## Main results

- `ConservationLaw.TestFunction.integral_Iic_dx`,
  `ConservationLaw.TestFunction.integral_Ioi_dx`: the improper fundamental theorem
  of calculus on half-lines; the contribution at infinity vanishes by compact
  support.
- `ConservationLaw.TestFunction.eq_zero_at_zero`,
  `ConservationLaw.TestFunction.eq_zero_at_terminal`: a test function vanishes on
  the initial and terminal time slices.

## Implementation notes

We work with the explicit product measure `planeMeasure = volume.prod volume` on
`ℝ × ℝ`.  On this space it is definitionally equal to `volume` (the lemma
`setIntegral_plane` is proved by `rfl`), but naming it keeps elaboration and
instance resolution predictable in the Fubini arguments of subsequent files.
Reviewers may prefer to inline it through `MeasureTheory.Measure.volume_eq_prod`.

The auxiliary lemmas `hasDerivAt_prodMk`, `fderiv_coord_fst`, `fderiv_coord_snd`
and `fderiv_apply_decomp` decompose the Fréchet derivative of a curried function
of two real variables into its two partial derivatives.  They are stated here in
the exact generality needed by this development; close relatives may already
exist in Mathlib and should be deduplicated at review time.

## Tags

conservation law, test function, weak solution, compact support
-/

open MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ConservationLaw

/-! ### Auxiliary lemmas on the product structure of `ℝ × ℝ` -/

/-- Lebesgue measure on the plane as an explicit product (avoids instance
ambiguity in Fubini arguments).  Definitionally equal to `volume`. -/
noncomputable def planeMeasure : Measure (ℝ × ℝ) :=
  (volume : Measure ℝ).prod (volume : Measure ℝ)

lemma setIntegral_plane {f : ℝ × ℝ → ℝ} {s t : Set ℝ} :
    (∫ z in s ×ˢ t, f z) = (∫ z in s ×ˢ t, f z ∂planeMeasure) := by
  dsimp [planeMeasure]
  rfl

lemma setIntegral_plane_prod {f : ℝ × ℝ → ℝ} {s t : Set ℝ}
    (hf : IntegrableOn f (s ×ˢ t) planeMeasure) :
    (∫ z in s ×ˢ t, f z ∂planeMeasure) =
      ∫ x in s, ∫ y in t, f (x, y) :=
  setIntegral_prod (μ := volume) (ν := volume) f hf

lemma setIntegral_plane_prod_symm {f : ℝ × ℝ → ℝ} {s t : Set ℝ}
    (hf : IntegrableOn f (s ×ˢ t) planeMeasure) :
    (∫ x in s, ∫ y in t, f (x, y)) =
      (∫ z in s ×ˢ t, f z ∂planeMeasure) :=
  (setIntegral_plane_prod hf).symm

lemma integrableOn_plane_of_integrable {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hf : Integrable f) : IntegrableOn f s planeMeasure := by
  dsimp [IntegrableOn, planeMeasure]
  exact hf.integrableOn

/-- A curve with both coordinates differentiable is differentiable into the
product, with the pair of derivatives as derivative. -/
lemma hasDerivAt_prodMk {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => (f y, g y)) (f', g') x := by
  convert (hf.hasFDerivAt.prodMk hg.hasFDerivAt).hasDerivAt using 1
  ext <;> simp

/-- The Fréchet derivative evaluated at `(1, 0)` is the partial derivative in
the first coordinate. -/
lemma fderiv_coord_fst (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
    (h : DifferentiableAt ℝ (fun q : ℝ × ℝ => u q.1 q.2) p) :
    fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p (1, 0) =
      deriv (fun t => u t p.2) p.1 := by
  have hline : HasDerivAt (fun t : ℝ => (t, p.2)) (1, 0) p.1 :=
    hasDerivAt_prodMk (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2)
  change fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p (1, 0) =
    deriv ((fun q : ℝ × ℝ => u q.1 q.2) ∘ fun t : ℝ => (t, p.2)) p.1
  exact (h.hasFDerivAt.comp_hasDerivAt p.1 hline).deriv.symm

/-- The Fréchet derivative evaluated at `(0, 1)` is the partial derivative in
the second coordinate. -/
lemma fderiv_coord_snd (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
    (h : DifferentiableAt ℝ (fun q : ℝ × ℝ => u q.1 q.2) p) :
    fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p (0, 1) =
      deriv (u p.1) p.2 := by
  have hline : HasDerivAt (fun x : ℝ => (p.1, x)) (0, 1) p.2 :=
    hasDerivAt_prodMk (hasDerivAt_const p.2 p.1) (hasDerivAt_id p.2)
  change fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p (0, 1) =
    deriv ((fun q : ℝ × ℝ => u q.1 q.2) ∘ fun x : ℝ => (p.1, x)) p.2
  exact (h.hasFDerivAt.comp_hasDerivAt p.2 hline).deriv.symm

/-- Linear decomposition of the Fréchet derivative into partial derivatives. -/
lemma fderiv_apply_decomp (u : ℝ → ℝ → ℝ) (p v : ℝ × ℝ)
    (h : DifferentiableAt ℝ (fun q : ℝ × ℝ => u q.1 q.2) p) :
    fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p v =
      v.1 * deriv (fun t => u t p.2) p.1 + v.2 * deriv (u p.1) p.2 := by
  let L := fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
  change L v = _
  rw [hv, map_add, map_smul, map_smul]
  rw [fderiv_coord_fst u p h, fderiv_coord_snd u p h]
  simp [smul_eq_mul]

/-! ### The space-time cylinder and test functions -/

/-- The open space-time cylinder `(0, T) × ℝ`. -/
def spacetimeDomain (T : ℝ) : Set (ℝ × ℝ) := Ioo 0 T ×ˢ (univ : Set ℝ)

/--
A test function for the problem on `(0, T) × ℝ`: it is smooth, compactly
supported, and its topological support is contained in the open cylinder.
The last condition makes the boundary terms at `t = 0, T` and at spatial
infinity vanish.
-/
structure TestFunction (T : ℝ) where
  /-- The underlying function of time and space. -/
  toFun : ℝ → ℝ → ℝ
  /-- Joint smoothness in `(t, x)`. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => toFun p.1 p.2)
  /-- Joint compact support. -/
  compactSupport : HasCompactSupport (fun p : ℝ × ℝ => toFun p.1 p.2)
  /-- The topological support lies inside the open cylinder. -/
  support_subset : tsupport (fun p : ℝ × ℝ => toFun p.1 p.2) ⊆ spacetimeDomain T

namespace TestFunction

instance (T : ℝ) : CoeFun (TestFunction T) fun _ => ℝ → ℝ → ℝ :=
  ⟨TestFunction.toFun⟩

/-- Time partial derivative of a test function. -/
noncomputable def dt {T : ℝ} (φ : TestFunction T) (t x : ℝ) : ℝ :=
  deriv (fun s => φ s x) t

/-- Space partial derivative of a test function. -/
noncomputable def dx {T : ℝ} (φ : TestFunction T) (t x : ℝ) : ℝ :=
  deriv (φ t) x

/-- Every spatial slice of a test function is smooth. -/
lemma contDiff_spaceSlice {T : ℝ} (φ : TestFunction T) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (φ t) := by
  have hline : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using φ.smooth.comp hline

/-- Every spatial slice has compact support.  The proof projects the joint
compact support of `φ` onto the spatial axis. -/
lemma hasCompactSupport_spaceSlice {T : ℝ} (φ : TestFunction T) (t : ℝ) :
    HasCompactSupport (φ t) := by
  let joint : ℝ × ℝ → ℝ := fun p => φ p.1 p.2
  let K : Set ℝ := Prod.snd '' tsupport joint
  have hK : IsCompact K := φ.compactSupport.image continuous_snd
  apply HasCompactSupport.intro hK
  intro x hx
  by_contra hne
  have hpSupport : (t, x) ∈ Function.support joint := by
    simpa only [Function.mem_support, joint] using hne
  have hpTSupport : (t, x) ∈ tsupport joint := subset_closure hpSupport
  exact hx ⟨(t, x), hpTSupport, rfl⟩

/-- In particular, the spatial slice is `C¹`. -/
lemma contDiff_one_spaceSlice {T : ℝ} (φ : TestFunction T) (t : ℝ) :
    ContDiff ℝ 1 (φ t) :=
  (φ.contDiff_spaceSlice t).of_le (by simp)

/-- Improper FTC on the left half-line: the contribution at `-∞` vanishes by
compact support. -/
lemma integral_Iic_dx {T : ℝ} (φ : TestFunction T) (t b : ℝ) :
    (∫ x in Iic b, φ.dx t x) = φ t b := by
  change (∫ x in Iic b, deriv (φ t) x) = φ t b
  exact HasCompactSupport.integral_Iic_deriv_eq
    (φ.contDiff_one_spaceSlice t) (φ.hasCompactSupport_spaceSlice t) b

/-- Improper FTC on the right half-line: the orientation produces the negative
sign at the boundary. -/
lemma integral_Ioi_dx {T : ℝ} (φ : TestFunction T) (t b : ℝ) :
    (∫ x in Ioi b, φ.dx t x) = -φ t b := by
  change (∫ x in Ioi b, deriv (φ t) x) = -φ t b
  exact HasCompactSupport.integral_Ioi_deriv_eq
    (φ.contDiff_one_spaceSlice t) (φ.hasCompactSupport_spaceSlice t) b

/-- The spatial derivative is integrable on the whole line. -/
lemma integrable_dx {T : ℝ} (φ : TestFunction T) (t : ℝ) :
    Integrable (φ.dx t) := by
  change Integrable (deriv (φ t))
  exact (φ.contDiff_one_spaceSlice t).continuous_deriv le_rfl
    |>.integrable_of_hasCompactSupport (φ.hasCompactSupport_spaceSlice t).deriv

/-- For fixed time, the time derivative depends continuously on `x`. -/
lemma continuous_dt_spaceSlice {T : ℝ} (φ : TestFunction T) (t : ℝ) :
    Continuous (φ.dt t) := by
  let joint : ℝ × ℝ → ℝ := fun p => φ p.1 p.2
  have hraw : Continuous
      (fun x : ℝ => (fderiv ℝ joint (t, x) : ℝ × ℝ →L[ℝ] ℝ) (1, 0)) := by
    have heval := φ.smooth.continuous_fderiv_apply (by simp)
    exact heval.comp
      ((continuous_const.prodMk continuous_id).prodMk continuous_const)
  have heq :
      (fun x : ℝ => (fderiv ℝ joint (t, x) : ℝ × ℝ →L[ℝ] ℝ) (1, 0)) =
        φ.dt t := by
    funext x
    exact fderiv_coord_fst φ.toFun (t, x)
      ((φ.smooth.differentiable (by simp)) (t, x))
  rw [← heq]
  exact hraw

/-- For fixed time, `∂ₜφ (t, ·)` retains compact spatial support. -/
lemma hasCompactSupport_dt_spaceSlice {T : ℝ} (φ : TestFunction T) (t : ℝ) :
    HasCompactSupport (φ.dt t) := by
  let joint : ℝ × ℝ → ℝ := fun p => φ p.1 p.2
  let K : Set ℝ := Prod.snd '' tsupport joint
  have hK : IsCompact K := φ.compactSupport.image continuous_snd
  apply HasCompactSupport.intro hK
  intro x hx
  have hall : (fun τ => φ τ x) = (fun _ => 0) := by
    funext τ
    by_contra hne
    have hpSupport : (τ, x) ∈ Function.support joint := by
      simpa only [Function.mem_support, joint] using hne
    have hpTSupport : (τ, x) ∈ tsupport joint := subset_closure hpSupport
    exact hx ⟨(τ, x), hpTSupport, rfl⟩
  simp only [dt, hall, deriv_const]

/-- The time derivative is also integrable in the spatial variable. -/
lemma integrable_dt_spaceSlice {T : ℝ} (φ : TestFunction T) (t : ℝ) :
    Integrable (φ.dt t) :=
  (φ.continuous_dt_spaceSlice t).integrable_of_hasCompactSupport
    (φ.hasCompactSupport_dt_spaceSlice t)

/-- A test function vanishes on every time slice outside `(0, T)`. -/
lemma eq_zero_of_time_notMem {T : ℝ} (φ : TestFunction T) {t : ℝ}
    (ht : t ∉ Ioo 0 T) (x : ℝ) : φ t x = 0 := by
  by_contra hne
  have hpSupport : (t, x) ∈ Function.support (fun p : ℝ × ℝ => φ p.1 p.2) := by
    simpa only [Function.mem_support] using hne
  have hpTSupport : (t, x) ∈ tsupport (fun p : ℝ × ℝ => φ p.1 p.2) :=
    subset_closure hpSupport
  have hpDomain := φ.support_subset hpTSupport
  exact ht hpDomain.1

@[simp] lemma eq_zero_at_zero {T : ℝ} (φ : TestFunction T) (x : ℝ) :
    φ 0 x = 0 :=
  φ.eq_zero_of_time_notMem (by simp) x

@[simp] lemma eq_zero_at_terminal {T : ℝ} (φ : TestFunction T) (x : ℝ) :
    φ T x = 0 :=
  φ.eq_zero_of_time_notMem (by simp) x

end TestFunction

end ConservationLaw

end


/-!
## Source file: `ConservationLaws/WeakSolution.lean`
-/

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


/-!
## Source file: `ConservationLaws/Galilean.lean`
-/

/-!
# Galilean change of coordinates for test functions

Along the moving frame `x = ξ + s * t` (velocity `s`), the time-derivative term
of the weak formulation of a conservation law against a *constant* state becomes
a total time derivative.  Its time integral then vanishes by the support
conditions of the test function at `t = 0, T`, and Fubini's theorem propagates
this cancellation to the double integrals over the half-planes
`(0, T) × (-∞, 0]` and `(0, T) × (0, ∞)`.

This is the analytic engine behind the exact reduction of the shock residual to
the Rankine–Hugoniot jump proved in `ConservationLaws.ShockReduction`.

## Main definitions

- `ConservationLaw.TestFunction.galilean`: the pullback `φ (t, ξ + s t)`.
- `ConservationLaw.galileanHomeo`: the plane homeomorphism `(t, ξ) ↦ (t, ξ + s t)`.
- `ConservationLaw.TestFunction.galileanTimeDeriv`: the total time derivative in
  the moving frame, as a joint function on the plane.

## Main results

- `ConservationLaw.TestFunction.deriv_galilean_time`: the chain rule
  `d/dt φ(t, ξ + s t) = ∂ₜφ + s ∂ₓφ` (evaluated on the moving line).
- `ConservationLaw.TestFunction.constant_state_galilean`: for constants `a, F`,
  the combination `a ∂ₜφ + F ∂ₓφ` on the moving line splits into a total time
  derivative plus `(F - s a) ∂ₓφ`.
- `ConservationLaw.TestFunction.integral_Ioo_Iic_galilean_time_deriv_zero`,
  `ConservationLaw.TestFunction.integral_Ioo_Ioi_galilean_time_deriv_zero`:
  the double integrals of the total-time-derivative term vanish
  (Fubini + one-dimensional cancellation).

## Implementation notes

Integrability certificates are obtained by transporting compact support through
`galileanHomeo` (`HasCompactSupport.comp_homeomorph`) rather than by direct
estimates; this keeps every integrability proof a composition of continuity and
compact-support facts.
-/

open MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ConservationLaw

/-- The Galilean homeomorphism `(t, ξ) ↦ (t, ξ + s t)` of the plane. -/
noncomputable def galileanHomeo (s : ℝ) : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun p := (p.1, p.2 + s * p.1)
  invFun p := (p.1, p.2 - s * p.1)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

namespace TestFunction

/-- A test function seen from the Galilean frame `x = ξ + s t`. -/
noncomputable def galilean {T : ℝ} (φ : TestFunction T) (s : ℝ) (t ξ : ℝ) : ℝ :=
  φ t (ξ + s * t)

/-- Chain rule in time for the Galilean pullback. -/
lemma deriv_galilean_time {T : ℝ} (φ : TestFunction T) (s t ξ : ℝ) :
    deriv (fun τ => φ.galilean s τ ξ) t =
      φ.dt t (ξ + s * t) + s * φ.dx t (ξ + s * t) := by
  let γ : ℝ → ℝ × ℝ := fun τ => (τ, ξ + s * τ)
  have hγ : HasDerivAt γ (1, s) t := by
    have hsecond : HasDerivAt (fun τ : ℝ => ξ + s * τ) s t := by
      exact (hasDerivAt_const_mul (x := t) s).const_add ξ
    exact hasDerivAt_prodMk (hasDerivAt_id' t) hsecond
  have hφ : DifferentiableAt ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (γ t) :=
    (φ.smooth.differentiable (by simp)) (γ t)
  have hcomp := hφ.hasFDerivAt.comp_hasDerivAt t hγ
  rw [fderiv_apply_decomp φ.toFun (γ t) (1, s) hφ] at hcomp
  dsimp [γ] at hcomp
  simpa only [Function.comp_def, one_mul, galilean, dt, dx] using hcomp.deriv

/-- Galilean transformation of the weak integrand against a constant state `a`
with flux value `F`.  The time term becomes a total derivative.  In applications
`F = f a` for the flux `f` of the conservation law. -/
lemma constant_state_galilean {T : ℝ} (φ : TestFunction T)
    (a F s t ξ : ℝ) :
    a * φ.dt t (ξ + s * t) + F * φ.dx t (ξ + s * t) =
      a * deriv (fun τ => φ.galilean s τ ξ) t +
        (F - s * a) * φ.dx t (ξ + s * t) := by
  rw [φ.deriv_galilean_time s t ξ]
  ring

/-- The Galilean pullback is `C¹` in time for each `ξ`. -/
lemma contDiff_one_galilean_time {T : ℝ} (φ : TestFunction T) (s ξ : ℝ) :
    ContDiff ℝ 1 (fun t => φ.galilean s t ξ) := by
  have hcurve : ContDiff ℝ 1 (fun t : ℝ => (t, ξ + s * t)) := by
    exact contDiff_id.prodMk (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hsmooth : ContDiff ℝ 1 (fun p : ℝ × ℝ => φ p.1 p.2) :=
    φ.smooth.of_le (by simp)
  simpa only [galilean, Function.comp_def] using hsmooth.comp hcurve

/-- The time integral of the total Galilean derivative vanishes by the support
conditions at `t = 0, T`. -/
lemma integral_Ioo_deriv_galilean_time {T : ℝ} (φ : TestFunction T)
    (s ξ : ℝ) :
    (∫ t in Ioo 0 T, deriv (fun τ => φ.galilean s τ ξ) t) = 0 := by
  by_cases hT : 0 ≤ T
  · have hg := φ.contDiff_one_galilean_time s ξ
    have hFTC :
        (∫ t in (0 : ℝ)..T, deriv (fun τ => φ.galilean s τ ξ) t) =
          φ.galilean s T ξ - φ.galilean s 0 ξ := by
      exact intervalIntegral.integral_deriv_eq_sub
        (fun t _ => (hg.differentiable (by norm_num)) t)
        ((hg.continuous_deriv le_rfl).intervalIntegrable 0 T)
    rw [intervalIntegral.integral_of_le hT] at hFTC
    rw [integral_Ioc_eq_integral_Ioo] at hFTC
    simpa [galilean] using hFTC
  · rw [Ioo_eq_empty (not_lt_of_ge (le_of_not_ge hT))]
    simp

/-- Version multiplied by a constant state, as it appears in the transformed
integrand. -/
lemma integral_Ioo_const_mul_deriv_galilean_time {T : ℝ}
    (φ : TestFunction T) (C s ξ : ℝ) :
    (∫ t in Ioo 0 T, C * deriv (fun τ => φ.galilean s τ ξ) t) = 0 := by
  rw [integral_const_mul]
  rw [φ.integral_Ioo_deriv_galilean_time s ξ]
  simp

/-! ### Galilean integrability (technical `MeasureTheory` certificates) -/

/-- Joint time derivative `∂ₜφ` as a function on `(t, x)`. -/
noncomputable def jointDt {T : ℝ} (φ : TestFunction T) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun q : ℝ × ℝ => φ q.1 q.2) p (1, 0)

/-- Joint space derivative `∂ₓφ` as a function on `(t, x)`. -/
noncomputable def jointDx {T : ℝ} (φ : TestFunction T) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun q : ℝ × ℝ => φ q.1 q.2) p (0, 1)

lemma jointDt_eq {T : ℝ} (φ : TestFunction T) (p : ℝ × ℝ) :
    φ.jointDt p = φ.dt p.1 p.2 := by
  simp only [jointDt, TestFunction.dt]
  exact fderiv_coord_fst φ.toFun p ((φ.smooth.differentiable (by simp)) p)

lemma jointDx_eq {T : ℝ} (φ : TestFunction T) (p : ℝ × ℝ) :
    φ.jointDx p = φ.dx p.1 p.2 := by
  simp only [jointDx, TestFunction.dx]
  exact fderiv_coord_snd φ.toFun p ((φ.smooth.differentiable (by simp)) p)

lemma continuous_jointDt {T : ℝ} (φ : TestFunction T) :
    Continuous φ.jointDt := by
  have h := φ.smooth.continuous_fderiv_apply (by simp)
  have hconst : Continuous fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ)) := continuous_const
  exact (h.comp (continuous_id.prodMk hconst)).congr fun p => by simp [jointDt]

lemma continuous_jointDx {T : ℝ} (φ : TestFunction T) :
    Continuous φ.jointDx := by
  have h := φ.smooth.continuous_fderiv_apply (by simp)
  have hconst : Continuous fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ)) := continuous_const
  exact (h.comp (continuous_id.prodMk hconst)).congr fun p => by simp [jointDx]

private lemma jointDt_eq_zero_of_notMem_tsupport {T : ℝ} (φ : TestFunction T) {p : ℝ × ℝ}
    (hp : p ∉ tsupport (fun q : ℝ × ℝ => φ q.1 q.2)) : φ.jointDt p = 0 := by
  have hf : fderiv ℝ (fun q : ℝ × ℝ => φ q.1 q.2) p = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := fun q : ℝ × ℝ => φ q.1 q.2) (x := p) hp
  simp [jointDt, hf]

private lemma jointDx_eq_zero_of_notMem_tsupport {T : ℝ} (φ : TestFunction T) {p : ℝ × ℝ}
    (hp : p ∉ tsupport (fun q : ℝ × ℝ => φ q.1 q.2)) : φ.jointDx p = 0 := by
  have hf : fderiv ℝ (fun q : ℝ × ℝ => φ q.1 q.2) p = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := fun q : ℝ × ℝ => φ q.1 q.2) (x := p) hp
  simp [jointDx, hf]

private lemma support_jointDt_subset {T : ℝ} (φ : TestFunction T) :
    Function.support φ.jointDt ⊆ tsupport (fun q : ℝ × ℝ => φ q.1 q.2) := by
  intro p hp
  by_contra hmem
  exact hp (φ.jointDt_eq_zero_of_notMem_tsupport hmem)

private lemma support_jointDx_subset {T : ℝ} (φ : TestFunction T) :
    Function.support φ.jointDx ⊆ tsupport (fun q : ℝ × ℝ => φ q.1 q.2) := by
  intro p hp
  by_contra hmem
  exact hp (φ.jointDx_eq_zero_of_notMem_tsupport hmem)

lemma hasCompactSupport_jointDt {T : ℝ} (φ : TestFunction T) :
    HasCompactSupport φ.jointDt :=
  φ.compactSupport.mono' (φ.support_jointDt_subset)

lemma hasCompactSupport_jointDx {T : ℝ} (φ : TestFunction T) :
    HasCompactSupport φ.jointDx :=
  φ.compactSupport.mono' (φ.support_jointDx_subset)

private lemma hasCompactSupport_const_mul_jointDx {T : ℝ} (φ : TestFunction T) (s : ℝ) :
    HasCompactSupport (fun q : ℝ × ℝ => s * φ.jointDx q) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
    exact HasCompactSupport.zero
  · refine HasCompactSupport.mono (φ.hasCompactSupport_jointDx) ?_
    rintro p hp
    simp only [Function.mem_support] at hp ⊢
    exact fun h => hp (by simp [h])

private lemma hasCompactSupport_jointGalileanDeriv {T : ℝ} (φ : TestFunction T) (s : ℝ) :
    HasCompactSupport (fun q : ℝ × ℝ => φ.jointDt q + s * φ.jointDx q) :=
  (φ.hasCompactSupport_jointDt).add (φ.hasCompactSupport_const_mul_jointDx s)

/-- Galilean total time derivative as a joint function on `(t, ξ)`. -/
noncomputable def galileanTimeDeriv {T : ℝ} (φ : TestFunction T) (s : ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun τ => φ.galilean s τ p.2) p.1

lemma galileanTimeDeriv_eq {T : ℝ} (φ : TestFunction T) (s : ℝ) (p : ℝ × ℝ) :
    φ.galileanTimeDeriv s p =
      φ.dt p.1 (p.2 + s * p.1) + s * φ.dx p.1 (p.2 + s * p.1) := by
  simpa [galileanTimeDeriv, galilean] using φ.deriv_galilean_time s p.1 p.2

@[simp] lemma galileanTimeDeriv_uncurry {T : ℝ} (φ : TestFunction T) (s t ξ : ℝ) :
    φ.galileanTimeDeriv s (t, ξ) = deriv (fun τ => φ.galilean s τ ξ) t :=
  rfl

lemma galileanTimeDeriv_eq_joint {T : ℝ} (φ : TestFunction T) (s : ℝ) (p : ℝ × ℝ) :
    φ.galileanTimeDeriv s p =
      (fun q : ℝ × ℝ => φ.jointDt q + s * φ.jointDx q) (galileanHomeo s p) := by
  simp [galileanTimeDeriv_eq, jointDt_eq, jointDx_eq, galileanHomeo]

lemma integrable_galileanTimeDeriv {T : ℝ} (φ : TestFunction T) (s : ℝ) :
    Integrable (φ.galileanTimeDeriv s) := by
  set joint : ℝ × ℝ → ℝ := fun q => φ.jointDt q + s * φ.jointDx q
  have hcont : Continuous joint :=
    φ.continuous_jointDt.add (continuous_const.mul φ.continuous_jointDx)
  have hsupport : HasCompactSupport (joint ∘ (galileanHomeo s)) :=
    (φ.hasCompactSupport_jointGalileanDeriv s).comp_homeomorph (galileanHomeo s)
  have h : Integrable (joint ∘ (galileanHomeo s)) :=
    (hcont.comp (galileanHomeo s).continuous).integrable_of_hasCompactSupport hsupport
  convert h using 1
  funext p
  simpa [joint] using φ.galileanTimeDeriv_eq_joint s p

lemma integrable_smul_dx_galilean {T : ℝ} (φ : TestFunction T) (s c : ℝ) :
    Integrable (fun p : ℝ × ℝ => c * φ.dx p.1 (p.2 + s * p.1)) := by
  set f : ℝ × ℝ → ℝ := (fun q => c * φ.jointDx q) ∘ (galileanHomeo s)
  have hcont : Continuous f :=
    (continuous_const.mul φ.continuous_jointDx).comp (galileanHomeo s).continuous
  have heq :
      (fun p : ℝ × ℝ => c * φ.dx p.1 (p.2 + s * p.1)) = f := by
    funext p
    simp [f, jointDx_eq, galileanHomeo]
  have hsupport : HasCompactSupport f :=
    (φ.hasCompactSupport_const_mul_jointDx c).comp_homeomorph (galileanHomeo s)
  rw [heq]
  exact hcont.integrable_of_hasCompactSupport hsupport

lemma integrableOn_Ioo_Iic_smul_dx_galilean {T : ℝ} (φ : TestFunction T) (s c : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => c * φ.dx p.1 (p.2 + s * p.1)) (Ioo 0 T ×ˢ Iic 0) planeMeasure :=
  integrableOn_plane_of_integrable (φ.integrable_smul_dx_galilean s c)

lemma integrableOn_Ioo_Ioi_smul_dx_galilean {T : ℝ} (φ : TestFunction T) (s c : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => c * φ.dx p.1 (p.2 + s * p.1)) (Ioo 0 T ×ˢ Ioi 0) planeMeasure :=
  integrableOn_plane_of_integrable (φ.integrable_smul_dx_galilean s c)

/-- Fubini + `integral_Ioo_const_mul_deriv_galilean_time` on `Ioo × Iic`. -/
lemma integral_Ioo_Iic_galilean_time_deriv_zero {T : ℝ} (φ : TestFunction T)
    (C s : ℝ) :
    (∫ t in Ioo 0 T, ∫ ξ in Iic 0,
      C * deriv (fun τ => φ.galilean s τ ξ) t) = 0 := by
  set g : ℝ × ℝ → ℝ := fun p => C * φ.galileanTimeDeriv s p
  have hg : IntegrableOn g (Ioo 0 T ×ˢ Iic 0) planeMeasure :=
    integrableOn_plane_of_integrable ((φ.integrable_galileanTimeDeriv s).const_mul C)
  have hf_swap :
      Integrable (Function.uncurry fun t ξ => g (t, ξ))
        ((volume.restrict (Ioo 0 T)).prod (volume.restrict (Iic 0))) := by
    dsimp [IntegrableOn, planeMeasure, Function.uncurry] at hg ⊢
    rw [Measure.prod_restrict]
    exact hg
  calc
    ∫ t in Ioo 0 T, ∫ ξ in Iic 0, C * deriv (fun τ => φ.galilean s τ ξ) t
        = ∫ p in Ioo 0 T ×ˢ Iic 0, g p := by
      simpa [g, galileanTimeDeriv_uncurry] using
        (setIntegral_plane_prod_symm hg).trans setIntegral_plane.symm
    _ = ∫ ξ in Iic 0, ∫ t in Ioo 0 T, g (t, ξ) := by
      trans (∫ t in Ioo 0 T, ∫ ξ in Iic 0, g (t, ξ))
      · rw [setIntegral_plane]
        exact setIntegral_plane_prod hg
      · exact integral_integral_swap (μ := volume.restrict (Ioo 0 T))
          (ν := volume.restrict (Iic 0)) hf_swap
    _ = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun ξ _ => ?_
      simpa [g, galileanTimeDeriv] using φ.integral_Ioo_const_mul_deriv_galilean_time C s ξ

/-- Right (`Ioi`) version of the same Fubini argument. -/
lemma integral_Ioo_Ioi_galilean_time_deriv_zero {T : ℝ} (φ : TestFunction T)
    (C s : ℝ) :
    (∫ t in Ioo 0 T, ∫ ξ in Ioi 0,
      C * deriv (fun τ => φ.galilean s τ ξ) t) = 0 := by
  set g : ℝ × ℝ → ℝ := fun p => C * φ.galileanTimeDeriv s p
  have hg : IntegrableOn g (Ioo 0 T ×ˢ Ioi 0) planeMeasure :=
    integrableOn_plane_of_integrable ((φ.integrable_galileanTimeDeriv s).const_mul C)
  have hf_swap :
      Integrable (Function.uncurry fun t ξ => g (t, ξ))
        ((volume.restrict (Ioo 0 T)).prod (volume.restrict (Ioi 0))) := by
    dsimp [IntegrableOn, planeMeasure, Function.uncurry] at hg ⊢
    rw [Measure.prod_restrict]
    exact hg
  calc
    ∫ t in Ioo 0 T, ∫ ξ in Ioi 0, C * deriv (fun τ => φ.galilean s τ ξ) t
        = ∫ p in Ioo 0 T ×ˢ Ioi 0, g p := by
      simpa [g, galileanTimeDeriv_uncurry] using
        (setIntegral_plane_prod_symm hg).trans setIntegral_plane.symm
    _ = ∫ ξ in Ioi 0, ∫ t in Ioo 0 T, g (t, ξ) := by
      trans (∫ t in Ioo 0 T, ∫ ξ in Ioi 0, g (t, ξ))
      · rw [setIntegral_plane]
        exact setIntegral_plane_prod hg
      · exact integral_integral_swap (μ := volume.restrict (Ioo 0 T))
          (ν := volume.restrict (Ioi 0)) hf_swap
    _ = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun ξ _ => ?_
      simpa [g, galileanTimeDeriv] using φ.integral_Ioo_const_mul_deriv_galilean_time C s ξ

end TestFunction

end ConservationLaw

end


/-!
## Source file: `ConservationLaws/ShockProfile.lean`
-/

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


/-!
## Source file: `ConservationLaws/ShockReduction.lean`
-/

/-!
# Exact reduction of the shock residual to the Rankine–Hugoniot jump

The fundamental theorem of this development: for **any** flux `f : ℝ → ℝ` and
any states and speed, the distributional residual of the travelling step
collapses exactly to the boundary integral of the Rankine–Hugoniot deficit along
the moving interface,

  `weakResidual f (shockProfile uL uR s) φ
     = ∫_{(0,T)} ((f uL - f uR) - s (uL - uR)) · φ (t, s t) dt`.

In particular the step is a weak solution **iff** its speed satisfies the
Rankine–Hugoniot condition — with no hypotheses whatsoever on the flux, which
only ever enters through the two constants `f uL` and `f uR`.

The proof proceeds in three phases:

1. *Static domain* (spatial shifts): the translation `x = ξ + s t` converts the
   moving half-lines into `(-∞, 0]` and `(0, ∞)`, with translation invariance of
   Lebesgue measure.
2. *Analytic evaluation and Fubini*: on each half, the Galilean total-time
   derivative integrates to zero (`ConservationLaws.Galilean`) and only the
   `∂ₓφ` term survives, evaluated by the improper FTC boundary formulas.
3. *Assembly*: the spatial split of `ConservationLaws.ShockProfile`, additivity
   of the time marginals, and the two half-plane collapses.

## Main results

- `ConservationLaw.shock_integral_left`, `ConservationLaw.shock_integral_right`:
  each half of the double integral collapses to a boundary term.
- `ConservationLaw.hasShockIntegralReduction`: the reduction holds for all
  parameters (the fundamental theorem).
- `ConservationLaw.isWeakSolution_shockProfile_of_rankineHugoniot`: the
  unconditional packaging — a Rankine–Hugoniot step is a weak solution.

## Tags

shock wave, Rankine-Hugoniot, Fubini, conservation law, weak solution
-/

open MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ConservationLaw

/-! ### Phase 1: static domain via spatial shifts -/

/-- Spatial translation `x = ξ + c`: converts `Iic c` into `Iic 0`. -/
private lemma integral_Iic_shift (c : ℝ) {f : ℝ → ℝ} :
    (∫ x in Iic c, f x) = ∫ ξ in Iic 0, f (ξ + c) := by
  let e := (Homeomorph.addRight c)
  have he := e.isClosedEmbedding.measurableEmbedding
  have hμ : volume = Measure.map e volume := by
    simpa only [e, Homeomorph.coe_addRight] using (map_add_right_eq_self volume c).symm
  have hpre :
      ∫ ξ in Iic 0, f (ξ + c) = ∫ ξ in e ⁻¹' Iic c, f (e ξ) := by
    simp only [e, Homeomorph.coe_addRight, preimage_add_const_Iic, sub_self]
  calc
    ∫ x in Iic c, f x
        = ∫ x in Iic c, f x ∂(Measure.map e volume) :=
      congr_arg (fun μ => ∫ x in Iic c, f x ∂μ) hμ
    _ = ∫ ξ in e ⁻¹' Iic c, f (e ξ) := he.setIntegral_map (μ := volume) f (Iic c)
    _ = ∫ ξ in Iic 0, f (ξ + c) := hpre.symm

/-- Spatial translation `x = ξ + c`: converts `Ioi c` into `Ioi 0`. -/
private lemma integral_Ioi_shift (c : ℝ) {f : ℝ → ℝ} :
    (∫ x in Ioi c, f x) = ∫ ξ in Ioi 0, f (ξ + c) := by
  let e := (Homeomorph.addRight c)
  have he := e.isClosedEmbedding.measurableEmbedding
  have hμ : volume = Measure.map e volume := by
    simpa only [e, Homeomorph.coe_addRight] using (map_add_right_eq_self volume c).symm
  have hpre :
      ∫ ξ in Ioi 0, f (ξ + c) = ∫ ξ in e ⁻¹' Ioi c, f (e ξ) := by
    simp only [e, Homeomorph.coe_addRight, preimage_add_const_Ioi, sub_self]
  calc
    ∫ x in Ioi c, f x
        = ∫ x in Ioi c, f x ∂(Measure.map e volume) :=
      congr_arg (fun μ => ∫ x in Ioi c, f x ∂μ) hμ
    _ = ∫ ξ in e ⁻¹' Ioi c, f (e ξ) := he.setIntegral_map (μ := volume) f (Ioi c)
    _ = ∫ ξ in Ioi 0, f (ξ + c) := hpre.symm

lemma integral_Iic_shift_weakIntegrand {f : ℝ → ℝ} {T : ℝ}
    (φ : TestFunction T) (uL s t : ℝ) :
    (∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) =
    ∫ ξ in Iic 0, weakIntegrand f (fun _ _ => uL) φ t (ξ + s * t) :=
  integral_Iic_shift (s * t)

lemma integral_Ioi_shift_weakIntegrand {f : ℝ → ℝ} {T : ℝ}
    (φ : TestFunction T) (uR s t : ℝ) :
    (∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) =
    ∫ ξ in Ioi 0, weakIntegrand f (fun _ _ => uR) φ t (ξ + s * t) :=
  integral_Ioi_shift (s * t)

/-- Time marginal: the spatial integral over the moving left domain is
integrable in `t`. -/
private lemma integrableOn_time_weakIntegrand_Iic {f : ℝ → ℝ} {T : ℝ}
    (φ : TestFunction T) (uL s : ℝ) :
    IntegrableOn
      (fun t => ∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) (Ioo 0 T) := by
  set G : ℝ × ℝ → ℝ := fun p => weakIntegrand f (fun _ _ => uL) φ p.1 (p.2 + s * p.1)
  have hf₁₂ : IntegrableOn
      (fun p => uL * φ.galileanTimeDeriv s p + (f uL - s * uL) * φ.dx p.1 (p.2 + s * p.1))
      (Ioo 0 T ×ˢ Iic 0) planeMeasure :=
    (integrableOn_plane_of_integrable ((φ.integrable_galileanTimeDeriv s).const_mul uL)).add
      (φ.integrableOn_Ioo_Iic_smul_dx_galilean s (f uL - s * uL))
  have hG_eq : G = fun p =>
      uL * φ.galileanTimeDeriv s p + (f uL - s * uL) * φ.dx p.1 (p.2 + s * p.1) := by
    funext p
    simp only [G]
    exact φ.constant_state_galilean uL (f uL) s p.1 p.2
  have hG : IntegrableOn G (Ioo 0 T ×ˢ Iic 0) planeMeasure := hG_eq ▸ hf₁₂
  have hG_int : Integrable G ((volume.restrict (Ioo 0 T)).prod (volume.restrict (Iic 0))) := by
    dsimp [IntegrableOn, planeMeasure] at hG
    convert hG using 2
    rw [Measure.prod_restrict]
  have hmarg := Integrable.integral_prod_left (E := ℝ) hG_int
  have hfun :
      (fun t => ∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) =
        fun t => ∫ ξ in Iic 0, G (t, ξ) := by
    funext t
    simp only [G]
    exact integral_Iic_shift_weakIntegrand φ uL s t
  simpa [IntegrableOn, hfun] using hmarg

private lemma integrableOn_time_weakIntegrand_Ioi {f : ℝ → ℝ} {T : ℝ}
    (φ : TestFunction T) (uR s : ℝ) :
    IntegrableOn
      (fun t => ∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) (Ioo 0 T) := by
  set G : ℝ × ℝ → ℝ := fun p => weakIntegrand f (fun _ _ => uR) φ p.1 (p.2 + s * p.1)
  have hf₁₂ : IntegrableOn
      (fun p => uR * φ.galileanTimeDeriv s p + (f uR - s * uR) * φ.dx p.1 (p.2 + s * p.1))
      (Ioo 0 T ×ˢ Ioi 0) planeMeasure :=
    (integrableOn_plane_of_integrable ((φ.integrable_galileanTimeDeriv s).const_mul uR)).add
      (φ.integrableOn_Ioo_Ioi_smul_dx_galilean s (f uR - s * uR))
  have hG_eq : G = fun p =>
      uR * φ.galileanTimeDeriv s p + (f uR - s * uR) * φ.dx p.1 (p.2 + s * p.1) := by
    funext p
    simp only [G]
    exact φ.constant_state_galilean uR (f uR) s p.1 p.2
  have hG : IntegrableOn G (Ioo 0 T ×ˢ Ioi 0) planeMeasure := hG_eq ▸ hf₁₂
  have hG_int : Integrable G ((volume.restrict (Ioo 0 T)).prod (volume.restrict (Ioi 0))) := by
    dsimp [IntegrableOn, planeMeasure] at hG
    convert hG using 2
    rw [Measure.prod_restrict]
  have hmarg := Integrable.integral_prod_left (E := ℝ) hG_int
  have hfun :
      (fun t => ∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) =
        fun t => ∫ ξ in Ioi 0, G (t, ξ) := by
    funext t
    simp only [G]
    exact integral_Ioi_shift_weakIntegrand φ uR s t
  simpa [IntegrableOn, hfun] using hmarg

/-- Boundary formula on the shifted left half-line. -/
private lemma integral_Iic_shift_dx {T : ℝ} (φ : TestFunction T) (s t : ℝ) :
    (∫ ξ in Iic 0, φ.dx t (ξ + s * t)) = φ t (s * t) := by
  calc
    ∫ ξ in Iic 0, φ.dx t (ξ + s * t)
        = ∫ x in Iic (s * t), φ.dx t x := (integral_Iic_shift (s * t)).symm
    _ = φ t (s * t) := φ.integral_Iic_dx t (s * t)

/-- Boundary formula on the shifted right half-line. -/
private lemma integral_Ioi_shift_dx {T : ℝ} (φ : TestFunction T) (s t : ℝ) :
    (∫ ξ in Ioi 0, φ.dx t (ξ + s * t)) = -φ t (s * t) := by
  calc
    ∫ ξ in Ioi 0, φ.dx t (ξ + s * t)
        = ∫ x in Ioi (s * t), φ.dx t x := (integral_Ioi_shift (s * t)).symm
    _ = -φ t (s * t) := φ.integral_Ioi_dx t (s * t)

/-- The interface boundary function `t ↦ c · φ (t, s t)` has compact support. -/
private lemma hasCompactSupport_shock_boundary {T : ℝ} (φ : TestFunction T) (c s : ℝ) :
    HasCompactSupport (fun t => c * φ t (s * t)) := by
  by_cases hc : c = 0
  · subst hc
    simp
    exact HasCompactSupport.zero
  · let K := Prod.fst '' tsupport (fun p : ℝ × ℝ => φ p.1 p.2)
    refine HasCompactSupport.intro (φ.compactSupport.image continuous_fst) ?_
    intro t ht
    by_contra hφ
    have hpTSupport : (t, s * t) ∈ tsupport (fun p : ℝ × ℝ => φ p.1 p.2) := by
      have hpSupport : (t, s * t) ∈ Function.support (fun p : ℝ × ℝ => φ p.1 p.2) := by
        simpa [Function.mem_support, hc] using hφ
      exact subset_closure hpSupport
    exact ht ⟨(t, s * t), hpTSupport, rfl⟩

private lemma integrableOn_shock_boundary {T : ℝ} (φ : TestFunction T) (c s : ℝ) :
    IntegrableOn (fun t => c * φ t (s * t)) (Ioo 0 T) := by
  have hcurve : Continuous fun t : ℝ => (t, s * t) :=
    continuous_id.prodMk (continuous_const.mul continuous_id)
  have hcont : Continuous (fun t => c * φ t (s * t)) :=
    continuous_const.mul (φ.smooth.continuous.comp hcurve)
  exact hcont.integrable_of_hasCompactSupport (hasCompactSupport_shock_boundary φ c s) |>.integrableOn

/-! ### Phase 2: analytic evaluation and Fubini -/

/-- The time integral of the left half collapses to the boundary term. -/
lemma shock_integral_left {f : ℝ → ℝ} {T : ℝ} (φ : TestFunction T) (uL s : ℝ) :
    (∫ t in Ioo 0 T, ∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) =
    ∫ t in Ioo 0 T, (f uL - s * uL) * φ t (s * t) := by
  set f₁ : ℝ × ℝ → ℝ := fun p => uL * φ.galileanTimeDeriv s p
  set f₂ : ℝ × ℝ → ℝ := fun p => (f uL - s * uL) * φ.dx p.1 (p.2 + s * p.1)
  have hf₁ : IntegrableOn f₁ (Ioo 0 T ×ˢ Iic 0) planeMeasure := by
    simpa [f₁] using integrableOn_plane_of_integrable
      ((φ.integrable_galileanTimeDeriv s).const_mul uL)
  have hf₂ : IntegrableOn f₂ (Ioo 0 T ×ˢ Iic 0) planeMeasure :=
    φ.integrableOn_Ioo_Iic_smul_dx_galilean s (f uL - s * uL)
  have hf₁₂ : IntegrableOn (f₁ + f₂) (Ioo 0 T ×ˢ Iic 0) planeMeasure := hf₁.add hf₂
  calc
    (∫ t in Ioo 0 T, ∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x)
        = ∫ t in Ioo 0 T, ∫ ξ in Iic 0, weakIntegrand f (fun _ _ => uL) φ t (ξ + s * t) := by
      congr 1
      funext t
      exact integral_Iic_shift_weakIntegrand φ uL s t
    _ = ∫ t in Ioo 0 T, ∫ ξ in Iic 0, f₁ (t, ξ) + f₂ (t, ξ) := by
      congr 1
      funext t
      congr 1
      funext ξ
      simp only [f₁, f₂, TestFunction.galileanTimeDeriv]
      exact φ.constant_state_galilean uL (f uL) s t ξ
    _ = ∫ p in Ioo 0 T ×ˢ Iic 0, f₁ p + f₂ p := by
      rw [setIntegral_plane]
      exact (setIntegral_plane_prod hf₁₂).symm
    _ = (∫ p in Ioo 0 T ×ˢ Iic 0, f₁ p) + (∫ p in Ioo 0 T ×ˢ Iic 0, f₂ p) :=
      integral_add hf₁ hf₂
    _ = ∫ p in Ioo 0 T ×ˢ Iic 0, f₂ p := by
      have h₁ : ∫ p in Ioo 0 T ×ˢ Iic 0, f₁ p = 0 := by
        rw [setIntegral_plane]
        refine (setIntegral_plane_prod hf₁).trans ?_
        simpa [f₁, TestFunction.galileanTimeDeriv_uncurry] using
          φ.integral_Ioo_Iic_galilean_time_deriv_zero uL s
      rw [h₁, zero_add]
    _ = ∫ t in Ioo 0 T, ∫ ξ in Iic 0, f₂ (t, ξ) := by
      rw [setIntegral_plane]
      exact setIntegral_plane_prod hf₂
    _ = ∫ t in Ioo 0 T, (f uL - s * uL) * φ t (s * t) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      rw [integral_const_mul]
      congr 1
      exact integral_Iic_shift_dx φ s t

/-- The right-half integral collapses to the boundary term with opposite sign. -/
lemma shock_integral_right {f : ℝ → ℝ} {T : ℝ} (φ : TestFunction T) (uR s : ℝ) :
    (∫ t in Ioo 0 T, ∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) =
    - ∫ t in Ioo 0 T, (f uR - s * uR) * φ t (s * t) := by
  set f₁ : ℝ × ℝ → ℝ := fun p => uR * φ.galileanTimeDeriv s p
  set f₂ : ℝ × ℝ → ℝ := fun p => (f uR - s * uR) * φ.dx p.1 (p.2 + s * p.1)
  have hf₁ : IntegrableOn f₁ (Ioo 0 T ×ˢ Ioi 0) planeMeasure := by
    simpa [f₁] using integrableOn_plane_of_integrable
      ((φ.integrable_galileanTimeDeriv s).const_mul uR)
  have hf₂ : IntegrableOn f₂ (Ioo 0 T ×ˢ Ioi 0) planeMeasure :=
    φ.integrableOn_Ioo_Ioi_smul_dx_galilean s (f uR - s * uR)
  have hf₁₂ : IntegrableOn (f₁ + f₂) (Ioo 0 T ×ˢ Ioi 0) planeMeasure := hf₁.add hf₂
  calc
    (∫ t in Ioo 0 T, ∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x)
        = ∫ t in Ioo 0 T, ∫ ξ in Ioi 0, weakIntegrand f (fun _ _ => uR) φ t (ξ + s * t) := by
      congr 1
      funext t
      exact integral_Ioi_shift_weakIntegrand φ uR s t
    _ = ∫ t in Ioo 0 T, ∫ ξ in Ioi 0, f₁ (t, ξ) + f₂ (t, ξ) := by
      congr 1
      funext t
      congr 1
      funext ξ
      simp only [f₁, f₂, TestFunction.galileanTimeDeriv]
      exact φ.constant_state_galilean uR (f uR) s t ξ
    _ = ∫ p in Ioo 0 T ×ˢ Ioi 0, f₁ p + f₂ p := by
      rw [setIntegral_plane]
      exact (setIntegral_plane_prod hf₁₂).symm
    _ = (∫ p in Ioo 0 T ×ˢ Ioi 0, f₁ p) + (∫ p in Ioo 0 T ×ˢ Ioi 0, f₂ p) :=
      integral_add hf₁ hf₂
    _ = ∫ p in Ioo 0 T ×ˢ Ioi 0, f₂ p := by
      have h₁ : ∫ p in Ioo 0 T ×ˢ Ioi 0, f₁ p = 0 := by
        rw [setIntegral_plane]
        refine (setIntegral_plane_prod hf₁).trans ?_
        simpa [f₁, TestFunction.galileanTimeDeriv_uncurry] using
          φ.integral_Ioo_Ioi_galilean_time_deriv_zero uR s
      rw [h₁, zero_add]
    _ = ∫ t in Ioo 0 T, ∫ ξ in Ioi 0, f₂ (t, ξ) := by
      rw [setIntegral_plane]
      exact setIntegral_plane_prod hf₂
    _ = - ∫ t in Ioo 0 T, (f uR - s * uR) * φ t (s * t) := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      calc
        ∫ ξ in Ioi 0, (f uR - s * uR) * φ.dx t (ξ + s * t)
            = (f uR - s * uR) * ∫ ξ in Ioi 0, φ.dx t (ξ + s * t) := by
              rw [integral_const_mul]
        _ = (f uR - s * uR) * (-φ t (s * t)) := by
              rw [integral_Ioi_shift_dx φ s t]
        _ = -((f uR - s * uR) * φ t (s * t)) := by
              ring

/-! ### Phase 3: assembly -/

/-- **Fundamental theorem.**  For any flux, the residual of the travelling step
collapses to the Rankine–Hugoniot jump along the moving interface. -/
theorem hasShockIntegralReduction (f : ℝ → ℝ) (T uL uR s : ℝ) :
    HasShockIntegralReduction f T uL uR s := by
  intro φ
  dsimp only [HasShockIntegralReduction, weakResidual]
  calc
    (∫ t in Ioo 0 T, ∫ x, weakIntegrand f (shockProfile uL uR s) φ t x)
        = ∫ t in Ioo 0 T, ((∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) +
            (∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x)) := by
      congr 1
      funext t
      exact integral_spatial_split φ uL uR s t
    _ = (∫ t in Ioo 0 T, ∫ x in Iic (s * t), weakIntegrand f (fun _ _ => uL) φ t x) +
        (∫ t in Ioo 0 T, ∫ x in Ioi (s * t), weakIntegrand f (fun _ _ => uR) φ t x) := by
      exact integral_add (integrableOn_time_weakIntegrand_Iic φ uL s)
        (integrableOn_time_weakIntegrand_Ioi φ uR s)
    _ = (∫ t in Ioo 0 T, (f uL - s * uL) * φ t (s * t)) -
        (∫ t in Ioo 0 T, (f uR - s * uR) * φ t (s * t)) := by
      rw [shock_integral_left, shock_integral_right]
      simp [sub_eq_add_neg]
    _ = ∫ t in Ioo 0 T, ((f uL - f uR) - s * (uL - uR)) * φ t (s * t) := by
      rw [← integral_sub
        (integrableOn_shock_boundary φ (f uL - s * uL) s)
        (integrableOn_shock_boundary φ (f uR - s * uR) s)]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      ring

/-- **Unconditional packaging.**  A travelling step whose speed satisfies the
Rankine–Hugoniot condition is a weak solution of the conservation law, for any
flux. -/
theorem isWeakSolution_shockProfile_of_rankineHugoniot {f : ℝ → ℝ}
    (T uL uR s : ℝ) (hRH : RankineHugoniot f uL uR s) :
    IsWeakSolution f T (shockProfile uL uR s) :=
  isWeakSolution_shockProfile T uL uR s
    (hasShockIntegralReduction f T uL uR s) hRH

end ConservationLaw

end


/-!
## Source file: `ConservationLaws/Burgers.lean`
-/

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
