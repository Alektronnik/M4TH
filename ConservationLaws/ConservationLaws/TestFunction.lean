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
