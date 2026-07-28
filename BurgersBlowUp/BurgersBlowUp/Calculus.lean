/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-!
# Multivariable calculus lemmas for the method of characteristics

Decomposition of the Fréchet derivative of a curried function of two real
variables into its two partial derivatives, together with the derivative of a
curve into the product `ℝ × ℝ`.  These are the calculus ingredients of the
chain rule along characteristic curves used by the blow-up argument.

## Main results

- `Burgers.hasDerivAt_prodMk`: derivative of `t ↦ (f t, g t)`.
- `Burgers.fderiv_coord_fst`, `Burgers.fderiv_coord_snd`: the Fréchet
  derivative evaluated at `(1, 0)` and `(0, 1)` recovers the two partial
  derivatives.
- `Burgers.fderiv_apply_decomp`: linear decomposition
  `Df (v) = v₁ ∂ₜ f + v₂ ∂ₓ f`.

## Implementation notes

This package is self-contained by design: these four lemmas coincide, statement
for statement, with `ConservationLaw.hasDerivAt_prodMk`,
`ConservationLaw.fderiv_coord_fst`, `ConservationLaw.fderiv_coord_snd` and
`ConservationLaw.fderiv_apply_decomp` of the sibling `ConservationLaws`
package.  At Mathlib-contribution time they are submitted **once** (a single
shared PR that both PR series depend on); close relatives may also already
exist in Mathlib and should be deduplicated at review.

## Tags

Frechet derivative, partial derivative, chain rule
-/

@[expose] public section

namespace Burgers

/-- Derivative of a function with values in the product. -/
lemma hasDerivAt_prodMk {f : ℝ → ℝ} {g : ℝ → ℝ} {f' g' : ℝ} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => (f t, g t)) (f', g') s := by
  have h_prod := (hf.hasFDerivAt.prodMk hg.hasFDerivAt).hasDerivAt
  have h_deriv_eq : (((ContinuousLinearMap.toSpanSingleton ℝ f').prod
      (ContinuousLinearMap.toSpanSingleton ℝ g')) 1) = (f', g') := by
    ext <;> simp
  rw [← h_deriv_eq]
  exact h_prod

/-- Partial derivative with respect to the first coordinate. -/
lemma fderiv_coord_fst (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
    (h_diff : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) p) :
    fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) p (1, 0) = deriv (fun t => u t p.2) p.1 := by
  let f := fun p' : ℝ × ℝ => u p'.1 p'.2
  let γ := fun t : ℝ => (t, p.2)
  -- Analytic derivative of the slicing line `γ (t)`.
  have h_γ_deriv : HasDerivAt γ (1, 0) p.1 := by
    have hd1 : HasDerivAt (fun t => t) 1 p.1 := hasDerivAt_id p.1
    have hd2 : HasDerivAt (fun _ => p.2) 0 p.1 := hasDerivAt_const p.1 p.2
    exact hasDerivAt_prodMk hd1 hd2
  -- The line passes through `p`.
  have hp : γ p.1 = p := Prod.ext rfl rfl
  -- The Fréchet derivative of `u`, evaluated exactly at `p`.
  have h_f_fderiv : HasFDerivAt f (fderiv ℝ f p) (γ p.1) := by
    rw [hp]
    exact h_diff.hasFDerivAt
  -- Compose Fréchet (2D) with `HasDerivAt` (1D).
  have h_comp := h_f_fderiv.comp_hasDerivAt p.1 h_γ_deriv
  exact h_comp.deriv.symm

/-- Partial derivative with respect to the second coordinate. -/
lemma fderiv_coord_snd (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
    (h_diff : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) p) :
    fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) p (0, 1) = deriv (u p.1) p.2 := by
  let f := fun p' : ℝ × ℝ => u p'.1 p'.2
  let γ := fun t : ℝ => (p.1, t)
  have h_γ_deriv : HasDerivAt γ (0, 1) p.2 := by
    have hd1 : HasDerivAt (fun _ => p.1) 0 p.2 := hasDerivAt_const p.2 p.1
    have hd2 : HasDerivAt (fun t => t) 1 p.2 := hasDerivAt_id p.2
    exact hasDerivAt_prodMk hd1 hd2
  have hp : γ p.2 = p := Prod.ext rfl rfl
  have h_f_fderiv : HasFDerivAt f (fderiv ℝ f p) (γ p.2) := by
    rw [hp]
    exact h_diff.hasFDerivAt
  have h_comp := h_f_fderiv.comp_hasDerivAt p.2 h_γ_deriv
  exact h_comp.deriv.symm

/-- Linear decomposition of the Fréchet derivative into partial derivatives. -/
lemma fderiv_apply_decomp (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (dp : ℝ × ℝ)
    (h_diff : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) p) :
    fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) p dp =
      dp.1 * deriv (fun t => u t p.2) p.1 + dp.2 * deriv (u p.1) p.2 := by
  let L := fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) p
  have h_dp_decomp : dp = dp.1 • (1, 0) + dp.2 • (0, 1) := by
    ext <;> simp
  have h1 : L dp = dp.1 • L (1, 0) + dp.2 • L (0, 1) := by
    rw [h_dp_decomp]
    rw [map_add, map_smul, map_smul]
    dsimp
    ring
  rw [h1]
  rw [fderiv_coord_fst u p h_diff, fderiv_coord_snd u p h_diff]
  rfl

end Burgers

end
