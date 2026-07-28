/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import BurgersBlowUp.ODE

/-!
# Classical solutions of the Burgers equation and the method of characteristics

The classical (`C²`) solution concept for the inviscid Burgers equation
`∂ₜ u + u ∂ₓ u = 0` on `[0, T) × ℝ`, and the method of characteristics for the
compressive linear initial datum `u₀ (x) = -x`, whose characteristics are the
straight lines `t ↦ x₀ (1 - t)`, all focusing at the point `(1, 0)`.

The key structural results are that the solution is constant along these lines
(`constant_along_characteristic`, proved through the linear ODE uniqueness
lemma), and the spatially differentiated PDE
`∂ₜ u_x + (u_x) ^ 2 + u ∂ₓ u_x = 0` (`pde_spatial_deriv`), which feeds the
Riccati evolution of the gradient in `BurgersBlowUp.BlowUp`.

## Main definitions

- `Burgers.IsRegularSolution`: the `C²` solution predicate,
  with joint differentiability, the PDE on `[0, T)`, differentiability of the
  gradient, equality of second mixed derivatives (Schwarz), and a global
  gradient bound.
- `Burgers.initialRamp`: the compressive datum `u₀ (x) = -x`.

## Main results

- `Burgers.hasDerivAt_along_line`: total derivative of a
  solution along the line `t ↦ x₀ (1 - t)` (any initial datum).
- `Burgers.constant_along_characteristic`:
  `u (t, x₀ (1 - t)) = -x₀` for the ramp datum.
- `Burgers.pde_spatial_deriv`: the spatially differentiated
  PDE (any initial datum).

## Implementation notes

The lemmas whose proofs never inspect the initial condition
(`hasDerivAt_along_line`, `differentiableAt_slice`,
`differentiableAt_timeDeriv_slice`, `pde_spatial_deriv`) are stated for an
arbitrary datum `u₀`; only the constancy result is specific to `initialRamp`.
The generalisation of the whole development to an arbitrary compressive datum
(`deriv u₀ x₀ < 0`, critical time `-1 / deriv u₀ x₀`, curved characteristics
`x₀ + u₀ (x₀) t`) follows the same Lyapunov/Riccati strategy and is planned as
follow-up work once compilation is set up.

## Tags

Burgers equation, method of characteristics, classical solution
-/

open Set

@[expose] public section

namespace Burgers

/--
Rigorous (`C²`-type) regular solution concept for one-dimensional Burgers with
initial datum `u₀` on the time interval `[0, T)`.
-/
structure IsRegularSolution (u₀ : ℝ → ℝ) (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  /-- The initial condition. -/
  initial : ∀ x, u 0 x = u₀ x
  /-- Joint differentiability in `(t, x)`. -/
  differentiable : Differentiable ℝ (fun p : ℝ × ℝ => u p.1 p.2)
  /-- The partial differential equation on `[0, T)`. -/
  pde : ∀ t ∈ Set.Ico 0 T, ∀ x,
    deriv (fun s => u s x) t + u t x * deriv (u t) x = 0
  /-- First-order spatial smoothness of the gradient on each time slice. -/
  gradient_differentiable_slice : ∀ t ∈ Set.Icc 0 T,
    Differentiable ℝ (fun x => deriv (u t) x)
  /-- Equality of second mixed derivatives (Schwarz/Clairaut condition). -/
  schwarz : ∀ t ∈ Set.Ico 0 T, ∀ x,
    deriv (fun t' => deriv (u t') x) t = deriv (fun x' => deriv (fun s => u s x') t) x
  /-- Joint differentiability of the gradient (`C²` solution). -/
  gradient_differentiable : Differentiable ℝ (fun p' : ℝ × ℝ => deriv (u p'.1) p'.2)
  /-- Global bound on the gradient. -/
  gradient_bounded : ∃ M : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x, |deriv (u t) x| ≤ M

/-- The compressive linear initial datum `u₀ (x) = -x`. -/
def initialRamp (x : ℝ) : ℝ := -x

/-- Total derivative (chain rule) of a solution along the line
`t ↦ x₀ (1 - t)`, shifted by `x₀`, rewritten through the PDE.  Valid for any
initial datum: only the PDE and joint differentiability are used. -/
lemma hasDerivAt_along_line {u₀ : ℝ → ℝ} {T : ℝ} {u : ℝ → ℝ → ℝ}
    (hsol : IsRegularSolution u₀ T u) (x₀ : ℝ) :
    ∀ s ∈ Set.Ico 0 T,
      HasDerivAt (fun t => u t (x₀ * (1 - t)) + x₀)
        (- (u s (x₀ * (1 - s)) + x₀) * deriv (u s) (x₀ * (1 - s)))
        s := by
  intro s hs
  -- The characteristic curve in the plane: `γ (t) = (t, x₀ (1 - t))`.
  let γ := fun t => (t, x₀ * (1 - t))
  -- Its velocity is `(1, -x₀)`.
  have h_deriv_γ : HasDerivAt γ (1, -x₀) s := by
    have h1 : HasDerivAt (fun t => t) 1 s := hasDerivAt_id s
    have h2 : HasDerivAt (fun t => x₀ * (1 - t)) (-x₀) s := by
      have hd : HasDerivAt (fun t => 1 - t) (-1) s := by
        have h_const := hasDerivAt_const s (1 : ℝ)
        have h_id := hasDerivAt_id s
        have h_sub := h_const.sub h_id
        change HasDerivAt (fun t => 1 - t) (0 - 1) s at h_sub
        have h_deriv_eq : 0 - 1 = (-1 : ℝ) := by ring
        rw [h_deriv_eq] at h_sub
        exact h_sub
      have h_mul := hd.const_mul x₀
      have h_deriv_eq : x₀ * -1 = -x₀ := by ring
      rw [← h_deriv_eq]
      exact h_mul
    exact hasDerivAt_prodMk h1 h2
  -- Chain rule along the curve.
  have h_chain := hasDerivAt_comp_curve u γ s (1, -x₀) h_deriv_γ (hsol.differentiable (γ s))
  have h_chain_add := h_chain.add_const x₀
  -- Rewrite the time derivative through the PDE.
  have h_pde_val := hsol.pde s hs (x₀ * (1 - s))
  have h_deriv_t : deriv (fun t' => u t' (x₀ * (1 - s))) s =
      - u s (x₀ * (1 - s)) * deriv (u s) (x₀ * (1 - s)) := by
    linarith [h_pde_val]
  change HasDerivAt (fun t => u t (x₀ * (1 - t)) + x₀)
    (1 * deriv (fun t' => u t' (x₀ * (1 - s))) s +
      -x₀ * deriv (u s) (x₀ * (1 - s))) s at h_chain_add
  have h_deriv_eq : 1 * deriv (fun t' => u t' (x₀ * (1 - s))) s +
      -x₀ * deriv (u s) (x₀ * (1 - s)) =
        - (u s (x₀ * (1 - s)) + x₀) * deriv (u s) (x₀ * (1 - s)) := by
    rw [h_deriv_t]
    ring
  rw [← h_deriv_eq]
  exact h_chain_add

/-- For the ramp datum, the solution is constant along the characteristic:
`u (t, x₀ (1 - t)) = -x₀`.  Proof: `Y (s) = u (s, x₀ (1 - s)) + x₀` starts at
zero and satisfies the linear ODE `Y' = -Y · u_x`, hence vanishes by
`linear_ode_uniqueness`. -/
lemma constant_along_characteristic {T : ℝ} {u : ℝ → ℝ → ℝ}
    (hsol : IsRegularSolution initialRamp T u)
    (x₀ : ℝ) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    u t (x₀ * (1 - t)) = -x₀ := by
  let Y := fun s => u s (x₀ * (1 - s)) + x₀
  have hY0 : Y 0 = 0 := by
    dsimp [Y]
    rw [hsol.initial]
    unfold initialRamp
    ring
  -- The analytic chain rule via `HasDerivAt`.
  have hY_deriv : ∀ s ∈ Set.Ico 0 T, HasDerivAt Y (- Y s * deriv (u s) (x₀ * (1 - s))) s := by
    exact hasDerivAt_along_line hsol x₀
  -- Global gradient bound of the regular solution.
  obtain ⟨M, hM⟩ := hsol.gradient_bounded
  have h_bound : ∀ s ∈ Set.Icc 0 T, |deriv (u s) (x₀ * (1 - s))| ≤ M := by
    intro s hs
    exact hM s hs (x₀ * (1 - s))
  -- Continuity of `Y`.
  have hY_cont : ContinuousOn Y (Set.Icc 0 T) := by
    have hu_cont : Continuous (fun p : ℝ × ℝ => u p.1 p.2) := hsol.differentiable.continuous
    have h_γ_cont : Continuous (fun s => (s, x₀ * (1 - s))) := by fun_prop
    have h_comp : Continuous Y := by
      have : Y = (fun s => u s (x₀ * (1 - s)) + x₀) := rfl
      rw [this]
      fun_prop
    exact h_comp.continuousOn
  -- Linear ODE uniqueness.
  have hY_zero : ∀ s ∈ Set.Icc 0 T, Y s = 0 := by
    apply linear_ode_uniqueness Y (fun s => deriv (u s) (x₀ * (1 - s))) T M
      hY_cont h_bound hY0 hY_deriv
  have h_final : Y t = 0 := hY_zero t ht
  linarith

/-- The solution is differentiable in `x` for each time (strict consequence of
joint differentiability). -/
lemma differentiableAt_slice {u₀ : ℝ → ℝ} {T : ℝ} {u : ℝ → ℝ → ℝ}
    (hsol : IsRegularSolution u₀ T u) (t : ℝ) (x : ℝ) :
    DifferentiableAt ℝ (u t) x := by
  have h_joint : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (t, x) :=
    hsol.differentiable (t, x)
  fun_prop

/-- The velocity `u_t` is differentiable in `x`, thanks to the PDE itself:
`u_t = -u · u_x` is a product of differentiable functions. -/
lemma differentiableAt_timeDeriv_slice {u₀ : ℝ → ℝ} {T : ℝ} {u : ℝ → ℝ → ℝ}
    (hsol : IsRegularSolution u₀ T u) (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : ℝ) :
    DifferentiableAt ℝ (fun x' => deriv (fun s => u s x') t) x := by
  -- Extract `u_t` explicitly from the PDE: `u_t = -u · u_x`.
  have h_ut_eq : (fun x' => deriv (fun s => u s x') t) =
      fun x' => - u t x' * deriv (u t) x' := by
    ext x'
    have h_pde := hsol.pde t ht x'
    linarith
  rw [h_ut_eq]
  have hd_u : DifferentiableAt ℝ (u t) x := differentiableAt_slice hsol t x
  have ht_Icc : t ∈ Set.Icc 0 T := ⟨ht.1, le_of_lt ht.2⟩
  have hd_ux : DifferentiableAt ℝ (fun x' => deriv (u t) x') x :=
    hsol.gradient_differentiable_slice t ht_Icc x
  fun_prop

/-- **Spatially differentiated Burgers equation.**  Differentiating the PDE in
`x` with the sum and product rules yields
`∂ₜ u_x + (u_x) ^ 2 + u ∂ₓ u_x = 0`.  Valid for any initial datum. -/
lemma pde_spatial_deriv {u₀ : ℝ → ℝ} {T : ℝ} {u : ℝ → ℝ → ℝ}
    (hsol : IsRegularSolution u₀ T u) (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : ℝ) :
    deriv (fun x' => deriv (fun s => u s x') t) x + (deriv (u t) x) ^ 2 +
      u t x * deriv (fun x' => deriv (u t) x') x = 0 := by
  -- The PDE is identically zero as a function of `x'`.
  have h_pde_func : (fun x' => deriv (fun s => u s x') t + u t x' * deriv (u t) x') =
      (fun _ => (0 : ℝ)) := by
    ext x'; exact hsol.pde t ht x'
  -- Hence its derivative is zero.
  have h_deriv_both : deriv (fun x' => deriv (fun s => u s x') t +
      u t x' * deriv (u t) x') x = 0 := by
    simp only [h_pde_func, deriv_const]
  have ht_Icc : t ∈ Set.Icc 0 T := ⟨ht.1, le_of_lt ht.2⟩
  have hd1 : DifferentiableAt ℝ (fun x' => deriv (fun s => u s x') t) x :=
    differentiableAt_timeDeriv_slice hsol t ht x
  have hd_u : DifferentiableAt ℝ (u t) x := differentiableAt_slice hsol t x
  have hd_ux : DifferentiableAt ℝ (fun x' => deriv (u t) x') x :=
    hsol.gradient_differentiable_slice t ht_Icc x
  have hd2 : DifferentiableAt ℝ (fun x' => u t x' * deriv (u t) x') x := hd_u.mul hd_ux
  -- Sum rule: `∂ₓ (A + B) = ∂ₓ A + ∂ₓ B`.
  have h_sum : deriv (fun x' => deriv (fun s => u s x') t + u t x' * deriv (u t) x') x =
      deriv (fun x' => deriv (fun s => u s x') t) x +
        deriv (fun x' => u t x' * deriv (u t) x') x :=
    deriv_add hd1 hd2
  -- Combine: `∂ₓ A + ∂ₓ B = 0`.
  have h_key : deriv (fun x' => deriv (fun s => u s x') t) x +
      deriv (fun x' => u t x' * deriv (u t) x') x = 0 :=
    h_sum.symm.trans h_deriv_both
  -- Product rule.
  have h_prod : deriv (fun x' => u t x' * deriv (u t) x') x =
      deriv (u t) x * deriv (u t) x + u t x * deriv (fun x' => deriv (u t) x') x :=
    deriv_mul hd_u hd_ux
  rw [h_prod] at h_key
  have h_sq : deriv (u t) x * deriv (u t) x = deriv (u t) x ^ 2 := by ring
  rw [h_sq] at h_key
  linarith

end Burgers

end
