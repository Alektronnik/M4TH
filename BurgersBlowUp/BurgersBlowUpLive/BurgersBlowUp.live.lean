/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# BurgersBlowUp live edition

Single-file live edition of the `BurgersBlowUp` package for web certification
and study.  The mathematical content is the package source fused in dependency
order: `Calculus`, `ODE`, `Characteristics`, and `BlowUp`.
-/


/-!
## Source file: `BurgersBlowUp/Calculus.lean`
-/

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


/-!
## Source file: `BurgersBlowUp/ODE.lean`
-/

/-!
# ODE lemmas for the method of characteristics

Self-contained ordinary-differential-equation ingredients used by the gradient
blow-up argument for the inviscid Burgers equation:

* a **Lyapunov-energy uniqueness lemma** for linear ODEs: if `Y 0 = 0` and
  `Y' = -Y · f` with `f` bounded, then `Y ≡ 0` on `[0, T]`.  The proof runs the
  classical Grönwall argument through the energy
  `W (s) = Y (s) ^ 2 · exp (-2 M s)`, whose derivative is nonpositive;
* the **exact solution of the Riccati equation** `V' = -V ^ 2` with
  `V 0 = -1`, namely `V (t) = -1 / (1 - t)` on `[0, T]` for `T < 1`, obtained by
  reducing to the linear uniqueness lemma via `U (s) = V (s) (1 - s) + 1`;
* the **chain rule along a plane curve**: the derivative of
  `t ↦ u (γ t).1 (γ t).2` decomposes into the two partial derivatives of `u`
  paired with the velocity of `γ`.

## Main results

- `Burgers.linear_ode_uniqueness`
- `Burgers.riccati_ode_solution`
- `Burgers.hasDerivAt_comp_curve`

## Implementation notes

`linear_ode_uniqueness` is proved from scratch via the Lyapunov energy rather
than through Mathlib's Grönwall machinery
(`norm_le_gronwallBound_of_norm_deriv_right_le`, `ODE_solution_unique`); whether
those subsume it should be evaluated at review time.  Similarly, the private
lemma `exists_abs_le_of_continuousOn` is likely subsumed by
`IsCompact.exists_bound_of_continuousOn`; it is kept private pending
deduplication.

## Tags

ODE, uniqueness, Gronwall, Lyapunov, Riccati, chain rule
-/

open Set

@[expose] public section

namespace Burgers

/-- A function starting at `0` with nonpositive derivative on `[0, T)` is
nonpositive on `[0, T]`.  Thin wrapper over `antitoneOn_of_deriv_nonpos`. -/
private lemma nonpos_of_deriv_nonpos (g : ℝ → ℝ) (T : ℝ)
    (h_cont : ContinuousOn g (Set.Icc 0 T))
    (h_diff : DifferentiableOn ℝ g (Set.Ioo 0 T))
    (h_zero : g 0 = 0)
    (h_deriv : ∀ s ∈ Set.Ico 0 T, deriv g s ≤ 0) :
    ∀ t ∈ Set.Icc 0 T, g t ≤ 0 := by
  intro t ht
  have hsc : Convex ℝ (Set.Icc 0 T) := convex_Icc 0 T
  have hM : ∀ x ∈ interior (Set.Icc 0 T), deriv g x ≤ 0 := by
    intro x hx
    rw [interior_Icc] at hx
    exact h_deriv x ⟨le_of_lt hx.1, hx.2⟩
  have h_anti : AntitoneOn g (Set.Icc 0 T) := by
    have h_diff_int : DifferentiableOn ℝ g (interior (Set.Icc 0 T)) := by
      rw [interior_Icc]
      exact h_diff
    exact antitoneOn_of_deriv_nonpos hsc h_cont h_diff_int hM
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := by
    constructor
    · rfl
    · exact le_trans ht.1 ht.2
  have h_le := h_anti h0 ht ht.1
  rw [h_zero] at h_le
  exact h_le

/-- Differentiability of the Lyapunov energy `Y ^ 2 · exp (-2 M s)` on the open
interval. -/
private lemma differentiableOn_lyapunov (Y : ℝ → ℝ) (f : ℝ → ℝ) (T M : ℝ)
    (hY : ∀ s ∈ Set.Ico 0 T, HasDerivAt Y (- Y s * f s) s) :
    DifferentiableOn ℝ (fun s => Y s ^ 2 * Real.exp (-2 * M * s)) (Set.Ioo 0 T) := by
  intro s hs
  have hYs := hY s ⟨le_of_lt hs.1, hs.2⟩
  have hY_diff : DifferentiableAt ℝ Y s := hYs.differentiableAt
  have hexp_diff : DifferentiableAt ℝ (fun s => Real.exp (-2 * M * s)) s := by
    fun_prop
  exact (hY_diff.pow 2 |>.mul hexp_diff).differentiableWithinAt

/-- **Uniqueness for linear ODEs** (corollary of Grönwall).  If `Y 0 = 0` and
`Y' (s) = -Y (s) · f (s)` with `|f| ≤ M` on `[0, T]`, then `Y ≡ 0` on `[0, T]`.
Proved via the Lyapunov energy `W (s) = Y (s) ^ 2 · exp (-2 M s)`. -/
lemma linear_ode_uniqueness (Y : ℝ → ℝ) (f : ℝ → ℝ) (T : ℝ) (M : ℝ)
    (hY_cont : ContinuousOn Y (Set.Icc 0 T))
    (h_bound : ∀ s ∈ Set.Icc 0 T, |f s| ≤ M)
    (h_zero : Y 0 = 0)
    (h_deriv : ∀ s ∈ Set.Ico 0 T, HasDerivAt Y (- Y s * f s) s) :
    ∀ t ∈ Set.Icc 0 T, Y t = 0 := by
  intro t ht
  let W := fun s => Y s ^ 2 * Real.exp (-2 * M * s)
  have hW0 : W 0 = 0 := by
    dsimp [W]
    rw [h_zero]
    ring
  have h_deriv_W : ∀ s ∈ Set.Ico 0 T, deriv W s ≤ 0 := by
    intro s hs
    have hY_s := h_deriv s hs
    have hY2_s : HasDerivAt (fun x => Y x ^ 2) (2 * Y s * (- Y s * f s)) s := by
      have h_step := hY_s.pow 2
      have h_deriv_eq : 2 * Y s ^ (2 - 1) * (- Y s * f s) = 2 * Y s * (- Y s * f s) := by
        have h_pow_sub : 2 - 1 = 1 := by norm_num
        rw [h_pow_sub, pow_one]
      rw [← h_deriv_eq]
      exact h_step
    have hexp_s : HasDerivAt (fun x => Real.exp (-2 * M * x))
        (-2 * M * Real.exp (-2 * M * s)) s := by
      have h_step := HasDerivAt.exp ((hasDerivAt_id s).const_mul (-2 * M))
      change HasDerivAt (fun x => Real.exp (-2 * M * x))
        (Real.exp (-2 * M * s) * (-2 * M * 1)) s at h_step
      have h_deriv_eq : Real.exp (-2 * M * s) * (-2 * M * 1) =
          -2 * M * Real.exp (-2 * M * s) := by
        ring
      rw [← h_deriv_eq]
      exact h_step
    have hW_s : HasDerivAt W
        ((2 * Y s * (- Y s * f s)) * Real.exp (-2 * M * s) +
          (Y s ^ 2) * (-2 * M * Real.exp (-2 * M * s))) s :=
      hY2_s.mul hexp_s
    have h_deriv_eq : deriv W s = -2 * Y s ^ 2 * (f s + M) * Real.exp (-2 * M * s) := by
      rw [hW_s.deriv]
      ring
    rw [h_deriv_eq]
    have h_f_le_M : -M ≤ f s := by
      have : |f s| ≤ M := h_bound s ⟨hs.1, le_of_lt hs.2⟩
      exact (abs_le.mp this).1
    have h_sum_pos : 0 ≤ f s + M := by linarith
    have h_prod : 0 ≤ 2 * Y s ^ 2 * (f s + M) * Real.exp (-2 * M * s) := by
      positivity
    linarith
  have hW_cont : ContinuousOn W (Set.Icc 0 T) := by
    apply ContinuousOn.mul
    · exact hY_cont.pow 2
    · apply ContinuousOn.comp (f := fun s => -2 * M * s) Real.continuous_exp.continuousOn
      · exact (continuous_const.mul continuous_id').continuousOn
      · exact Set.mapsTo_univ _ _
  have hW_nonpos : W t ≤ 0 := by
    exact nonpos_of_deriv_nonpos W T hW_cont
      (differentiableOn_lyapunov Y f T M h_deriv) hW0 h_deriv_W t ht
  have hW_nonneg : W t ≥ 0 := by
    dsimp [W]
    positivity
  have hW_zero : W t = 0 := by linarith
  dsimp [W] at hW_zero
  have h_exp_pos : Real.exp (-2 * M * t) > 0 := by positivity
  have hY_sq_zero : Y t ^ 2 = 0 := by
    cases mul_eq_zero.mp hW_zero with
    | inl h1 => exact h1
    | inr h2 =>
      have : Real.exp (-2 * M * t) ≠ 0 := ne_of_gt h_exp_pos
      contradiction
  exact sq_eq_zero_iff.mp hY_sq_zero

/-- **Chain rule along a plane curve.**  Given `u : ℝ² → ℝ` (curried) and
`γ : ℝ → ℝ²`, the derivative of `u ∘ γ` is
`u_t · γ₁' + u_x · γ₂'` evaluated at `γ s`. -/
lemma hasDerivAt_comp_curve (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) (s : ℝ) (dγ : ℝ × ℝ)
    (h_deriv_γ : HasDerivAt γ dγ s)
    (h_diff : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (γ s)) :
    HasDerivAt (fun t => u (γ t).1 (γ t).2)
      (dγ.1 * deriv (fun t' => u t' (γ s).2) (γ s).1 +
        dγ.2 * deriv (u (γ s).1) (γ s).2) s := by
  have h_chain := h_diff.hasFDerivAt.comp_hasDerivAt s h_deriv_γ
  have h_eval := fderiv_apply_decomp u (γ s) dγ h_diff
  rw [h_eval] at h_chain
  exact h_chain

/-- A continuous function on `[0, T]` is bounded there.  Likely subsumed by
`IsCompact.exists_bound_of_continuousOn`; kept private pending deduplication. -/
private lemma exists_abs_le_of_continuousOn (g : ℝ → ℝ) (T : ℝ)
    (h_cont : ContinuousOn g (Set.Icc 0 T)) :
    ∃ M : ℝ, ∀ s ∈ Set.Icc 0 T, |g s| ≤ M := by
  have h_comp : IsCompact (g '' Set.Icc 0 T) := isCompact_Icc.image_of_continuousOn h_cont
  obtain ⟨b, hb⟩ := h_comp.bddAbove
  obtain ⟨a, ha⟩ := h_comp.bddBelow
  use max |a| |b|
  intro s hs
  have h_mem : g s ∈ g '' Set.Icc 0 T := Set.mem_image_of_mem g hs
  have h_le := hb h_mem
  have h_ge := ha h_mem
  rw [abs_le]
  constructor
  · have : - max |a| |b| ≤ -|a| := by
      rw [neg_le_neg_iff]
      exact le_max_left |a| |b|
    have : -|a| ≤ a := by linarith [le_abs_self a, neg_le_abs a]
    linarith
  · have : b ≤ |b| := le_abs_self b
    have : |b| ≤ max |a| |b| := le_max_right |a| |b|
    linarith

/-- **Exact solution of the Riccati equation** `V' = -V ^ 2`.  If `V 0 = -1` and
`V' (s) = -V (s) ^ 2` on `[0, T]` with `T < 1`, then `V (t) = -1 / (1 - t)`.
Proved by reducing `U (s) = V (s) (1 - s) + 1` to the linear uniqueness lemma. -/
lemma riccati_ode_solution (V : ℝ → ℝ) (T : ℝ) (hT : T < 1)
    (hV_cont : ContinuousOn V (Set.Icc 0 T))
    (h_zero : V 0 = -1)
    (h_deriv : ∀ s ∈ Set.Ico 0 T, HasDerivAt V (- (V s) ^ 2) s) :
    ∀ t ∈ Set.Icc 0 T, V t = -1 / (1 - t) := by
  intro t ht
  let U := fun s => V s * (1 - s) + 1
  have hU0 : U 0 = 0 := by
    dsimp [U]
    rw [h_zero]
    ring
  have hU_deriv : ∀ s ∈ Set.Ico 0 T, HasDerivAt U (- U s * V s) s := by
    intro s hs
    have hV_s := h_deriv s hs
    have h_1_minus : HasDerivAt (fun x => 1 - x) (-1) s := by
      have h_const := hasDerivAt_const s (1 : ℝ)
      have h_id := hasDerivAt_id s
      have h_sub := h_const.sub h_id
      change HasDerivAt (fun t => 1 - t) (0 - 1) s at h_sub
      have h_deriv_eq : 0 - 1 = (-1 : ℝ) := by ring
      rw [h_deriv_eq] at h_sub
      exact h_sub
    have h_prod := hV_s.mul h_1_minus
    have h_add := h_prod.add_const 1
    have h_deriv_eq : -V s ^ 2 * (1 - s) + V s * -1 = - (V s * (1 - s) + 1) * V s := by ring
    rw [h_deriv_eq] at h_add
    change HasDerivAt U (- U s * V s) s at h_add
    exact h_add
  obtain ⟨M, h_bound⟩ := exists_abs_le_of_continuousOn V T hV_cont
  have h_U_zero : U t = 0 := by
    have hU_cont : ContinuousOn U (Set.Icc 0 T) := by
      have : U = (fun s => V s * (1 - s) + 1) := rfl
      rw [this]
      fun_prop
    have h_zero_all := linear_ode_uniqueness U V T M hU_cont h_bound hU0 hU_deriv
    exact h_zero_all t ht
  have h_1_minus_t : 1 - t ≠ 0 := by
    have : t < 1 := lt_of_le_of_lt ht.2 hT
    linarith
  dsimp [U] at h_U_zero
  have h_eq : V t * (1 - t) = -1 := by linarith
  have h_div : V t = -1 / (1 - t) := by
    rw [eq_div_iff h_1_minus_t]
    exact h_eq
  exact h_div

end Burgers

end


/-!
## Source file: `BurgersBlowUp/Characteristics.lean`
-/

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


/-!
## Source file: `BurgersBlowUp/BlowUp.lean`
-/

/-!
# Gradient blow-up for the inviscid Burgers equation

Formation of a singularity in finite time: for the compressive initial datum
`u₀ (x) = -x`, no `C²` regular solution of the inviscid Burgers equation exists
on `[0, T)` once `T ≥ 1`.

The mechanism is the classical one, carried out analytically end to end.  Along
each characteristic line `t ↦ x₀ (1 - t)` the spatial gradient
`V (t) = u_x (t, x₀ (1 - t))` satisfies the Riccati equation `V' = -V ^ 2` with
`V (0) = -1` (`gradient_riccati_evolution`, obtained from the spatially
differentiated PDE, the Schwarz condition and the constancy of `u` along the
characteristic).  The exact solution `V (t) = -1 / (1 - t)`
(`gradient_eq_neg_one_div`) therefore diverges as `t → 1⁻`.

The blow-up theorem itself avoids any limit argument: given the gradient bound
`M` of a putative regular solution, evaluating the exact formula at the critical
time `t = 1 - 1 / (|M| + 1)` produces a gradient of magnitude `|M| + 1 > M` —
a purely algebraic contradiction.

## Main results

- `Burgers.gradient_riccati_evolution`: the gradient satisfies
  `V' = -V ^ 2` along characteristics.
- `Burgers.gradient_eq_neg_one_div`:
  `u_x (t, x₀ (1 - t)) = -1 / (1 - t)` for `t < 1`.
- `Burgers.not_isRegularSolution_initialRamp`: **the blow-up
  theorem** — there is no regular solution on `[0, T)` for `T ≥ 1`.

## Tags

Burgers equation, blow-up, singularity formation, Riccati, shock
-/

open Set

@[expose] public section

namespace Burgers

/-- **Riccati evolution of the gradient along characteristics.**
Differentiating the Burgers equation in `x` and using the Schwarz condition,
the gradient `V (s) = u_x (s, x₀ (1 - s))` satisfies `V' = -V ^ 2`. -/
lemma gradient_riccati_evolution {T : ℝ} {u : ℝ → ℝ → ℝ}
    (hsol : IsRegularSolution initialRamp T u) (x₀ : ℝ) :
    ∀ s ∈ Set.Ico 0 T,
      HasDerivAt (fun t => deriv (u t) (x₀ * (1 - t)))
        (- (deriv (u s) (x₀ * (1 - s))) ^ 2)
        s := by
  intro s hs
  let γ := fun t => (t, x₀ * (1 - t))
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
  have h_diff := hsol.gradient_differentiable (γ s)
  have h_chain := hasDerivAt_comp_curve (fun t x => deriv (u t) x) γ s (1, -x₀)
    h_deriv_γ h_diff
  have h_u_const := constant_along_characteristic hsol x₀ s ⟨hs.1, le_of_lt hs.2⟩
  have h_schwarz := hsol.schwarz s hs (x₀ * (1 - s))
  have h_pde := pde_spatial_deriv hsol s hs (x₀ * (1 - s))
  have h_deriv_eq : 1 * deriv (fun t' => deriv (u t') (x₀ * (1 - s))) s +
      -x₀ * deriv (fun x' => deriv (u s) x') (x₀ * (1 - s)) =
        - (deriv (u s) (x₀ * (1 - s))) ^ 2 := by
    rw [h_schwarz, ← h_u_const]
    linarith [h_pde]
  rw [h_deriv_eq] at h_chain
  exact h_chain

/-- **Exact gradient formula along characteristics.**  The Riccati ODE
`V' = -V ^ 2` with `V (0) = -1` gives `u_x (t, x₀ (1 - t)) = -1 / (1 - t)`. -/
lemma gradient_eq_neg_one_div {T : ℝ} {u : ℝ → ℝ → ℝ}
    (hsol : IsRegularSolution initialRamp T u)
    (x₀ : ℝ) (t : ℝ) (ht : t ∈ Set.Ico 0 T) (ht_lt : t < 1) :
    deriv (u t) (x₀ * (1 - t)) = -1 / (1 - t) := by
  -- The gradient along the characteristic.
  let V := fun s => deriv (u s) (x₀ * (1 - s))
  -- Initial value: `V (0) = deriv initialRamp x₀ = -1`.
  have hV0 : V 0 = -1 := by
    dsimp [V]
    have h_u0 : u 0 = initialRamp := by
      ext x
      exact hsol.initial x
    rw [h_u0]
    have h_simp : x₀ * (1 - 0) = x₀ := by ring
    rw [h_simp]
    have h_deriv : HasDerivAt initialRamp (-1) x₀ := by
      unfold initialRamp
      exact HasDerivAt.neg (hasDerivAt_id x₀)
    exact h_deriv.deriv
  -- Riccati evolution on `[0, t)`.
  have hV_deriv : ∀ s ∈ Set.Ico 0 t, HasDerivAt V (- (V s) ^ 2) s := by
    intro s hs
    have hs_T : s ∈ Set.Ico 0 T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    exact gradient_riccati_evolution hsol x₀ s hs_T
  -- Continuity of `V` on `[0, t]`.
  have hV_cont : ContinuousOn V (Set.Icc 0 t) := by
    have h_joint_diff : Differentiable ℝ (fun p' : ℝ × ℝ => deriv (u p'.1) p'.2) :=
      hsol.gradient_differentiable
    have h_joint_cont : Continuous (fun p' : ℝ × ℝ => deriv (u p'.1) p'.2) :=
      h_joint_diff.continuous
    have h_γ_cont : Continuous (fun s => (s, x₀ * (1 - s))) := by fun_prop
    exact (h_joint_cont.comp h_γ_cont).continuousOn
  -- Exact Riccati solution.
  have h_riccati := riccati_ode_solution V t ht_lt hV_cont hV0 hV_deriv
  have ht_Icc : t ∈ Set.Icc 0 t := ⟨ht.1, le_rfl⟩
  exact h_riccati t ht_Icc

/-- **The blow-up theorem.**  The Burgers equation with initial datum
`u₀ (x) = -x` develops a gradient singularity: no `C²` regular solution exists
on `[0, T)` once `T ≥ 1`.

The proof is a purely algebraic contradiction, with no limit argument: at the
critical time `t = 1 - 1 / (|M| + 1)` the exact gradient formula gives magnitude
`|M| + 1`, exceeding the gradient bound `M` of the putative solution. -/
theorem not_isRegularSolution_initialRamp {T : ℝ} (hT : 1 ≤ T) (u : ℝ → ℝ → ℝ) :
    ¬ IsRegularSolution initialRamp T u := by
  intro hsol
  obtain ⟨M, hM⟩ := hsol.gradient_bounded
  -- The critical time `t = 1 - 1 / (|M| + 1)` lies in `[0, T]`.
  have h_t_Icc : 1 - 1 / (|M| + 1) ∈ Set.Icc 0 T := by
    constructor
    · have h_pos : 0 < |M| + 1 := by positivity
      have : 1 / (|M| + 1) ≤ 1 := by
        rw [div_le_iff₀ h_pos, one_mul]
        linarith [abs_nonneg M]
      linarith
    · have : 1 - 1 / (|M| + 1) < 1 := by
        have : 0 < 1 / (|M| + 1) := by positivity
        linarith
      linarith
  have h_t : 1 - 1 / (|M| + 1) ∈ Set.Ico 0 T := by
    constructor
    · exact h_t_Icc.1
    · have : 1 - 1 / (|M| + 1) < 1 := by
        have : 0 < 1 / (|M| + 1) := by positivity
        linarith
      linarith
  have h_t_lt : 1 - 1 / (|M| + 1) < 1 := by
    have : 0 < 1 / (|M| + 1) := by positivity
    linarith
  -- Exact gradient value at the critical time, on the characteristic `x₀ = 0`.
  have h_deriv_val := gradient_eq_neg_one_div hsol 0 (1 - 1 / (|M| + 1)) h_t h_t_lt
  have h_zero : (0 : ℝ) * (1 - (1 - 1 / (|M| + 1))) = 0 := by ring
  rw [h_zero] at h_deriv_val
  -- The gradient bound at `x = 0`.
  have h_bound := hM (1 - 1 / (|M| + 1)) h_t_Icc 0
  rw [h_deriv_val] at h_bound
  -- Simplify the denominator: `1 - (1 - 1 / (|M| + 1)) = 1 / (|M| + 1)`.
  have h_denom : 1 - (1 - 1 / (|M| + 1)) = 1 / (|M| + 1) := by ring
  rw [h_denom] at h_bound
  -- Simplify `-1 / (1 / (|M| + 1)) = -(|M| + 1)`.
  have h_div : -1 / (1 / (|M| + 1)) = -(|M| + 1) := by
    have h_pos : 0 < |M| + 1 := by positivity
    have : 1 / (|M| + 1) ≠ 0 := by positivity
    field_simp
  rw [h_div] at h_bound
  -- Final contradiction: `|-(|M| + 1)| ≤ M` forces `|M| + 1 ≤ M`.
  have h_abs : |-(|M| + 1)| = |M| + 1 := by
    rw [abs_neg, abs_of_pos]
    positivity
  rw [h_abs] at h_bound
  linarith [le_abs_self M]

/-! ### Certificates

Concrete instances checked by the kernel.  After `lake build`, running

  `#print axioms Burgers.not_isRegularSolution_initialRamp`

must report only the foundational axioms `propext`, `Classical.choice`,
`Quot.sound`. -/

section Certificates

/-- No regular solution exists on `[0, 1)`. -/
example (u : ℝ → ℝ → ℝ) : ¬ IsRegularSolution initialRamp 1 u :=
  not_isRegularSolution_initialRamp le_rfl u

/-- In particular, no global regular solution exists on `[0, 2)`. -/
example : ¬ ∃ u : ℝ → ℝ → ℝ, IsRegularSolution initialRamp 2 u := by
  rintro ⟨u, hu⟩
  exact not_isRegularSolution_initialRamp (by norm_num) u hu

end Certificates

end Burgers

end
