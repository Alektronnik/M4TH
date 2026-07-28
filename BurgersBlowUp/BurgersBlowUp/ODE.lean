/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import BurgersBlowUp.Calculus

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
