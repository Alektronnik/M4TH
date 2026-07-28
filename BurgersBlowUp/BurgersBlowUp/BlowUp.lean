/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import BurgersBlowUp.Characteristics

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
