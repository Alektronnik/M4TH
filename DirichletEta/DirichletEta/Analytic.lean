/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import DirichletEta.Basic

/-!
# Analytic API for the Dirichlet eta product

This file records the differentiability of eta terms and the analyticity of
the zeta-product normalisation on the punctured right half-plane.
-/

@[expose] public section

open Complex Set

namespace DirichletEta

lemma etaTerm_differentiable (n : ℕ) : Differentiable ℂ (etaTerm n) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  unfold etaTerm
  refine Differentiable.div (differentiable_const _) ?_ ?_
  · refine Differentiable.const_cpow differentiable_id ?_
    exact Or.inl hn
  · simp [hn]

lemma etaPartialSum_differentiable (N : ℕ) : Differentiable ℂ (etaPartialSum N) := by
  unfold etaPartialSum
  have h_eq : (fun s => ∑ n ∈ Finset.range N, etaTerm n s) =
      (∑ n ∈ Finset.range N, etaTerm n) := by
    ext s
    simp only [Finset.sum_apply]
  rw [h_eq]
  exact Differentiable.sum fun n _ => etaTerm_differentiable n

lemma etaTerm_norm_eq {s : ℂ} (n : ℕ) (_hs : 0 < s.re) :
    ‖etaTerm n s‖ = (n + 1 : ℝ) ^ (-s.re) := by
  have hn : 0 < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  unfold etaTerm
  simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow]
  have h_eq : (n + 1 : ℂ) = (((n + 1 : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [h_eq]
  rw [norm_cpow_eq_rpow_re_of_pos hn]
  rw [one_div, Real.rpow_neg (by linarith)]

lemma analyticOn_etaZetaProduct :
    AnalyticOn ℂ (fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
      {s | 0 < s.re ∧ s ≠ 1} := by
  have hU : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
  rw [analyticOn_iff_differentiableOn hU]
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.mul ?_ (differentiableAt_riemannZeta hs.2)
  refine (differentiableAt_const 1).sub ?_
  refine DifferentiableAt.const_cpow ((differentiableAt_const 1).sub differentiableAt_id) ?_
  exact Or.inl (by norm_num : (2 : ℂ) ≠ 0)

lemma analyticOn_dirichletEta :
    AnalyticOn ℂ dirichletEta {s | 0 < s.re ∧ s ≠ 1} := by
  dsimp [dirichletEta]
  exact analyticOn_etaZetaProduct

lemma dirichletEta_eq_zeta_of_re_pos {s : ℂ} (_hs : 0 < s.re) (_hs1 : s ≠ 1) :
    dirichletEta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s :=
  rfl

end DirichletEta

