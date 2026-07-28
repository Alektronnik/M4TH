/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Tactic

/-!
# DiscreteAbelChebyshev.live

Single-file live version of the `DiscreteAbelChebyshev` package.
-/

@[expose] public section

/-!
## Source file: `DiscreteAbelChebyshev/Basic.lean`
-/

open Finset

namespace DiscreteAbelChebyshev

/-- Partial sums of a real sequence over `range n`. -/
noncomputable def sumSeq (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, a i

@[simp] lemma sumSeq_zero (a : ℕ → ℝ) : sumSeq a 0 = 0 := by
  simp [sumSeq]

lemma sumSeq_succ (a : ℕ → ℝ) (n : ℕ) :
    sumSeq a (n + 1) = sumSeq a n + a n := by
  simp [sumSeq, Finset.sum_range_succ]

/-- Recover `a n` from consecutive partial sums. -/
lemma sumSeq_sub_succ (a : ℕ → ℝ) (n : ℕ) :
    sumSeq a (n + 1) - sumSeq a n = a n := by
  simp [sumSeq_succ]

/-- Shift `n ↦ n + 1` in a sum over `range N`. -/
lemma sum_range_add_one (g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, g (n + 1) =
      ((∑ k ∈ range (N + 1), g k) - g 0) := by
  exact (sub_eq_iff_eq_add.mpr (sum_range_succ' g N)).symm

/-- Telescoping identity for shifted partial sums. -/
lemma sum_sumSeq_mul_shift (a f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, sumSeq a (n + 1) * f (n + 1) =
      sumSeq a N * f N + ∑ n ∈ range N, sumSeq a n * f n := by
  have h0 : sumSeq a 0 * f 0 = 0 := by simp [sumSeq_zero]
  calc
    ∑ n ∈ range N, sumSeq a (n + 1) * f (n + 1)
        = ((∑ k ∈ range (N + 1), sumSeq a k * f k) - sumSeq a 0 * f 0) :=
          sum_range_add_one (fun k => sumSeq a k * f k) N
    _ = (∑ k ∈ range (N + 1), sumSeq a k * f k) := by rw [h0, sub_zero]
    _ = sumSeq a N * f N + ∑ k ∈ range N, sumSeq a k * f k := by
      rw [Finset.sum_range_succ, add_comm]

/-- Fundamental finite Abel summation identity. -/
lemma abel_summation (a f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, a n * f n =
      sumSeq a N * f N -
        ∑ n ∈ range N, sumSeq a (n + 1) * (f (n + 1) - f n) := by
  have hterm :
      ∀ n ∈ range N,
        a n * f n = sumSeq a (n + 1) * f n - sumSeq a n * f n := by
    intro n _
    rw [← sumSeq_sub_succ a n, sub_mul]
  calc
    ∑ n ∈ range N, a n * f n
        = ∑ n ∈ range N, (sumSeq a (n + 1) * f n - sumSeq a n * f n) :=
          Finset.sum_congr rfl hterm
    _ = ∑ n ∈ range N, sumSeq a (n + 1) * f n -
          ∑ n ∈ range N, sumSeq a n * f n := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ n ∈ range N, sumSeq a (n + 1) * f n + sumSeq a N * f N -
          ∑ n ∈ range N, sumSeq a (n + 1) * f (n + 1) := by
          have h := sum_sumSeq_mul_shift a f N
          linarith
    _ = sumSeq a N * f N -
          ∑ n ∈ range N, sumSeq a (n + 1) * (f (n + 1) - f n) := by
          have hsplit :
              ∑ n ∈ range N, sumSeq a (n + 1) * (f (n + 1) - f n) =
                ∑ n ∈ range N, sumSeq a (n + 1) * f (n + 1) -
                  ∑ n ∈ range N, sumSeq a (n + 1) * f n := by
            simp_rw [mul_sub, ← Finset.sum_sub_distrib]
          rw [hsplit]
          abel

/-- The real von Mangoldt-like sequence used by the discrete Chebyshev bridge. -/
noncomputable def mangoldt (n : ℕ) : ℝ :=
  if IsPrimePow n then Real.log (Nat.minFac n) else 0

/-- Discrete Chebyshev `ψ` as a partial sum of `mangoldt`. -/
noncomputable def psi (N : ℕ) : ℝ :=
  sumSeq mangoldt N

/-- Safe reciprocal logarithm weight. -/
noncomputable def invLog (n : ℕ) : ℝ :=
  if n ≥ 2 then 1 / Real.log (n : ℝ) else 0

/-- Constant sequence equal to `1`. -/
noncomputable def seqOne (_n : ℕ) : ℝ :=
  1

@[simp] lemma sumSeq_one (N : ℕ) : sumSeq seqOne N = (N : ℝ) := by
  dsimp [sumSeq, seqOne]
  simp

end DiscreteAbelChebyshev

/-!
## Source file: `DiscreteAbelChebyshev/ChebyshevBridge.lean`
-/

open Finset

namespace DiscreteAbelChebyshev

/-- Exact Abel identity for the weighted von Mangoldt sum. -/
lemma pi_approx_eq_abel (N : ℕ) :
    ∑ n ∈ range N, mangoldt n * invLog n =
      psi N * invLog N - ∑ n ∈ range N, psi (n + 1) * (invLog (n + 1) - invLog n) := by
  exact abel_summation mangoldt invLog N

/-- Discrete Chebyshev error `E(n) = ψ(n) - n`. -/
noncomputable def psi_error (n : ℕ) : ℝ :=
  psi n - n

/-- Split the Abel correction into main and error terms. -/
lemma abel_psi_split (N : ℕ) :
    ∑ n ∈ range N, psi (n + 1) * (invLog (n + 1) - invLog n) =
      (∑ n ∈ range N, (n + 1 : ℝ) * (invLog (n + 1) - invLog n)) +
      (∑ n ∈ range N, psi_error (n + 1) * (invLog (n + 1) - invLog n)) := by
  dsimp [psi_error]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  push_cast
  ring

/-- Reverse Abel collapse for the main term. -/
lemma main_term_collapse (N : ℕ) :
    ∑ n ∈ range N, (n + 1 : ℝ) * (invLog (n + 1) - invLog n) =
      (N : ℝ) * invLog N - ∑ n ∈ range N, invLog n := by
  have h_abel := abel_summation seqOne invLog N
  have h_left : ∑ n ∈ range N, seqOne n * invLog n = ∑ n ∈ range N, invLog n := by
    apply Finset.sum_congr rfl
    intro x _
    dsimp [seqOne]
    ring
  rw [h_left] at h_abel
  simp_rw [sumSeq_one] at h_abel
  have h_cast : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    intro n
    push_cast
    rfl
  simp_rw [h_cast] at h_abel
  linarith

/-- Exact weighted-prime approximation identity. -/
lemma pi_approx_final (N : ℕ) :
    ∑ n ∈ range N, mangoldt n * invLog n =
      (∑ n ∈ range N, invLog n) +
        psi_error N * invLog N -
          ∑ n ∈ range N, psi_error (n + 1) * (invLog (n + 1) - invLog n) := by
  have h1 := pi_approx_eq_abel N
  have h2 := abel_psi_split N
  have h3 := main_term_collapse N
  have h_psi : psi N = (N : ℝ) + psi_error N := by
    dsimp [psi_error]
    ring
  rw [h1, h2, h3, h_psi]
  ring

/-- Chebyshev error bound hypothesis. -/
def IsChebyshevBounded (C : ℝ) (N₀ : ℕ) : Prop :=
  ∀ N ≥ N₀, |psi_error N| ≤ C * Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2

/-- Residual error-sum estimate, kept as an explicit frontier. -/
def ChebyshevErrorSumBound (C : ℝ) (N₀ : ℕ) : Prop :=
  ∀ N, N ≥ max N₀ 2 →
    |∑ n ∈ range N, psi_error (n + 1) * (invLog (n + 1) - invLog n)| ≤
      C * 2 * Real.sqrt (N : ℝ)

/-- Bound for the endpoint error term. -/
lemma bound_error_eval
    (C : ℝ) (N₀ : ℕ) (_hC : 0 ≤ C) (h_bound : IsChebyshevBounded C N₀)
    (N : ℕ) (hN : N ≥ max N₀ 2) :
    |psi_error N * invLog N| ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
  have hN_ge_N₀ : N ≥ N₀ := le_trans (le_max_left N₀ 2) hN
  have hN_ge_2 : N ≥ 2 := le_trans (le_max_right N₀ 2) hN
  have h_psi := h_bound N hN_ge_N₀
  have h_log_pos : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega)
  have h_inv_log_pos : 0 < 1 / Real.log (N : ℝ) := one_div_pos.mpr h_log_pos
  dsimp [invLog]
  rw [if_pos hN_ge_2, abs_mul, abs_of_pos h_inv_log_pos]
  calc
    |psi_error N| * (1 / Real.log (N : ℝ))
        ≤ (C * Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2) *
            (1 / Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_right h_psi h_inv_log_pos.le
    _ = C * Real.sqrt (N : ℝ) * ((Real.log (N : ℝ)) ^ 2 / Real.log (N : ℝ)) := by ring
    _ = C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
      congr 2
      rw [pow_two]
      exact mul_div_cancel_right₀ _ h_log_pos.ne'

/-- Derivative of `1 / log x` on the positive real axis. -/
lemma deriv_invLog (x : ℝ) (hx : 1 < x) :
    deriv (fun t => (Real.log t)⁻¹) x = - (x * (Real.log x) ^ 2)⁻¹ := by
  have h_log_pos : 0 < Real.log x := Real.log_pos hx
  have hd1 : HasDerivAt Real.log (x⁻¹) x := Real.hasDerivAt_log (by linarith)
  have hd2 : HasDerivAt (fun y => y⁻¹) (-(Real.log x ^ 2)⁻¹) (Real.log x) :=
    hasDerivAt_inv h_log_pos.ne'
  have hd3 := HasDerivAt.comp x hd2 hd1
  have heq : deriv (fun t => (Real.log t)⁻¹) x = (-(Real.log x ^ 2)⁻¹) * x⁻¹ :=
    hd3.deriv
  rw [heq]
  have h_den : x * (Real.log x) ^ 2 ≠ 0 := by positivity
  field_simp

lemma invLog_continuousOn (n : ℕ) (hn : n ≥ 2) :
    ContinuousOn (fun t => (Real.log t)⁻¹) (Set.Icc (n : ℝ) (n + 1 : ℝ)) := by
  intro x hx
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx_gt_1 : 1 < x := by linarith [hx.1]
  refine ContinuousAt.continuousWithinAt ?_
  refine (Real.continuousAt_log (by linarith)).inv₀ (Real.log_pos hx_gt_1).ne'

lemma invLog_differentiableOn (n : ℕ) (hn : n ≥ 2) :
    DifferentiableOn ℝ (fun t => (Real.log t)⁻¹) (Set.Ioo (n : ℝ) (n + 1 : ℝ)) := by
  intro x hx
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx_gt_1 : 1 < x := by linarith [hx.1]
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (Real.differentiableAt_log (by linarith)).inv (Real.log_pos hx_gt_1).ne'

/-- Mean-value bound for the discrete reciprocal-log difference. -/
lemma invLog_diff_bound (n : ℕ) (hn : n ≥ 2) :
    |invLog (n + 1) - invLog n| ≤
      (1 : ℝ) / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
  have hn_re : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : 0 < (n : ℝ) := by linarith
  have h_lt : (n : ℝ) < (n + 1 : ℝ) := by linarith
  have h_mvt :=
    exists_deriv_eq_slope (fun t => (Real.log t)⁻¹) h_lt
      (invLog_continuousOn n hn) (invLog_differentiableOn n hn)
  rcases h_mvt with ⟨c, hc, h_eq⟩
  have hc_gt_1 : 1 < c := by linarith [hc.1]
  have hc_pos : 0 < c := by linarith
  have h_deriv_c := deriv_invLog c hc_gt_1
  dsimp [invLog]
  have hn1 : n + 1 ≥ 2 := by omega
  rw [if_pos hn1, if_pos hn]
  have h_inv1 : 1 / Real.log ((n + 1 : ℕ) : ℝ) = (Real.log ((n + 1 : ℝ)))⁻¹ := by
    push_cast
    exact one_div _
  have h_inv2 : 1 / Real.log (n : ℝ) = (Real.log (n : ℝ))⁻¹ := one_div _
  rw [h_inv1, h_inv2]
  have h_slope :
      (Real.log (n + 1 : ℝ))⁻¹ - (Real.log (n : ℝ))⁻¹ =
        deriv (fun t => (Real.log t)⁻¹) c * ((n + 1 : ℝ) - n) := by
    rw [h_eq]
    ring
  have h_diff_one : (n + 1 : ℝ) - n = 1 := by ring
  rw [h_diff_one, mul_one] at h_slope
  rw [h_slope, h_deriv_c]
  have h_abs : |- (c * (Real.log c) ^ 2)⁻¹| = (c * (Real.log c) ^ 2)⁻¹ := by
    rw [abs_neg]
    have : 0 ≤ (c * (Real.log c) ^ 2)⁻¹ := by positivity
    exact abs_of_nonneg this
  rw [h_abs, inv_eq_one_div]
  have h_log_mono : Real.log (n : ℝ) ≤ Real.log c := Real.log_le_log hn_pos hc.1.le
  have h_log_n_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have h_sq_mono : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log c) ^ 2 := by
    nlinarith
  have h_denom_mono :
      (n : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ c * (Real.log c) ^ 2 := by
    have h1 :
        (n : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ c * (Real.log (n : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hc.1.le (by positivity)
    have h2 : c * (Real.log (n : ℝ)) ^ 2 ≤ c * (Real.log c) ^ 2 :=
      mul_le_mul_of_nonneg_left h_sq_mono hc_pos.le
    linarith
  have h_denom_pos : 0 < (n : ℝ) * (Real.log (n : ℝ)) ^ 2 :=
    mul_pos hn_pos (by positivity)
  exact one_div_le_one_div_of_le h_denom_pos h_denom_mono

/-- Discrete Chebyshev error transfer, conditional on the residual sum frontier. -/
theorem chebyshev_implies_prime_error
    (C : ℝ) (N₀ : ℕ) (hC : 0 ≤ C)
    (h_bound : IsChebyshevBounded C N₀) (h_sum : ChebyshevErrorSumBound C N₀)
    (N : ℕ) (hN : N ≥ max N₀ 2) :
    |∑ n ∈ range N, mangoldt n * invLog n - ∑ n ∈ range N, invLog n| ≤
      C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) + C * 2 * Real.sqrt (N : ℝ) := by
  have h_sub :
      ∑ n ∈ range N, mangoldt n * invLog n - ∑ n ∈ range N, invLog n =
        psi_error N * invLog N +
          (-∑ n ∈ range N, psi_error (n + 1) * (invLog (n + 1) - invLog n)) := by
    linarith [pi_approx_final N]
  rw [h_sub]
  calc
    |psi_error N * invLog N +
        (-∑ n ∈ range N, psi_error (n + 1) * (invLog (n + 1) - invLog n))|
        ≤ |psi_error N * invLog N| +
          |-∑ n ∈ range N, psi_error (n + 1) * (invLog (n + 1) - invLog n)| :=
            abs_add_le _ _
    _ = |psi_error N * invLog N| +
          |∑ n ∈ range N, psi_error (n + 1) * (invLog (n + 1) - invLog n)| := by
            rw [abs_neg]
    _ ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) + C * 2 * Real.sqrt (N : ℝ) :=
          add_le_add (bound_error_eval C N₀ hC h_bound N hN) (h_sum N hN)

end DiscreteAbelChebyshev

