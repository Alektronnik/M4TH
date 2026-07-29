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
import Mathlib.Tactic

/-!
# Discrete Abel summation

This file proves a finite Abel summation identity for partial sums of a real
sequence and records the `1 / log n` weight used in the Chebyshev-to-prime
counting bridge.
-/

@[expose] public section

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
