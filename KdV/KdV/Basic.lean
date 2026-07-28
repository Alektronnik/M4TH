/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-!
# The Korteweg-de Vries equation

This file contains the basic smooth solution predicate for the one-dimensional
KdV equation

`u_t + u u_x + u_xxx = 0`

and the elementary chain-rule lemmas for travelling waves `u(t, x) = f (x - c t)`.

## Main definitions

- `KdV.IsSolution`: smooth solutions of KdV on `[0, T)`.
- `KdV.TravellingWave`: a three-times differentiable travelling-wave profile.

## Main results

- `KdV.travellingWave_reduction`: a travelling-wave KdV solution satisfies the
  stationary soliton ODE `-c f' + f f' + f''' = 0`.

## Implementation notes

This file uses the Mathlib-style predicate `IsSolution T u` for smooth KdV
solutions, keeping the solution regularity and the PDE identity explicit.

## Tags

KdV equation, travelling wave, soliton, PDE
-/

@[expose] public section

namespace KdV

set_option maxHeartbeats 600000

/-- Smooth solutions of the one-dimensional KdV equation
`u_t + u u_x + u_xxx = 0` on the time interval `[0, T)`. -/
structure IsSolution (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  differentiable : Differentiable ℝ (fun p : ℝ × ℝ => u p.1 p.2)
  differentiable_dx : ∀ t, Differentiable ℝ (fun x => deriv (u t) x)
  differentiable_dxx : ∀ t, Differentiable ℝ (fun y => deriv (fun x => deriv (u t) x) y)
  pde : ∀ t ∈ Set.Ico 0 T, ∀ x,
    deriv (fun s => u s x) t + u t x * deriv (u t) x +
      deriv (fun y => deriv (fun z => deriv (u t) z) y) x = 0

/-- A three-times differentiable travelling-wave profile.  The wave speed is
kept in the structure parameter because later files use the same profile in the
ansatz `u(t, x) = f (x - c t)`. -/
structure TravellingWave (c : ℝ) where
  profile : ℝ → ℝ
  differentiable : Differentiable ℝ profile
  differentiable_deriv : Differentiable ℝ (fun x => deriv profile x)
  differentiable_deriv2 : Differentiable ℝ (fun y => deriv (fun x => deriv profile x) y)

/-- Time derivative of a travelling-wave ansatz. -/
lemma travellingWave_deriv_time (f : ℝ → ℝ) (c t x : ℝ) :
    deriv (fun s => f (x - c * s)) t = -c * deriv f (x - c * t) := by
  calc
    deriv (fun s => f (x - c * s)) t =
        c * deriv (fun y => f (x - y)) (c * t) := by
      simpa only [smul_eq_mul] using
        deriv_comp_mul_left c (fun y => f (x - y)) t
    _ = -c * deriv f (x - c * t) := by
      rw [deriv_comp_const_sub]
      ring

/-- Spatial derivative of a travelling-wave ansatz. -/
lemma travellingWave_deriv_space (f : ℝ → ℝ) (c t x : ℝ) :
    deriv (fun y => f (y - c * t)) x = deriv f (x - c * t) := by
  exact deriv_comp_sub_const f (c * t) x

/-- Third spatial derivative of a travelling-wave ansatz. -/
lemma travellingWave_deriv_space3 (f : ℝ → ℝ) (c t x : ℝ) :
    deriv (fun y => deriv (fun z => deriv (fun w => f (w - c * t)) z) y) x =
      deriv (fun y => deriv (fun z => deriv f z) y) (x - c * t) := by
  rw [show (fun w => f (w - c * t)) = fun w => f (w - (c * t)) by rfl]
  simp_rw [deriv_comp_sub_const]

/-- Travelling-wave reduction of KdV to the stationary soliton ODE. -/
theorem travellingWave_reduction {T : ℝ} {u : ℝ → ℝ → ℝ} (sol : IsSolution T u)
    (c : ℝ) (wave : TravellingWave c)
    (h_wave : ∀ t x, u t x = wave.profile (x - c * t))
    (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : ℝ) :
    -c * deriv wave.profile (x - c * t) +
      wave.profile (x - c * t) * deriv wave.profile (x - c * t) +
      deriv (fun y => deriv (fun z => deriv wave.profile z) y) (x - c * t) = 0 := by
  have h_pde := sol.pde t ht x
  have h_u_eq : u = fun t x => wave.profile (x - c * t) := by
    ext t' x'
    exact h_wave t' x'
  rw [h_u_eq] at h_pde
  have h_ut := travellingWave_deriv_time wave.profile c t x
  have h_ux := travellingWave_deriv_space wave.profile c t x
  have h_uxxx := travellingWave_deriv_space3 wave.profile c t x
  dsimp at h_pde
  rw [h_ut, h_ux, h_uxxx] at h_pde
  exact h_pde

end KdV

end
