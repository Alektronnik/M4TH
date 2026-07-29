/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# Basic asymptotic objects for the Xi contour frontier

This file defines the classical Riemann-von Mangoldt main term and records the
package-local names used by the typed analytic frontier.
-/

@[expose] public section

open Complex Topology Filter Asymptotics

namespace RiemannAsymptoticFrontier

/-- Classical Riemann-von Mangoldt main term. -/
noncomputable def vonMangoldtMainTerm (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1)

/-- Simplified asymptotic equivalent main term. -/
noncomputable def vonMangoldtMainTermSimplified (T : ℝ) : ℝ :=
  T * Real.log T / (2 * Real.pi)

/-- Abstract multiplicity-counting function used by the frontier package.

The concrete zero-counting definition belongs to the zero-counting package.
This package only needs a function whose asymptotic behaviour is synthesized
from contour hypotheses.
-/
abbrev ZeroCountingFunction := ℝ → ℝ

/-- Normalized real part of a contour contribution. -/
noncomputable def contourNormalizedRealPart (z : ℂ) : ℝ :=
  (z / (2 * Real.pi * Complex.I)).re

lemma contourNormalizedRealPart_add (z w : ℂ) :
    contourNormalizedRealPart (z + w) =
      contourNormalizedRealPart z + contourNormalizedRealPart w := by
  dsimp [contourNormalizedRealPart]
  rw [add_div, Complex.add_re]

lemma contourNormalizedRealPart_sub (z w : ℂ) :
    contourNormalizedRealPart (z - w) =
      contourNormalizedRealPart z - contourNormalizedRealPart w := by
  dsimp [contourNormalizedRealPart]
  rw [sub_div, Complex.sub_re]

lemma contourNormalizedRealPart_neg (z : ℂ) :
    contourNormalizedRealPart (-z) = -contourNormalizedRealPart z := by
  dsimp [contourNormalizedRealPart]
  rw [neg_div, Complex.neg_re]

lemma contourNormalizedRealPart_of_real_mul_I (x : ℝ) :
    contourNormalizedRealPart (2 * Real.pi * Complex.I * x) = x := by
  dsimp [contourNormalizedRealPart]
  field_simp [Complex.two_pi_I_ne_zero]
  simp [ofReal_re]

lemma abs_contourNormalizedRealPart_le_norm_div (z : ℂ) :
    |contourNormalizedRealPart z| ≤ ‖z‖ / (2 * Real.pi) := by
  dsimp [contourNormalizedRealPart]
  calc
    |(z / (2 * Real.pi * Complex.I)).re| ≤ ‖z / (2 * Real.pi * Complex.I)‖ :=
      Complex.abs_re_le_norm _
    _ = ‖z‖ / ‖(2 * Real.pi * Complex.I : ℂ)‖ := Complex.norm_div z _
    _ = ‖z‖ / (2 * Real.pi) := by
      simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]

end RiemannAsymptoticFrontier
