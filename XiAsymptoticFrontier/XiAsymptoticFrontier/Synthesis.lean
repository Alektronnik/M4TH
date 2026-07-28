/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import XiAsymptoticFrontier.Frontier

/-!
# Conditional synthesis of Riemann-von Mangoldt

This file proves that the typed analytic frontier implies the asymptotic
zero-counting theorem.  All analytic estimates are hypotheses of
`AnalyticFrontier`; no trusted declarations are introduced.
-/

@[expose] public section

open Complex Topology Filter Asymptotics

namespace RiemannAsymptoticFrontier

/-- Multiplicity-counting Riemann-von Mangoldt statement for an abstract zero-counting function. -/
def RiemannVonMangoldtMultiplicityCounting (N : ZeroCountingFunction) : Prop :=
  IsEquivalent atTop N vonMangoldtMainTerm

/-- Safe-height counting follows the main term once the gamma term is dominant
and all other contour terms are negligible. -/
theorem safe_counting_equiv_main {Nsafe : ZeroCountingFunction} {C : ContourComponents}
    (hReconstruct : C.reconstructs Nsafe)
    (hGamma : GammaHorizontalStirlingGoal C)
    (hResidual : C.residual =o[atTop] vonMangoldtMainTerm) :
    IsEquivalent atTop Nsafe vonMangoldtMainTerm := by
  have hsum : IsEquivalent atTop (fun T => C.gammaHorizontal T + C.residual T)
      vonMangoldtMainTerm :=
    IsEquivalent.add_isLittleO hGamma hResidual
  exact hsum.congr_left (Filter.EventuallyEq.symm hReconstruct)

/-- The typed analytic frontier implies Riemann-von Mangoldt for `Nsafe`. -/
theorem safe_riemann_von_mangoldt_from_frontier {N Nsafe : ZeroCountingFunction}
    {C : ContourComponents} (h : AnalyticFrontier N Nsafe C) :
    RiemannVonMangoldtMultiplicityCounting Nsafe := by
  dsimp [RiemannVonMangoldtMultiplicityCounting]
  exact safe_counting_equiv_main h.reconstructs_safe h.gamma_horizontal
    (residual_negligible h.near_origin h.polynomial h.gamma_vertical h.zeta_edges)

/-- The typed analytic frontier implies Riemann-von Mangoldt for the original count. -/
theorem riemann_von_mangoldt_from_contour_frontier {N Nsafe : ZeroCountingFunction}
    {C : ContourComponents} (h : AnalyticFrontier N Nsafe C) :
    RiemannVonMangoldtMultiplicityCounting N := by
  exact h.safe_height_counting.trans (safe_riemann_von_mangoldt_from_frontier h)

/-- Package-level conditional statement. -/
def RiemannVonMangoldtFromContourFrontier : Prop :=
  ∀ {N Nsafe : ZeroCountingFunction} {C : ContourComponents},
    AnalyticFrontier N Nsafe C → RiemannVonMangoldtMultiplicityCounting N

theorem riemann_von_mangoldt_from_contour_bridge :
    RiemannVonMangoldtFromContourFrontier := by
  intro N Nsafe C h
  exact riemann_von_mangoldt_from_contour_frontier h

end RiemannAsymptoticFrontier
