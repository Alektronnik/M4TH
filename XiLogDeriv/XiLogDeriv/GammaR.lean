/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import XiLogDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# `Gammaℝ` logarithmic derivative and digamma API

This file proves the archimedean identity

`logDeriv Gammaℝ(s) = -1/2 * log π + 1/2 * digamma(s/2)`.
-/

@[expose] public section

open Complex Topology Filter

namespace RiemannLogDeriv

lemma Complex_Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (him : s.im ≠ 0) :
    Complex.Gammaℝ s ≠ 0 := by
  intro h
  rcases (Complex.Gammaℝ_eq_zero_iff (s := s)).mp h with ⟨n, hn⟩
  have him0 : s.im = 0 := by
    rw [hn]
    norm_cast
  exact him him0

lemma differentiableAt_Complex_Gammaℝ_of_ne_zero {s : ℂ} (hγ : Complex.Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  let f := fun t : ℂ => ((Complex.Gammaℝ t)⁻¹)⁻¹
  have hdiff : DifferentiableAt ℂ f s :=
    (Complex.differentiable_Gammaℝ_inv.differentiableAt).inv (inv_ne_zero hγ)
  have heq : f = Complex.Gammaℝ := funext fun t => by dsimp [f]; simp [inv_inv]
  rw [heq] at hdiff
  exact hdiff

lemma completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hγ : Complex.Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
  calc
    completedRiemannZeta s = Complex.Gammaℝ s * completedRiemannZeta s / Complex.Gammaℝ s :=
      (mul_div_cancel_left₀ (completedRiemannZeta s) hγ).symm
    _ = Complex.Gammaℝ s * riemannZeta s := by
      rw [riemannZeta_def_of_ne_zero hs0, mul_div_assoc]

lemma completedRiemannZeta_eq_mul_on_ne_zero {z : ℂ}
    (hz0 : z ≠ 0) (hγ : Complex.Gammaℝ z ≠ 0) :
    completedRiemannZeta z = Complex.Gammaℝ z * riemannZeta z :=
  completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta hz0 hγ

lemma completedRiemannZetaLogDeriv_eq_logDeriv_mul_of_ne_zero {s : ℂ}
    (hs0 : s ≠ 0) (hγ : Complex.Gammaℝ s ≠ 0) :
    logDeriv completedRiemannZeta s =
      logDeriv (fun z => Complex.Gammaℝ z * riemannZeta z) s := by
  have hγ_ev : ∀ᶠ z in 𝓝 s, Complex.Gammaℝ z ≠ 0 :=
    (differentiableAt_Complex_Gammaℝ_of_ne_zero hγ).continuousAt.eventually_ne hγ
  have hev : completedRiemannZeta =ᶠ[𝓝 s] fun z => Complex.Gammaℝ z * riemannZeta z := by
    filter_upwards [hγ_ev, continuous_id.continuousAt.eventually_ne hs0] with z hγz hz0
    exact completedRiemannZeta_eq_mul_on_ne_zero hz0 hγz
  have heq := completedRiemannZeta_eq_mul_on_ne_zero hs0 hγ
  rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, heq]

/-- Second-stage expansion `Λ'/Λ = Gammaℝ'/Gammaℝ + ζ'/ζ`. -/
theorem completedRiemannZetaLogDeriv_expansion_of_factors_ne_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hγ : Complex.Gammaℝ s ≠ 0)
    (hzeta : riemannZeta s ≠ 0) (_hΛ : completedRiemannZeta s ≠ 0) :
    completedRiemannZetaLogDeriv s = gammaRFactorLogDeriv s + riemannZetaLogDeriv s := by
  dsimp [completedRiemannZetaLogDeriv, gammaRFactorLogDeriv, riemannZetaLogDeriv]
  rw [completedRiemannZetaLogDeriv_eq_logDeriv_mul_of_ne_zero hs0 hγ,
    logDeriv_mul s hγ hzeta (differentiableAt_Complex_Gammaℝ_of_ne_zero hγ)
      (differentiableAt_riemannZeta hs1)]

lemma gammaRPiCpow_logDeriv (s : ℂ) :
    logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
      -(1 / 2) * log (Real.pi : ℂ) := by
  have hpine : (Real.pi : ℂ) ≠ 0 := by simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
  have hpow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [cpow_ne_zero_iff]
    exact Or.inl hpine
  have hdiff : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s :=
    ((differentiableAt_id.neg).div_const (2 : ℂ))
  have hderiv :
      deriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
        log (Real.pi : ℂ) * deriv (fun z : ℂ => -z / 2) s *
          (Real.pi : ℂ) ^ (-s / 2) := by
    simpa using Complex.deriv_const_cpow hdiff (c := (Real.pi : ℂ))
  dsimp [logDeriv, logDeriv_apply]
  rw [hderiv]
  have hfeq : (fun z : ℂ => -z / 2) = fun x : ℂ => (-id) x / 2 := by
    funext x
    simp [Pi.neg_apply, id_eq]
  have hAt := (((hasDerivAt_id s).neg).div_const (2 : ℂ)).deriv
  have hder : deriv (fun z : ℂ => -z / 2) s = -(1 / 2) := by
    rw [congrArg (fun g => deriv g s) hfeq, hAt]
    norm_num
  rw [hder]
  field_simp [hpow_ne]

lemma gamma_half_digamma_logDeriv {s : ℂ} (hγ : Gamma (s / 2) ≠ 0) :
    logDeriv (fun z : ℂ => Gamma (z / 2)) s = (1 / 2) * digamma (s / 2) := by
  let g : ℂ → ℂ := fun z => z / 2
  have hdiff : DifferentiableAt ℂ g s := differentiableAt_id.div_const (2 : ℂ)
  have hhs : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m hm
    exact hγ ((Gamma_eq_zero_iff (s := s / 2)).mpr ⟨m, hm⟩)
  have hΓ : DifferentiableAt ℂ Gamma (s / 2) := differentiableAt_Gamma (s / 2) hhs
  calc
    logDeriv (fun z => Gamma (z / 2)) s
        = logDeriv (Gamma ∘ g) s := rfl
    _ = logDeriv Gamma (g s) * deriv g s := by
          rw [logDeriv_comp (f := Gamma) (g := g) (x := s) hΓ hdiff]
    _ = digamma (s / 2) * (1 / 2) := by
          simp [g, logDeriv_apply, digamma_def, deriv_div_const, one_div]
    _ = (1 / 2) * digamma (s / 2) := by ring

/-- Digamma identity for the archimedean factor `Gammaℝ`. -/
theorem gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma {s : ℂ}
    (hγ : Complex.Gammaℝ s ≠ 0) :
    gammaRFactorLogDeriv s =
      -(1 / 2) * log (Real.pi : ℂ) + (1 / 2) * digamma (s / 2) := by
  rw [gammaRFactorLogDeriv]
  have hEqFun : Complex.Gammaℝ = fun z => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) :=
    funext Complex.Gammaℝ_def
  have hlog : logDeriv Complex.Gammaℝ s =
      logDeriv (fun z => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) s := by
    simp [hEqFun]
  rw [hlog]
  have hpine : (Real.pi : ℂ) ≠ 0 := by simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
  have hpow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [cpow_ne_zero_iff]
    exact Or.inl hpine
  have hhalf_ne : Gamma (s / 2) ≠ 0 := by
    intro h
    rw [Complex.Gammaℝ_def] at hγ
    exact hγ (mul_eq_zero.mpr (Or.inr h))
  have hdiff : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s :=
    ((differentiableAt_id.neg).div_const (2 : ℂ))
  have hhs : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m hm
    exact hhalf_ne ((Gamma_eq_zero_iff (s := s / 2)).mpr ⟨m, hm⟩)
  have gdiff : DifferentiableAt ℂ (fun z => z / 2) s := differentiableAt_id.div_const (2 : ℂ)
  have hdiffGamma : DifferentiableAt ℂ (fun z => Gamma (z / 2)) s :=
    (differentiableAt_Gamma (s / 2) hhs).comp s gdiff
  rw [logDeriv_mul s hpow_ne hhalf_ne
      (hdiff.const_cpow (Or.inl hpine)) hdiffGamma,
    gammaRPiCpow_logDeriv, gamma_half_digamma_logDeriv hhalf_ne]

end RiemannLogDeriv

end

