/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic

/-!
# XiLogDeriv.live

Single-file live fusion of the public `XiLogDeriv` package.
This file is self-contained for Lean Web inspection and does not import package-local modules.
-/


/-!
## Source file: `XiLogDeriv/Basic.lean`
-/



/-!
# Basic Xi and log-derivative infrastructure

This file isolates the package-local definitions used to expand the logarithmic
derivative of the entire Riemann Xi variant.  The namespace is deliberately
package-specific so that this standalone package can coexist with the sibling
`ZetaZeroCounting` package in the same Lake workspace.
-/

@[expose] public section

open Complex Topology Filter

namespace RiemannLogDeriv

/-- The entire Xi variant used for critical-box contour arguments. -/
noncomputable def entireXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

/-- The polynomial factor `s(s-1)` in the completed-zeta factorization. -/
noncomputable def entireXiPolynomialFactor (s : ℂ) : ℂ :=
  s * (s - 1)

/-- Logarithmic derivative of the entire Xi variant. -/
noncomputable def entireXiLogDeriv (s : ℂ) : ℂ :=
  logDeriv entireXi s

/-- Logarithmic derivative of the polynomial factor `s(s-1)`. -/
noncomputable def entireXiPolynomialLogDeriv (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1)

/-- Logarithmic derivative of the completed zeta factor. -/
noncomputable def completedRiemannZetaLogDeriv (s : ℂ) : ℂ :=
  logDeriv completedRiemannZeta s

/-- Logarithmic derivative of the archimedean `Gammaℝ` factor. -/
noncomputable def gammaRFactorLogDeriv (s : ℂ) : ℂ :=
  logDeriv Complex.Gammaℝ s

/-- Classical logarithmic derivative of the Riemann zeta function. -/
noncomputable def riemannZetaLogDeriv (s : ℂ) : ℂ :=
  logDeriv riemannZeta s

lemma entireXiPolynomialFactor_eq (s : ℂ) :
    entireXiPolynomialFactor s = s * (s - 1) :=
  rfl

lemma entireXiLogDeriv_apply (s : ℂ) :
    entireXiLogDeriv s = deriv entireXi s / entireXi s :=
  logDeriv_apply entireXi s

lemma xi_polynomial_factor_ne_zero_of_ne_zero_ne_one {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s * (s - 1) ≠ 0 :=
  mul_ne_zero hs0 (sub_ne_zero.mpr hs1)

lemma differentiable_entireXi : Differentiable ℂ entireXi := by
  unfold entireXi
  exact ((differentiable_id.mul (differentiable_id.sub (differentiable_const (1 : ℂ)))).mul
    differentiable_completedZeta₀).add (differentiable_const (1 : ℂ))

lemma continuous_entireXi : Continuous entireXi :=
  differentiable_entireXi.continuous

lemma entireXi_ne_zero_at_zero : entireXi 0 ≠ 0 := by
  simp [entireXi]

lemma entireXi_ne_zero_at_one : entireXi 1 ≠ 0 := by
  simp [entireXi]

lemma analyticAt_entireXi (s : ℂ) : AnalyticAt ℂ entireXi s :=
  ((analyticOnNhd_univ_iff_differentiable).2 differentiable_entireXi) s (Set.mem_univ s)

/-- The entire Xi variant equals `s(s-1) completedRiemannZeta s` away from `0` and `1`. -/
lemma entireXi_eq_polynomial_times_completedZeta_of_ne_zero_ne_one {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireXi s = s * (s - 1) * completedRiemannZeta s := by
  have h_mathlib : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
    completedRiemannZeta_eq s
  have h_div1 : s * (s - 1) / s = s - 1 := by
    calc s * (s - 1) / s
      _ = (s - 1) * s / s := by ring
      _ = s - 1 := mul_div_cancel_right₀ (s - 1) hs0
  have h_div2 : s * (s - 1) / (1 - s) = -s := by
    have h_ne_one_sub : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
    calc s * (s - 1) / (1 - s)
      _ = -s * (1 - s) / (1 - s) := by ring
      _ = -s := mul_div_cancel_right₀ (-s) h_ne_one_sub
  calc
    entireXi s = s * (s - 1) * completedRiemannZeta₀ s + 1 := rfl
    _ = s * (s - 1) * completedRiemannZeta₀ s - (s - 1) + s := by ring
    _ = s * (s - 1) * completedRiemannZeta₀ s - s * (s - 1) / s -
        s * (s - 1) / (1 - s) := by
      rw [h_div1, h_div2]
      ring
    _ = s * (s - 1) * (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) := by ring
    _ = s * (s - 1) * completedRiemannZeta s := by rw [← h_mathlib]

lemma entireXi_eq_polynomial_mul_completedZeta_on_compl {z : ℂ}
    (hz : z ∈ ({0, 1} : Set ℂ)ᶜ) :
    entireXi z = entireXiPolynomialFactor z * completedRiemannZeta z := by
  have hz0 : z ≠ 0 := fun h => hz (Or.inl h)
  have hz1 : z ≠ 1 := fun h => hz (Or.inr h)
  exact entireXi_eq_polynomial_times_completedZeta_of_ne_zero_ne_one hz0 hz1

lemma logDeriv_linear_sub_one (s : ℂ) (_hs : s ≠ 1) :
    logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
  simp [logDeriv_apply, deriv_const, one_div]

lemma logDeriv_entireXiPolynomialFactor_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv entireXiPolynomialFactor s = 1 / s + 1 / (s - 1) := by
  rw [show entireXiPolynomialFactor = fun z => z * (z - 1) from
    funext entireXiPolynomialFactor_eq]
  have hmul := logDeriv_mul (f := fun w => w) (g := fun w => w - 1) s hs0
    (sub_ne_zero.mpr hs1) differentiableAt_id
    ((differentiableAt_id).sub (differentiableAt_const 1))
  rw [hmul, show logDeriv (fun w => w) = logDeriv id from funext fun _ => rfl,
    logDeriv_id, logDeriv_linear_sub_one s hs1]

lemma entireXiLogDeriv_eq_logDeriv_mul_completed_of_ne_zero_ne_one {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv entireXi s =
      logDeriv (fun z => entireXiPolynomialFactor z * completedRiemannZeta z) s := by
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (isClosed_singleton.union isClosed_singleton).isOpen_compl
  have hs_mem : s ∈ ({0, 1} : Set ℂ)ᶜ := by
    simpa [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using ⟨hs0, hs1⟩
  have hev : entireXi =ᶠ[𝓝 s] fun z => entireXiPolynomialFactor z * completedRiemannZeta z := by
    filter_upwards [hopen.mem_nhds hs_mem] with z hz using
      entireXi_eq_polynomial_mul_completedZeta_on_compl hz
  have heq : entireXi s = entireXiPolynomialFactor s * completedRiemannZeta s :=
    entireXi_eq_polynomial_mul_completedZeta_on_compl hs_mem
  rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, heq]

/-- First-stage expansion `ξ'/ξ = 1/s + 1/(s-1) + Λ'/Λ`. -/
theorem entireXiLogDeriv_expansion_of_ne_zero_ne_one {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (_hξ : entireXi s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) :
    entireXiLogDeriv s = 1 / s + 1 / (s - 1) + completedRiemannZetaLogDeriv s := by
  dsimp only [entireXiLogDeriv, completedRiemannZetaLogDeriv]
  have hpoly : entireXiPolynomialFactor s ≠ 0 :=
    xi_polynomial_factor_ne_zero_of_ne_zero_ne_one hs0 hs1
  rw [entireXiLogDeriv_eq_logDeriv_mul_completed_of_ne_zero_ne_one hs0 hs1,
    logDeriv_mul s hpoly hΛ
      ((differentiableAt_id).mul ((differentiableAt_id).sub (differentiableAt_const 1)))
      (differentiableAt_completedZeta hs0 hs1),
    logDeriv_entireXiPolynomialFactor_eq hs0 hs1]

end RiemannLogDeriv



/-!
## Source file: `XiLogDeriv/GammaR.lean`
-/



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



/-!
## Source file: `XiLogDeriv/DigammaContinuity.lean`
-/



/-!
# Continuity wrappers for `digamma`

This file packages the continuity facts for `Complex.digamma` that are useful
on positive real half-lines and on horizontal/vertical contour edges with
nonzero imaginary part.
-/

@[expose] public section

open Complex Topology Filter

namespace RiemannLogDeriv

lemma digamma_continuousAt_of_ne_neg_nat {z : ℂ} (hz : ∀ m : ℕ, z ≠ -↑m) :
    ContinuousAt Complex.digamma z := by
  have hΓ := differentiableAt_Gamma z hz
  have hγne : Gamma z ≠ 0 := Gamma_ne_zero hz
  have han : AnalyticAt ℂ Gamma z :=
    (Meromorphic.Gamma z).analyticAt (continuousAt_Gamma z hz)
  have hderiv : DifferentiableAt ℂ (deriv Gamma) z :=
    ((han.contDiffAt (n := 2)).derivWithin (m := 1)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
      (by norm_num)
  have hdiff : DifferentiableAt ℂ Complex.digamma z := by
    rw [Complex.digamma_def]
    exact DifferentiableAt.div hderiv hΓ hγne
  exact hdiff.continuousAt

lemma digamma_continuousAt_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    ContinuousAt Complex.digamma z :=
  digamma_continuousAt_of_ne_neg_nat (by
    intro m hm
    have := congrArg Complex.im hm
    simp at this
    exact hz this)

lemma digamma_ne_neg_nat_of_real_half_pos {t : ℝ} (ht : 0 < t) :
    ∀ n : ℕ, (t : ℂ) / 2 ≠ -↑n := by
  intro n hn
  have hre : 0 < ((t : ℂ) / 2).re := by
    simp [Complex.ofReal_re]
    linarith [ht]
  rcases n with _ | n
  · have hre0 : ((t : ℂ) / 2).re = 0 := by
      simpa [Complex.div_re, Complex.ofReal_re] using congrArg Complex.re hn
    linarith [hre]
  · have := congrArg Complex.re hn
    simp [Complex.ofReal_re, Complex.neg_re] at this
    linarith [hre]

lemma digamma_continuousAt_real_half_pos {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun (r : ℝ) => Complex.digamma ((r : ℂ) / (2 : ℂ))) t := by
  refine ContinuousAt.comp ?_ ?_
  · exact digamma_continuousAt_of_ne_neg_nat (digamma_ne_neg_nat_of_real_half_pos ht)
  · exact (continuous_ofReal.div_const (2 : ℂ)).continuousAt

lemma digamma_comp_real_half_continuousOn_Ioo :
    ContinuousOn (fun (t : ℝ) => Complex.digamma ((t : ℂ) / (2 : ℂ)))
      (Set.Ioo (0 : ℝ) 1) :=
  continuousOn_of_forall_continuousAt fun _ ht => digamma_continuousAt_real_half_pos ht.1

lemma digamma_continuousOn_of_forall_im_ne_zero {S : Set ℂ}
    (him : ∀ z ∈ S, z.im ≠ 0) :
    ContinuousOn Complex.digamma S :=
  continuousOn_of_forall_continuousAt fun z hz => digamma_continuousAt_of_im_ne_zero (him z hz)

lemma continuousOn_topEdgeParam {T : ℝ} :
    ContinuousOn (fun (t : ℝ) => (t : ℂ) + (T : ℂ) * I) (Set.Icc (0 : ℝ) (1 : ℝ)) :=
  ((continuous_ofReal : Continuous fun t : ℝ => (t : ℂ)).add
      (continuous_const : Continuous fun _ : ℝ => (T : ℂ) * I)).continuousOn

lemma digamma_comp_half_continuousOn_Icc {g : ℝ → ℂ} {S : Set ℝ}
    (hg : ContinuousOn g S) (hpos : ∀ y ∈ S, 0 < (g y).im) :
    ContinuousOn (fun y => Complex.digamma (g y)) S := by
  have him : ∀ z ∈ Set.image g S, z.im ≠ 0 := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact (hpos y hy).ne'
  have hψ := digamma_continuousOn_of_forall_im_ne_zero him
  exact hψ.comp hg (by intro x hx; exact ⟨x, hx, rfl⟩)

lemma digamma_top_edge_continuousOn_Icc {T : ℝ} (hT : 0 < T) :
    ContinuousOn
      (fun (t : ℝ) => Complex.digamma (((t : ℂ) + (T : ℂ) * I) / 2))
      (Set.Icc (0 : ℝ) (1 : ℝ)) :=
  digamma_comp_half_continuousOn_Icc
    (ContinuousOn.div_const continuousOn_topEdgeParam (2 : ℂ))
    (by
      intro t ht
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im]
      linarith [hT])

lemma digamma_right_tail_continuousOn_Icc (T : ℝ) :
    ContinuousOn (fun (y : ℝ) => Complex.digamma ((1 + (y : ℂ) * I) / 2))
      (Set.Icc (1 : ℝ) T) := by
  set g := fun y : ℝ => (1 + (y : ℂ) * I) / 2
  have hg : ContinuousOn g (Set.Icc (1 : ℝ) T) := by
    unfold g
    exact ContinuousOn.div_const
      (((continuous_const : Continuous fun (_ : ℝ) => (1 : ℂ)).add
          (continuous_ofReal.mul continuous_const)).continuousOn)
      (2 : ℂ)
  exact digamma_comp_half_continuousOn_Icc hg (by
    intro y hy
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im]
    linarith [hy.1])

lemma digamma_left_tail_continuousOn_Icc (T : ℝ) :
    ContinuousOn (fun (y : ℝ) => Complex.digamma (((y : ℂ) * I) / 2))
      (Set.Icc (1 : ℝ) T) := by
  set g := fun y : ℝ => ((y : ℂ) * I) / 2
  have hg : ContinuousOn g (Set.Icc (1 : ℝ) T) := by
    unfold g
    exact ContinuousOn.div_const ((continuous_ofReal.mul continuous_const).continuousOn) 2
  exact digamma_comp_half_continuousOn_Icc hg (by
    intro y hy
    simp [Complex.mul_im, Complex.ofReal_im]
    linarith [hy.1])

end RiemannLogDeriv



/-!
## Source file: `XiLogDeriv/Expansion.lean`
-/



/-!
# Full logarithmic-derivative expansion of Xi

This file combines the polynomial, `Gammaℝ`, and zeta logarithmic derivative
components.  Boundary-specific applications can supply the required nonzero
denominators from safe-height or contour hypotheses.
-/

@[expose] public section

open Complex Topology Filter

namespace RiemannLogDeriv

/-- The full decomposition
`ξ'/ξ = 1/s + 1/(s-1) + Gammaℝ'/Gammaℝ + ζ'/ζ`.
-/
theorem entireXiLogDeriv_full_expansion_of_factors_ne_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hξ : entireXi s ≠ 0)
    (hγ : Complex.Gammaℝ s ≠ 0) (hzeta : riemannZeta s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) :
    entireXiLogDeriv s =
      1 / s + 1 / (s - 1) + gammaRFactorLogDeriv s + riemannZetaLogDeriv s := by
  rw [entireXiLogDeriv_expansion_of_ne_zero_ne_one hs0 hs1 hξ hΛ,
    completedRiemannZetaLogDeriv_expansion_of_factors_ne_zero hs0 hs1 hγ hzeta hΛ]
  ring

/-- Regular-boundary form with the nonvanishing hypotheses exposed explicitly. -/
theorem entireXiLogDeriv_full_expansion_on_regular_boundary {T : ℝ} {s : ℂ}
    (hs_boundary : s ∈
      ({z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ z.im = T} ∪
        {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ z.im = 0} ∪
        {z : ℂ | z.re = 0 ∧ 0 ≤ z.im ∧ z.im ≤ T} ∪
        {z : ℂ | z.re = 1 ∧ 0 ≤ z.im ∧ z.im ≤ T}))
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hξ : entireXi s ≠ 0)
    (hγ : Complex.Gammaℝ s ≠ 0) (hzeta : riemannZeta s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) :
    entireXiLogDeriv s =
      entireXiPolynomialLogDeriv s + gammaRFactorLogDeriv s + riemannZetaLogDeriv s := by
  have _ := hs_boundary
  rw [entireXiPolynomialLogDeriv]
  exact entireXiLogDeriv_full_expansion_of_factors_ne_zero hs0 hs1 hξ hγ hzeta hΛ

/-- Digamma-substituted full decomposition of the Xi logarithmic derivative. -/
theorem entireXiLogDeriv_full_expansion_with_digamma {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hξ : entireXi s ≠ 0)
    (hγ : Complex.Gammaℝ s ≠ 0) (hzeta : riemannZeta s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) :
    entireXiLogDeriv s =
      entireXiPolynomialLogDeriv s -
        (1 / 2) * log (Real.pi : ℂ) +
        (1 / 2) * digamma (s / 2) +
        riemannZetaLogDeriv s := by
  rw [entireXiLogDeriv_full_expansion_of_factors_ne_zero hs0 hs1 hξ hγ hzeta hΛ,
    gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma hγ,
    entireXiPolynomialLogDeriv]
  ring

end RiemannLogDeriv



end
