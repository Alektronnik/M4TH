/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import XiLogDeriv.GammaR

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

end

