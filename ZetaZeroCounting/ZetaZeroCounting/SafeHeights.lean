/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import ZetaZeroCounting.ZeroCounting

/-!
# Safe heights for the critical box

A height `T` is **safe** when no nontrivial zero of zeta has imaginary part
exactly `T`: the top edge of the critical box does not pass through a zero.
Since the zeros with `0 < Im ≤ H` form a finite set, their imaginary parts are
a finite set of *forbidden heights*, and safe heights are dense above any
positive threshold: every interval `(T, T + ε]` contains one
(`exists_safe_height_in_interval`), so in particular safe heights exist above
`T` and within distance one of `T`.

This is the geometric input that makes contour arguments over the box
well-posed: at a safe height the Xi functions do not vanish on the top edge,
and — unconditionally, via Mathlib's zero-free region transported by the
functional equation — they do not vanish on the vertical edges away from the
corners either.  (Nonvanishing on the *bottom* edge requires the
nonvanishing of `ζ` on the real interval `(0,1)`, which belongs to the
Dirichlet-eta package.)

## Main definitions

- `Riemann.IsSafeHeight`, `Riemann.forbiddenHeights`.

## Main results

- `Riemann.exists_safe_height_in_interval`,
  `Riemann.exists_safe_height_above`,
  `Riemann.exists_safe_height_within_one`.
- `Riemann.zerosUpToIm_subset_criticalBoxInterior`: at a safe height, the
  counted zeros lie strictly inside the box.
- `Riemann.riemannXi_ne_zero_on_top_edge_of_safeHeight`,
  `Riemann.entireXi_ne_zero_on_top_edge_of_safeHeight`,
  `Riemann.riemannXi_ne_zero_on_right_edge`,
  `Riemann.riemannXi_ne_zero_on_left_edge`.

## Tags

Riemann zeta, safe height, critical strip, zero-free region
-/

@[expose] public section

open Complex Set

namespace Riemann

/-- Safe height: no nontrivial zero has `Im = T` (the top edge of the box does
not pass through a zero). -/
def IsSafeHeight (T : ℝ) : Prop :=
  ∀ s ∈ nontrivialZeros, s.im ≠ T

lemma isSafeHeight_iff_top_edge_no_nontrivial_zero {T : ℝ} :
    IsSafeHeight T ↔ ∀ s ∈ criticalBoxTopEdge T, s ∉ nontrivialZeros := by
  constructor
  · intro hT s hs hs_zero
    exact hT s hs_zero hs.2.2
  · intro h s hs_zero him
    have hs_top : s ∈ criticalBoxTopEdge T := by
      simp [criticalBoxTopEdge, hs_zero.2.1.le, hs_zero.2.2.le, him]
    exact h s hs_top hs_zero

/-- At a safe height, the counted zeros lie strictly in the interior of the
box. -/
theorem zerosUpToIm_subset_criticalBoxInterior {T : ℝ} (hSafe : IsSafeHeight T) :
    zerosUpToIm T ⊆ criticalBoxInterior T := by
  intro s hs
  simp only [criticalBoxInterior, zerosUpToIm, nontrivialZeros, Set.mem_setOf_eq] at hs ⊢
  rcases hs with ⟨⟨hzeta, hre₁, hre₂⟩, himpos, himle⟩
  have hz : s ∈ nontrivialZeros := ⟨hzeta, hre₁, hre₂⟩
  refine ⟨hre₁, hre₂, himpos, lt_of_le_of_ne himle (hSafe s hz)⟩

/-- `ξ` does not vanish on the top edge of a safe-height box (interior of the
strip). -/
lemma riemannXi_ne_zero_on_top_edge_of_safeHeight {T : ℝ} (_hT : 0 < T) (hSafe : IsSafeHeight T)
    {s : ℂ} (hs : s ∈ criticalBoxTopEdge T) (hs_re : 0 < s.re ∧ s.re < 1) :
    riemannXi s ≠ 0 := by
  intro hzero
  have hzeta : riemannZeta s = 0 := by
    dsimp [riemannXi] at hzero
    have hpoly : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
      xi_polynomial_ne_zero s hs_re
    have hcomp : completedRiemannZeta s = 0 := by
      rw [mul_eq_zero] at hzero
      cases hzero with
      | inl h => exact (hpoly h).elim
      | inr h => exact h
    exact (completedRiemannZeta_zero_iff s hs_re).mpr hcomp
  exact (isSafeHeight_iff_top_edge_no_nontrivial_zero.mp hSafe) s hs
    ⟨hzeta, hs_re⟩

/-- `entireXi` does not vanish on the top edge of a safe-height box (interior
of the strip, away from the corners). -/
lemma entireXi_ne_zero_on_top_edge_of_safeHeight {T : ℝ} (_hT : 0 < T) (hSafe : IsSafeHeight T)
    {s : ℂ} (hs : s ∈ criticalBoxTopEdge T) (hs_re : 0 < s.re ∧ s.re < 1)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireXi s ≠ 0 := by
  intro hzero
  have hpoly : s * (s - 1) ≠ 0 :=
    xi_polynomial_factor_ne_zero_of_ne_zero_ne_one hs0 hs1
  have hcomp : completedRiemannZeta s = 0 := by
    have heq := entireXi_eq_mul_completedRiemannZeta hs0 hs1
    rw [heq] at hzero
    rw [mul_eq_zero] at hzero
    cases hzero with
    | inl h => exact (hpoly h).elim
    | inr h => exact h
  have hzeta : riemannZeta s = 0 :=
    (completedRiemannZeta_zero_iff s hs_re).mpr hcomp
  exact (isSafeHeight_iff_top_edge_no_nontrivial_zero.mp hSafe) s hs ⟨hzeta, hs_re⟩

/-! ### Forbidden heights and density of safe heights -/

/-- The imaginary parts of the zeros with `0 < Im ≤ H`: a finite set of
forbidden heights. -/
noncomputable def forbiddenHeights (H : ℝ) : Finset ℝ :=
  (zerosUpToIm_finite H).toFinset.image (fun (s : ℂ) => s.im)

lemma mem_forbiddenHeights_iff {H t : ℝ} :
    t ∈ forbiddenHeights H ↔ ∃ s ∈ zerosUpToIm H, s.im = t := by
  simp [forbiddenHeights, Finset.mem_image, Set.Finite.mem_toFinset]

lemma nontrivialZero_im_mem_forbiddenHeights {H : ℝ} {s : ℂ}
    (hs : s ∈ nontrivialZeros) (hpos : 0 < s.im) (hle : s.im ≤ H) :
    s.im ∈ forbiddenHeights H := by
  rw [mem_forbiddenHeights_iff]
  exact ⟨s, ⟨hs, hpos, hle⟩, rfl⟩

/-- **Density of safe heights**: every interval `(T, T + ε]` contains a safe
height, because only finitely many heights are forbidden while the interval
is infinite. -/
theorem exists_safe_height_in_interval (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
    ∃ T', T < T' ∧ T' ≤ T + ε ∧ IsSafeHeight T' := by
  set F := forbiddenHeights (T + ε)
  have he : T < T + ε := by linarith
  have hInfinite : (Set.Ioo T (T + ε)).Infinite := Set.Ioo_infinite he
  have hExist : ∃ T', T' ∈ Set.Ioo T (T + ε) ∧ T' ∉ (F : Set ℝ) := by
    by_contra hall
    push Not at hall
    have hsub : Set.Ioo T (T + ε) ⊆ (F : Set ℝ) := fun x hx => hall x hx
    have hFin : (F : Set ℝ).Finite := F.finite_toSet
    exact hInfinite.not_finite (hFin.subset hsub)
  obtain ⟨T', hT', hT'not⟩ := hExist
  refine ⟨T', hT'.1, hT'.2.le, ?_⟩
  intro s hs him
  have him_in : T' ∈ forbiddenHeights (T + ε) := by
    rw [mem_forbiddenHeights_iff]
    refine ⟨s, ⟨hs, ?_, ?_⟩, him⟩
    · linarith [him, hT'.1]
    · linarith [him, hT'.2]
  exact hT'not him_in

/-- For every `T > 0` there is a safe height `T' ≥ T`. -/
theorem exists_safe_height_above (T : ℝ) (hT : 0 < T) :
    ∃ T', T ≤ T' ∧ IsSafeHeight T' := by
  obtain ⟨T', h₁, _, h₂⟩ := exists_safe_height_in_interval T 1 hT one_pos
  exact ⟨T', le_of_lt h₁, h₂⟩

/-- For every `T > 0` there is a safe height in `[T, T + 1]`.  The pinching
`T ≤ T' ≤ T + 1` is what the asymptotic layer of the counting formula needs. -/
theorem exists_safe_height_within_one (T : ℝ) (hT : 0 < T) :
    ∃ T', T ≤ T' ∧ T' ≤ T + 1 ∧ IsSafeHeight T' := by
  obtain ⟨T', hlt, hle, hSafe⟩ := exists_safe_height_in_interval T 1 hT one_pos
  exact ⟨T', le_of_lt hlt, hle, hSafe⟩

/-! ### Vertical edges: unconditional nonvanishing away from the corners

On `Re = 1` Mathlib's zero-free region applies directly; on `Re = 0` it is
transported by the functional equation.  Both edges are therefore zero-free
for `ξ` away from the corners, with no hypotheses on the height. -/

/-- Nontrivial zeros never lie on the vertical lines `Re = 0` or `Re = 1`. -/
lemma nontrivialZeros_not_on_vertical_edges {s : ℂ} (hs : s ∈ nontrivialZeros) :
    s ∉ criticalBoxLeftEdge 0 ∧ s ∉ criticalBoxRightEdge 0 := by
  constructor
  · intro h
    have : s.re = 0 := h.1
    linarith [hs.2.1, this]
  · intro h
    have : s.re = 1 := h.1
    linarith [hs.2.2, this]

theorem riemannXi_ne_zero_on_right_edge {T : ℝ} {s : ℂ}
    (hs : s ∈ criticalBoxRightEdge T) (him : s.im ≠ 0) :
    riemannXi s ≠ 0 := by
  have hs1 : s.re = 1 := hs.1
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h] at him
    simp at him
  have hs_ne_zero : s ≠ 0 := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  have hpoly : s * (s - 1) ≠ 0 :=
    xi_polynomial_factor_ne_zero_of_ne_zero_ne_one hs_ne_zero hs_ne_one
  have hcomp := completedRiemannZeta_ne_zero_of_re_eq_one hs1
  have hfactor : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
    simpa [mul_assoc] using mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) hpoly
  dsimp [riemannXi]
  exact mul_ne_zero hfactor hcomp

theorem riemannXi_ne_zero_on_left_edge {T : ℝ} {s : ℂ}
    (hs : s ∈ criticalBoxLeftEdge T) (hs0 : s ≠ 0) :
    riemannXi s ≠ 0 := by
  have hr : s.re = 0 := hs.1
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h] at hr
    simp at hr
  have hpoly : s * (s - 1) ≠ 0 :=
    xi_polynomial_factor_ne_zero_of_ne_zero_ne_one hs0 hs_ne_one
  have hcomp := completedRiemannZeta_ne_zero_of_re_eq_zero hr hs0
  have hfactor : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
    simpa [mul_assoc] using mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) hpoly
  dsimp [riemannXi]
  exact mul_ne_zero hfactor hcomp

end Riemann

end
