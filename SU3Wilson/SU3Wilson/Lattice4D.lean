/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import SU3Wilson.Wilson

/-!
# Constructive four-dimensional SU(3) lattice Wilson action

This file constructs plaquettes directly from four-dimensional SU(3) link
variables.  It proves the diagonal plaquette law, the Wilson term bounds, and
nonnegativity of the four-dimensional Wilson action.

## Main definitions

- `Physics.YangMills.Lattice4D`: a finite Euclidean four-dimensional lattice.
- `Physics.YangMills.Dir4`: the four coordinate directions.
- `Physics.YangMills.LinkVars4D`: SU(3)-valued link variables.
- `Physics.YangMills.plaquette4D`, `wilsonTerm4D`, `WilsonAction4D`.

## Main results

- `Physics.YangMills.plaquette4D_diagonal`.
- `Physics.YangMills.plaquette4D_trace_re_symm`.
- `Physics.YangMills.wilsonTerm4D_nonneg`.
- `Physics.YangMills.WilsonAction4D_nonneg`.

## Tags

Wilson action, lattice gauge theory, SU(3), four-dimensional lattice
-/

@[expose] public section

namespace Physics.YangMills

open Matrix Complex BigOperators

/-- Euclidean 4D lattice with temporal and three spatial extents. -/
abbrev Lattice4D (Lt Lx Ly Lz : ℕ) := Fin Lt × Fin Lx × Fin Ly × Fin Lz

/-- The four positive coordinate directions. -/
abbrev Dir4 := Fin 4

def dirT : Dir4 := 0
def dirX : Dir4 := 1
def dirY : Dir4 := 2
def dirZ : Dir4 := 3

/-- Cyclic successor in `Fin n`. -/
def wrapSucc {n : ℕ} (i : Fin n) : Fin n :=
  if hn : n = 0 then
    i
  else
    let npos : 0 < n := Nat.pos_of_ne_zero hn
    ⟨(i.val + 1) % n, Nat.mod_lt _ npos⟩

/-- Reversal of a `Fin n` index. -/
def finRev {n : ℕ} (i : Fin n) : Fin n :=
  if hn : n = 0 then
    i
  else
    let m := n - 1
    ⟨m - i.val, by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have h_lt : i.val < n := i.is_lt
      have hm_lt_n : m < n := by omega
      have hsub : m - i.val ≤ m := Nat.sub_le _ _
      exact lt_of_le_of_lt hsub hm_lt_n⟩

/-- Time reflection reverses the temporal coordinate and preserves space. -/
def timeReflection4D {Lt Lx Ly Lz : ℕ}
    (site : Lattice4D Lt Lx Ly Lz) : Lattice4D Lt Lx Ly Lz :=
  (finRev site.1, site.2.1, site.2.2.1, site.2.2.2)

/-- Shift by one in direction `mu`, with periodic boundary conditions. -/
def shift4D {Lt Lx Ly Lz : ℕ} (site : Lattice4D Lt Lx Ly Lz)
    (μ : Dir4) : Lattice4D Lt Lx Ly Lz :=
  match μ with
  | 0 => (wrapSucc site.1, site.2.1, site.2.2.1, site.2.2.2)
  | 1 => (site.1, wrapSucc site.2.1, site.2.2.1, site.2.2.2)
  | 2 => (site.1, site.2.1, wrapSucc site.2.2.1, site.2.2.2)
  | 3 => (site.1, site.2.1, site.2.2.1, wrapSucc site.2.2.2)

/-- Four-dimensional link configurations assign an `SU3` element to each directed link. -/
def LinkVars4D (Lt Lx Ly Lz : ℕ) : Type :=
  Lattice4D Lt Lx Ly Lz → Dir4 → SU3

variable {Lt Lx Ly Lz : ℕ}

/-- Plaquette at `site` in the `(mu, nu)` plane as an ordered four-link product. -/
noncomputable def plaquette4D (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) : SU3 :=
  U site μ *
    U (shift4D site μ) ν *
    (U (shift4D site ν) μ)⁻¹ *
    (U site ν)⁻¹

/-- The diagonal plaquette is the identity. -/
theorem plaquette4D_diagonal (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ : Dir4) :
    plaquette4D U site μ μ = 1 := by
  unfold plaquette4D
  have h : U (shift4D site μ) μ * (U (shift4D site μ) μ)⁻¹ = 1 := by
    simp
  calc
    U site μ * U (shift4D site μ) μ * (U (shift4D site μ) μ)⁻¹ * (U site μ)⁻¹
        = U site μ * (U (shift4D site μ) μ * (U (shift4D site μ) μ)⁻¹) *
            (U site μ)⁻¹ := by
      simp [mul_assoc]
    _ = U site μ * 1 * (U site μ)⁻¹ := by rw [h]
    _ = U site μ * (U site μ)⁻¹ := by simp
    _ = 1 := by simp

/-- The real trace of a plaquette is invariant under swapping its directions. -/
theorem plaquette4D_trace_re_symm (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) :
    (matrixTraceSU3 (plaquette4D U site μ ν)).re =
      (matrixTraceSU3 (plaquette4D U site ν μ)).re := by
  unfold plaquette4D
  have h_inv :
      (U site μ * U (shift4D site μ) ν * (U (shift4D site ν) μ)⁻¹ *
          (U site ν)⁻¹)⁻¹ =
        U site ν * U (shift4D site ν) μ * (U (shift4D site μ) ν)⁻¹ *
          (U site μ)⁻¹ := by
    simp [mul_assoc]
  have h_re_trace_inv (A : SU3) :
      (matrixTraceSU3 (A⁻¹ : SU3)).re = (matrixTraceSU3 A).re := by
    have h_val : (A⁻¹ : SU3).val = A.val.conjTranspose := rfl
    rw [matrixTraceSU3, h_val]
    have h_tr : (A.val.conjTranspose).trace = star (A.val.trace) := by
      calc
        (A.val.conjTranspose).trace = ∑ i : Fin 3, (A.val.conjTranspose) i i := by
          simp [Matrix.trace, Matrix.diag]
        _ = ∑ i : Fin 3, star (A.val i i) := by
          simp [Matrix.conjTranspose_apply]
        _ = star (∑ i : Fin 3, A.val i i) := by simp
        _ = star (A.val.trace) := by simp [Matrix.trace, Matrix.diag]
    rw [h_tr, matrixTraceSU3]
    simp
  rw [← h_inv]
  rw [h_re_trace_inv]

/-- Normalized sum over all 4D sites and direction pairs. -/
noncomputable def latticeSum4D
    (f : Lattice4D Lt Lx Ly Lz → Dir4 → Dir4 → ℝ) : ℝ :=
  let V := Lt * Lx * Ly * Lz
  (1 / (V : ℝ)) * ∑ site : Lattice4D Lt Lx Ly Lz,
    ∑ μ : Dir4, ∑ ν : Dir4, f site μ ν

/-- `latticeSum4D` is nonnegative for pointwise nonnegative inputs. -/
theorem latticeSum4D_nonneg (f : Lattice4D Lt Lx Ly Lz → Dir4 → Dir4 → ℝ)
    (hf : ∀ site μ ν, 0 ≤ f site μ ν) : 0 ≤ latticeSum4D f := by
  unfold latticeSum4D
  refine mul_nonneg ?_ ?_
  · refine div_nonneg zero_le_one (Nat.cast_nonneg _)
  · refine Finset.sum_nonneg (fun site _ => ?_)
    refine Finset.sum_nonneg (fun μ _ => ?_)
    refine Finset.sum_nonneg (fun ν _ => hf site μ ν)

/-- Wilson term for a constructive 4D plaquette. -/
noncomputable def wilsonTerm4D (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) : ℝ :=
  1 - (matrixTraceSU3 (plaquette4D U site μ ν)).re / 3

/-- Each 4D Wilson term is nonnegative. -/
theorem wilsonTerm4D_nonneg (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) :
    0 ≤ wilsonTerm4D U site μ ν := by
  unfold wilsonTerm4D
  rcases su3_trace_re_bound (plaquette4D U site μ ν) with ⟨_, h⟩
  linarith

/-- Each 4D Wilson term is at most `2`. -/
theorem wilsonTerm4D_le_two (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) :
    wilsonTerm4D U site μ ν ≤ 2 := by
  unfold wilsonTerm4D
  rcases su3_trace_re_bound (plaquette4D U site μ ν) with ⟨h, _⟩
  linarith

/-- Diagonal 4D Wilson terms vanish. -/
theorem wilsonTerm4D_diagonal (U : LinkVars4D Lt Lx Ly Lz)
    (site : Lattice4D Lt Lx Ly Lz) (μ : Dir4) :
    wilsonTerm4D U site μ μ = 0 := by
  unfold wilsonTerm4D
  rw [plaquette4D_diagonal U site μ]
  have h : matrixTraceSU3 (1 : SU3) = (3 : ℂ) := by
    simpa [oneSU3] using matrixTraceSU3_one
  rw [h]
  simp

/-- Constructive four-dimensional Wilson action. -/
noncomputable def WilsonAction4D (β : ℝ) (U : LinkVars4D Lt Lx Ly Lz) : ℝ :=
  β * latticeSum4D (wilsonTerm4D U)

/-- `WilsonAction4D` is nonnegative for `β >= 0`. -/
theorem WilsonAction4D_nonneg (β : ℝ) (U : LinkVars4D Lt Lx Ly Lz)
    (hβ : 0 ≤ β) : 0 ≤ WilsonAction4D β U := by
  unfold WilsonAction4D
  refine mul_nonneg hβ ?_
  apply latticeSum4D_nonneg (wilsonTerm4D U)
  intro site μ ν
  exact wilsonTerm4D_nonneg U site μ ν

/-- Time reflection on link configurations. Temporal links invert orientation;
spatial links are preserved after reflecting the site. -/
noncomputable def timeReflection4D_on_links
    (U : LinkVars4D Lt Lx Ly Lz) : LinkVars4D Lt Lx Ly Lz :=
  fun site μ =>
    let siteReversed := timeReflection4D site
    match μ with
    | 0 => (U siteReversed 0)⁻¹
    | _ => U siteReversed μ

end Physics.YangMills

end
