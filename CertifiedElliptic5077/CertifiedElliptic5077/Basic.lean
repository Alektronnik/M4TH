/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# A computational short-Weierstrass kit over `ℚ`

This file contains the self-contained algebraic core used by the certified
5077a1 entry: short Weierstrass curves, affine rational points, the point at
infinity, and explicit secant/tangent formulas.

## Main definitions

- `CertifiedEC.EllipticCurve`: a short Weierstrass model `y^2 = x^3 + a4*x + a6`.
- `CertifiedEC.RationalPoint`: affine rational points on such a curve.
- `CertifiedEC.ECPoint`: affine points plus the point at infinity.
- `CertifiedEC.naiveHeightRat`, `CertifiedEC.naiveHeight`.

## Main results

- `CertifiedEC.RationalPoint.addDistinct_comm`.
- `CertifiedEC.ECPoint.infinity_add`, `CertifiedEC.ECPoint.add_infinity`.
- `CertifiedEC.ECPoint.neg_add_self`, `CertifiedEC.ECPoint.add_comm`.

## Implementation notes

This package deliberately keeps a lightweight computational point type.  At
Mathlib-contribution time, reusable lemmas should be ported to
`WeierstrassCurve.Affine.Point`; the package keeps explicit formulas
because they are efficient for instance certificates.

## Tags

elliptic curve, rational point, Weierstrass model, certified computation
-/

@[expose] public section

namespace CertifiedEC

/-- Short Weierstrass model data.  Only `a4` and `a6` enter the equation in this
computational package; `a1`, `a2`, `a3` are retained for a uniform record shape. -/
structure EllipticCurve (K : Type) [Field K] where
  a1 : K
  a2 : K
  a3 : K
  a4 : K
  a6 : K

/-- Affine rational point on `y^2 = x^3 + a4*x + a6`. -/
structure RationalPoint (E : EllipticCurve ℚ) where
  x : ℚ
  y : ℚ
  on_curve : y ^ 2 = x ^ 3 + E.a4 * x + E.a6

namespace RationalPoint

@[ext] theorem ext {E : EllipticCurve ℚ} {P Q : RationalPoint E}
    (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q := by
  cases P
  cases Q
  simp_all

/-- Negation of an affine point on a short Weierstrass model. -/
def neg {E : EllipticCurve ℚ} (P : RationalPoint E) : RationalPoint E where
  x := P.x
  y := -P.y
  on_curve := by
    rw [neg_sq]
    exact P.on_curve

@[simp] theorem neg_x {E : EllipticCurve ℚ} (P : RationalPoint E) :
    P.neg.x = P.x := rfl

@[simp] theorem neg_y {E : EllipticCurve ℚ} (P : RationalPoint E) :
    P.neg.y = -P.y := rfl

@[simp] theorem neg_neg {E : EllipticCurve ℚ} (P : RationalPoint E) :
    P.neg.neg = P := by
  cases P
  simp [neg]

/-- Affine addition by the secant formula when the `x`-coordinates differ. -/
noncomputable def addDistinct {E : EllipticCurve ℚ}
    (P Q : RationalPoint E) (hx : Q.x ≠ P.x) : RationalPoint E := by
  let m : ℚ := (Q.y - P.y) / (Q.x - P.x)
  let x₃ : ℚ := m ^ 2 - P.x - Q.x
  let y₃ : ℚ := m * (P.x - x₃) - P.y
  refine ⟨x₃, y₃, ?_⟩
  have hP := P.on_curve
  have hQ := Q.on_curve
  have hm : m * (Q.x - P.x) = Q.y - P.y := by
    dsimp [m]
    field_simp [sub_ne_zero.mpr hx]
  have hsecant :
      m * (Q.y + P.y) = Q.x ^ 2 + Q.x * P.x + P.x ^ 2 + E.a4 := by
    have hfactor :
        (Q.y - P.y) * (Q.y + P.y) =
          (Q.x - P.x) * (Q.x ^ 2 + Q.x * P.x + P.x ^ 2 + E.a4) := by
      nlinarith [hP, hQ]
    apply (mul_left_cancel₀ (sub_ne_zero.mpr hx))
    calc
      (Q.x - P.x) * (m * (Q.y + P.y)) =
          (m * (Q.x - P.x)) * (Q.y + P.y) := by ring
      _ = (Q.y - P.y) * (Q.y + P.y) := by rw [hm]
      _ = (Q.x - P.x) *
          (Q.x ^ 2 + Q.x * P.x + P.x ^ 2 + E.a4) := hfactor
  have hA : E.a4 = m * (Q.y + P.y) - (Q.x ^ 2 + Q.x * P.x + P.x ^ 2) := by
    linarith [hsecant]
  have hB : E.a6 = P.y ^ 2 - P.x ^ 3 - E.a4 * P.x := by
    linarith [hP]
  have hB' : E.a6 = P.y ^ 2 - P.x ^ 3 -
      (m * (Q.y + P.y) - (Q.x ^ 2 + Q.x * P.x + P.x ^ 2)) * P.x := by
    rw [← hA]
    exact hB
  have hqy : Q.y = P.y + m * (Q.x - P.x) := by
    linarith [hm]
  dsimp [x₃, y₃]
  rw [hA, hB', hqy]
  ring

/-- Affine doubling by the tangent formula when `y ≠ 0`. -/
noncomputable def double {E : EllipticCurve ℚ}
    (P : RationalPoint E) (hy : P.y ≠ 0) : RationalPoint E := by
  let m : ℚ := (3 * P.x ^ 2 + E.a4) / (2 * P.y)
  let x₃ : ℚ := m ^ 2 - 2 * P.x
  let y₃ : ℚ := m * (P.x - x₃) - P.y
  refine ⟨x₃, y₃, ?_⟩
  have hP := P.on_curve
  have hm : m * (2 * P.y) = 3 * P.x ^ 2 + E.a4 := by
    dsimp [m]
    field_simp [hy]
  have hA : E.a4 = 2 * m * P.y - 3 * P.x ^ 2 := by
    nlinarith [hm]
  have hB : E.a6 = P.y ^ 2 - P.x ^ 3 - E.a4 * P.x := by
    linarith [hP]
  have hB' : E.a6 = P.y ^ 2 - P.x ^ 3 -
      (2 * m * P.y - 3 * P.x ^ 2) * P.x := by
    rw [← hA]
    exact hB
  dsimp [x₃, y₃]
  rw [hA, hB']
  ring

/-- The secant formula is symmetric in its two endpoints. -/
theorem addDistinct_comm {E : EllipticCurve ℚ} (P Q : RationalPoint E)
    (hQP : Q.x ≠ P.x) (hPQ : P.x ≠ Q.x) :
    P.addDistinct Q hQP = Q.addDistinct P hPQ := by
  have hm : (Q.y - P.y) / (Q.x - P.x) =
      (P.y - Q.y) / (P.x - Q.x) := by
    calc
      (Q.y - P.y) / (Q.x - P.x) =
          (-(P.y - Q.y)) / (-(P.x - Q.x)) := by ring
      _ = (P.y - Q.y) / (P.x - Q.x) := neg_div_neg_eq _ _
  apply ext
  · dsimp [addDistinct]
    rw [hm]
    ring
  · dsimp [addDistinct]
    rw [hm]
    have hslope :
        ((P.y - Q.y) / (P.x - Q.x)) * (Q.x - P.x) = Q.y - P.y := by
      rw [← hm]
      exact div_mul_cancel₀ _ (sub_ne_zero.mpr hQP)
    rw [show
      ((P.y - Q.y) / (P.x - Q.x)) ^ 2 - P.x - Q.x =
        ((P.y - Q.y) / (P.x - Q.x)) ^ 2 - Q.x - P.x by ring]
    linarith

end RationalPoint

/-- Projective point set: affine points plus the point at infinity. -/
inductive ECPoint (E : EllipticCurve ℚ) where
  | infinity : ECPoint E
  | affine (P : RationalPoint E) : ECPoint E

namespace ECPoint

noncomputable instance {E : EllipticCurve ℚ} : DecidableEq (RationalPoint E) :=
  Classical.decEq _

/-- Projective negation. -/
def neg {E : EllipticCurve ℚ} : ECPoint E → ECPoint E
  | infinity => infinity
  | affine P => affine P.neg

instance {E : EllipticCurve ℚ} : Neg (ECPoint E) := ⟨neg⟩

@[simp] theorem neg_infinity {E : EllipticCurve ℚ} :
    -(infinity : ECPoint E) = infinity := rfl

@[simp] theorem neg_affine {E : EllipticCurve ℚ} (P : RationalPoint E) :
    -(affine P) = affine P.neg := rfl

@[simp] theorem neg_neg {E : EllipticCurve ℚ} (P : ECPoint E) : -(-P) = P := by
  cases P <;> simp

/-- Total explicit composition law for the computational model. -/
noncomputable def add {E : EllipticCurve ℚ} : ECPoint E → ECPoint E → ECPoint E
  | infinity, Q => Q
  | P, infinity => P
  | affine P, affine Q =>
      if P = Q then
        if hy : P.y = 0 then infinity else affine (RationalPoint.double P hy)
      else if hx : Q.x = P.x then infinity
      else affine (P.addDistinct Q hx)

noncomputable instance {E : EllipticCurve ℚ} : Add (ECPoint E) := ⟨add⟩

instance {E : EllipticCurve ℚ} : Zero (ECPoint E) := ⟨infinity⟩

@[simp] theorem infinity_add {E : EllipticCurve ℚ} (P : ECPoint E) :
    (infinity : ECPoint E) + P = P := by
  rfl

@[simp] theorem add_infinity {E : EllipticCurve ℚ} (P : ECPoint E) :
    P + (infinity : ECPoint E) = P := by
  cases P <;> rfl

@[simp] theorem zero_eq_infinity {E : EllipticCurve ℚ} :
    (0 : ECPoint E) = infinity := rfl

theorem neg_add_self {E : EllipticCurve ℚ} (P : ECPoint E) : -P + P = 0 := by
  cases P with
  | infinity => rfl
  | affine P =>
      change add (affine P.neg) (affine P) = 0
      by_cases hy : P.y = 0
      · have hEq : P.neg = P := by
          apply RationalPoint.ext
          · rfl
          · simp [hy]
        simp [add, hEq, hy]
      · have hne : P.neg ≠ P := by
          intro h
          have := congrArg RationalPoint.y h
          simp only [RationalPoint.neg_y] at this
          exact hy (by linarith)
        simp [add, hne]

theorem add_comm {E : EllipticCurve ℚ} (P Q : ECPoint E) : P + Q = Q + P := by
  cases P with
  | infinity => cases Q <;> rfl
  | affine P =>
      cases Q with
      | infinity => rfl
      | affine Q =>
          by_cases hPQ : P = Q
          · subst Q
            rfl
          · have hQP : Q ≠ P := Ne.symm hPQ
            change add (affine P) (affine Q) = add (affine Q) (affine P)
            by_cases hx : Q.x = P.x
            · rw [add.eq_3, add.eq_3, if_neg hPQ, if_neg hQP, dif_pos hx, dif_pos hx.symm]
            · have hx' : P.x ≠ Q.x := Ne.symm hx
              rw [add.eq_3, add.eq_3, if_neg hPQ, if_neg hQP, dif_neg hx, dif_neg hx']
              exact congrArg affine (RationalPoint.addDistinct_comm P Q hx hx')

@[simp] theorem add_neg_self {E : EllipticCurve ℚ} (P : ECPoint E) :
    P + -P = 0 := by
  rw [add_comm, neg_add_self]

end ECPoint

/-- Naive logarithmic height of a rational number. -/
noncomputable def naiveHeightRat (q : ℚ) : ℝ :=
  Real.log (max ((q.num.natAbs : ℝ)) ((q.den : ℝ)))

theorem naiveHeightRat_nonnegative (q : ℚ) : 0 ≤ naiveHeightRat q := by
  unfold naiveHeightRat
  apply Real.log_nonneg
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  exact le_trans hden (le_max_right _ _)

/-- Naive height of a computational projective point. -/
noncomputable def naiveHeight {E : EllipticCurve ℚ} : ECPoint E → ℝ
  | ECPoint.infinity => 0
  | ECPoint.affine P => naiveHeightRat P.x

@[simp] theorem naiveHeight_infinity {E : EllipticCurve ℚ} :
    naiveHeight (ECPoint.infinity : ECPoint E) = 0 := rfl

@[simp] theorem naiveHeight_affine {E : EllipticCurve ℚ} (P : RationalPoint E) :
    naiveHeight (ECPoint.affine P) = naiveHeightRat P.x := rfl

theorem naiveHeight_nonnegative {E : EllipticCurve ℚ} (P : ECPoint E) :
    0 ≤ naiveHeight P := by
  cases P with
  | infinity => simp
  | affine P => exact naiveHeightRat_nonnegative P.x

end CertifiedEC

end
