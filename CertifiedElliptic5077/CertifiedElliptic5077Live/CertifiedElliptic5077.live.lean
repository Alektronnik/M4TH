/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.IntervalCases

/-!
# CertifiedElliptic5077 live edition

Single-file live edition of the `CertifiedElliptic5077` package for web
certification and study.  The mathematical content is the package source fused
in dependency order: `Basic`, `FiniteFieldCounts`, `IntegralModel`, and
`Entry5077a1`.
-/


/-!
## Source file: `CertifiedElliptic5077/Basic.lean`
-/

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
`WeierstrassCurve.Affine.Point`; the standalone package keeps explicit formulas
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


/-!
## Source file: `CertifiedElliptic5077/FiniteFieldCounts.lean`
-/

/-!
# Finite-field point counts for the curve 5077a1

This file defines the reduction of the integral model

`y^2 + y = x^3 - 7x + 6`

modulo a prime `p`, counts its affine points over `ZMod p`, and defines the
local Frobenius coefficient `a_p = p + 1 - #E(F_p)`.

## Main definitions

- `CertifiedEC.E5077Mod`: the integral Weierstrass model reduced modulo `p`.
- `CertifiedEC.affinePointsFinset`: finite set of affine solutions over `ZMod p`.
- `CertifiedEC.N_p`, `CertifiedEC.a_p`.

## Main results

- `CertifiedEC.a_p_two`, `CertifiedEC.a_p_three`, `CertifiedEC.a_p_five`.
- `CertifiedEC.N_two`, `CertifiedEC.N_three`, `CertifiedEC.N_five`.

## Implementation notes

The concrete certificates are kernel-checked finite `Finset` computations and
can be evaluated for additional primes.

## Tags

elliptic curve, finite field, Frobenius trace, certified data
-/

@[expose] public section

namespace CertifiedEC

/-- Reduction of the integral model 5077a1 modulo a prime `p`. -/
def E5077Mod (p : ℕ) [Fact p.Prime] : WeierstrassCurve (ZMod p) :=
  WeierstrassCurve.map (⟨0, 0, 1, -7, 6⟩ : WeierstrassCurve ℤ)
    (Int.castRingHom (ZMod p))

/-- Affine points `(x,y)` satisfying `y^2 + y = x^3 - 7x + 6` over `ZMod p`. -/
def affinePointsFinset (p : ℕ) [Fact p.Prime] : Finset ((ZMod p) × (ZMod p)) :=
  Finset.filter
    (fun ⟨x, y⟩ => y ^ 2 + y = x ^ 3 - (7 : ZMod p) * x + (6 : ZMod p))
    Finset.univ

/-- Number of projective points over `F_p`: affine points plus infinity. -/
def N_p (p : ℕ) [Fact p.Prime] : ℕ :=
  (affinePointsFinset p).card + 1

/-- Local Frobenius coefficient `a_p = p + 1 - #E(F_p)`. -/
def a_p (p : ℕ) [Fact p.Prime] : ℤ :=
  (p : ℤ) + 1 - (N_p p : ℤ)

instance fact_prime_2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
instance fact_prime_3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance fact_prime_5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem N_two : N_p 2 = 5 := by
  decide

theorem N_three : N_p 3 = 7 := by
  decide

theorem N_five : N_p 5 = 10 := by
  decide

theorem a_p_two : a_p 2 = -2 := by
  decide

theorem a_p_three : a_p 3 = -3 := by
  decide

theorem a_p_five : a_p 5 = -4 := by
  decide

end CertifiedEC

end


/-!
## Source file: `CertifiedElliptic5077/IntegralModel.lean`
-/

/-!
# The integral and short models of 5077a1

This file defines the short rational model and the original integral model of
Cremona curve 5077a1.  It proves their discriminants, the exact change of
coordinates from the integral model to the short model, and a finite
Nagell--Lutz-style candidate reduction for integral torsion candidates.

## Main definitions

- `CertifiedEC.E5077`: the short model `y^2 = x^3 - 7x + 25/4`.
- `CertifiedEC.E5077Integral`: the integral model `y^2 + y = x^3 - 7x + 6`.
- `CertifiedEC.IntegralModelRationalPoint`.
- `CertifiedEC.IntegralModelIntegerPoint`.

## Main results

- `CertifiedEC.delta_E5077_integral`.
- `CertifiedEC.shortDiscriminant_E5077`.
- `CertifiedEC.IntegralModelIntegerPoint.coordinates_mem_nagellLutz_candidates`.

## Tags

elliptic curve, 5077a1, integral model, Nagell-Lutz, discriminant
-/

@[expose] public section

namespace CertifiedEC

/-- The curve 5077a1 in short Weierstrass form over `ℚ`. -/
def E5077 : EllipticCurve ℚ where
  a1 := 0
  a2 := 0
  a3 := 0
  a4 := -7
  a6 := 25 / 4

/-- Integral model `y^2 + y = x^3 - 7x + 6`. -/
def E5077Integral : WeierstrassCurve ℤ :=
  ⟨0, 0, 1, -7, 6⟩

/-- The integral discriminant is exactly `5077`. -/
theorem delta_E5077_integral : E5077Integral.Δ = 5077 := by
  norm_num [E5077Integral, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem delta_E5077_integral_ne_zero : E5077Integral.Δ ≠ 0 := by
  rw [delta_E5077_integral]
  norm_num

/-- Rational affine points on the integral model. -/
structure IntegralModelRationalPoint where
  x : ℚ
  y : ℚ
  on_curve : y ^ 2 + y = x ^ 3 - 7 * x + 6

namespace IntegralModelRationalPoint

/-- Change of variables from `y^2 + y = x^3 - 7x + 6` to
`Y^2 = x^3 - 7x + 25/4`, namely `Y = y + 1/2`. -/
def toShort (P : IntegralModelRationalPoint) : RationalPoint E5077 where
  x := P.x
  y := P.y + 1 / 2
  on_curve := by
    have h := P.on_curve
    norm_num [E5077] at h ⊢
    nlinarith

/-- Inverse change of variables from the short model to the integral model. -/
def ofShort (P : RationalPoint E5077) : IntegralModelRationalPoint where
  x := P.x
  y := P.y - 1 / 2
  on_curve := by
    have h := P.on_curve
    norm_num [E5077] at h ⊢
    nlinarith

@[simp] theorem toShort_x (P : IntegralModelRationalPoint) : P.toShort.x = P.x := rfl

@[simp] theorem toShort_y (P : IntegralModelRationalPoint) :
    P.toShort.y = P.y + 1 / 2 := rfl

@[simp] theorem ofShort_x (P : RationalPoint E5077) :
    (ofShort P).x = P.x := rfl

@[simp] theorem ofShort_y (P : RationalPoint E5077) :
    (ofShort P).y = P.y - 1 / 2 := rfl

/-- Equivalence between rational points on the integral and short models. -/
def shortModelEquiv : IntegralModelRationalPoint ≃ RationalPoint E5077 where
  toFun := toShort
  invFun := ofShort
  left_inv := by
    intro P
    cases P
    simp [toShort, ofShort]
  right_inv := by
    intro P
    apply RationalPoint.ext <;> simp [toShort, ofShort]

end IntegralModelRationalPoint

/-- Integral affine points on the integral model. -/
structure IntegralModelIntegerPoint where
  x : ℤ
  y : ℤ
  on_curve : y ^ 2 + y = x ^ 3 - 7 * x + 6

namespace IntegralModelIntegerPoint

@[ext] theorem ext {P Q : IntegralModelIntegerPoint}
    (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q := by
  cases P
  cases Q
  simp_all

/-- Inclusion into rational points on the integral model. -/
def toRational (P : IntegralModelIntegerPoint) : IntegralModelRationalPoint where
  x := P.x
  y := P.y
  on_curve := by exact_mod_cast P.on_curve

/-- Inclusion into the short rational model. -/
def toShort (P : IntegralModelIntegerPoint) : RationalPoint E5077 :=
  P.toRational.toShort

@[simp] theorem toRational_x (P : IntegralModelIntegerPoint) : P.toRational.x = P.x := rfl
@[simp] theorem toRational_y (P : IntegralModelIntegerPoint) : P.toRational.y = P.y := rfl
@[simp] theorem toShort_x (P : IntegralModelIntegerPoint) : P.toShort.x = P.x := rfl
@[simp] theorem toShort_y (P : IntegralModelIntegerPoint) : P.toShort.y = P.y + 1 / 2 := rfl

/-- Factorization of the cubic side of the integral model. -/
theorem cubic_factor (x : ℤ) :
    x ^ 3 - 7 * x + 6 = (x + 3) * (x - 1) * (x - 2) := by
  ring

/-- If `y = 0` or `y = -1`, the only integral abscissas are `-3`, `1`, `2`. -/
theorem x_eq_of_y_eq_zero_or_neg_one (P : IntegralModelIntegerPoint)
    (hy : P.y = 0 ∨ P.y = -1) : P.x = -3 ∨ P.x = 1 ∨ P.x = 2 := by
  have hcubic : P.x ^ 3 - 7 * P.x + 6 = 0 := by
    have hcurve := P.on_curve
    rcases hy with hy | hy <;> rw [hy] at hcurve <;> norm_num at hcurve ⊢
    all_goals exact hcurve.symm
  rw [cubic_factor] at hcubic
  rcases mul_eq_zero.mp hcubic with hleft | hright
  · rcases mul_eq_zero.mp hleft with hx | hx
    · left
      linarith
    · right; left
      linarith
  · right; right
    linarith

theorem x_mem_candidates_of_y_eq_zero_or_neg_one (P : IntegralModelIntegerPoint)
    (hy : P.y = 0 ∨ P.y = -1) : P.x ∈ ({-3, 1, 2} : Finset ℤ) := by
  rcases P.x_eq_of_y_eq_zero_or_neg_one hy with hx | hx | hx <;> simp [hx]

/-- If `(2y+1)^2` divides the prime discriminant `5077`, then `y = 0` or `y = -1`. -/
theorem y_eq_zero_or_neg_one_of_psi_sq_dvd (P : IntegralModelIntegerPoint)
    (hdiv : (2 * P.y + 1) ^ 2 ∣ (5077 : ℤ)) : P.y = 0 ∨ P.y = -1 := by
  obtain ⟨k, hk⟩ := hdiv
  have hpsi0 : 2 * P.y + 1 ≠ 0 := by
    intro h
    rw [h] at hk
    norm_num at hk
  have hspos : 0 < (2 * P.y + 1) ^ 2 := sq_pos_of_ne_zero hpsi0
  have hkpos : 0 < k := by nlinarith
  have hsle : (2 * P.y + 1) ^ 2 ≤ 5077 := by nlinarith
  have hlo : -36 ≤ P.y := by nlinarith [sq_nonneg (2 * P.y + 1)]
  have hhi : P.y ≤ 35 := by nlinarith [sq_nonneg (2 * P.y + 1)]
  interval_cases P.y <;> norm_num at hk ⊢ <;> omega

/-- Nagell--Lutz candidate reduction for integral points on this model. -/
theorem coordinates_mem_nagellLutz_candidates (P : IntegralModelIntegerPoint)
    (hdiv : (2 * P.y + 1) ^ 2 ∣ (5077 : ℤ)) :
    P.x ∈ ({-3, 1, 2} : Finset ℤ) ∧ P.y ∈ ({0, -1} : Finset ℤ) := by
  have hy := P.y_eq_zero_or_neg_one_of_psi_sq_dvd hdiv
  exact ⟨P.x_mem_candidates_of_y_eq_zero_or_neg_one hy,
    by rcases hy with hy | hy <;> simp [hy]⟩

end IntegralModelIntegerPoint

/-- Discriminant of a short model `y^2 = x^3 + a4*x + a6`. -/
def shortDiscriminant (E : EllipticCurve ℚ) : ℚ :=
  -16 * (4 * E.a4 ^ 3 + 27 * E.a6 ^ 2)

/-- The short discriminant of 5077a1 is exactly `5077`. -/
theorem shortDiscriminant_E5077 : shortDiscriminant E5077 = 5077 := by
  norm_num [shortDiscriminant, E5077]

theorem E5077_nonsingular : shortDiscriminant E5077 ≠ 0 := by
  rw [shortDiscriminant_E5077]
  norm_num

end CertifiedEC

end


/-!
## Source file: `CertifiedElliptic5077/Entry5077a1.lean`
-/

/-!
# The certified 5077a1 entry

This file contains kernel-checked data for the curve 5077a1: the integral and
short models, discriminants, selected local point counts, explicit rational
points, and verified doubles.

## Main definitions

- `CertifiedEC.P1_5077`, `P2_5077`, `Pm3_5077`, `P3_5077`.
- `CertifiedEC.twiceP1_5077`, `twiceP2_5077`, `twicePm3_5077`.
- `CertifiedEC.basis5077`, `CertifiedEC.projectiveBasis5077`.
- `CertifiedEC.AlgebraicInvariants`, `CertifiedEC.invariants5077`.

## Main results

- `CertifiedEC.P1_add_self`.
- `CertifiedEC.P2_add_self`.
- `CertifiedEC.Pm3_add_self`.
- `CertifiedEC.basis5077_zero`, `basis5077_one`, `basis5077_two`.

## Implementation notes

The three points listed here are certified to lie on the curve and their doubles
are checked by reducing the explicit tangent formula with `norm_num`.  This is
the data-entry pattern intended for a future `CertifiedData`/LMFDB repository.

## Tags

elliptic curve, 5077a1, LMFDB, certified data, rational point
-/

@[expose] public section

namespace CertifiedEC

/-- First explicit rational point on 5077a1. -/
def P1_5077 : RationalPoint E5077 where
  x := 1
  y := 1 / 2
  on_curve := by
    norm_num [E5077]

/-- Second explicit rational point on 5077a1. -/
def P2_5077 : RationalPoint E5077 where
  x := 2
  y := 1 / 2
  on_curve := by
    norm_num [E5077]

/-- The point from integral coordinates `(-3, 0)`, in the short model. -/
def Pm3_5077 : RationalPoint E5077 where
  x := -3
  y := 1 / 2
  on_curve := by
    norm_num [E5077]

/-- Third generator candidate, from integral coordinates `(0, 2)`. -/
def P3_5077 : RationalPoint E5077 where
  x := 0
  y := 5 / 2
  on_curve := by
    norm_num [E5077]

/-- Certified double of `P1_5077`. -/
def twiceP1_5077 : RationalPoint E5077 where
  x := 14
  y := 103 / 2
  on_curve := by
    norm_num [E5077]

/-- Certified double of `P2_5077`. -/
def twiceP2_5077 : RationalPoint E5077 where
  x := 21
  y := -191 / 2
  on_curve := by
    norm_num [E5077]

/-- Certified double of `Pm3_5077`. -/
def twicePm3_5077 : RationalPoint E5077 where
  x := 406
  y := -16361 / 2
  on_curve := by
    norm_num [E5077]

/-- Kernel check: `2P1 = (14, 103/2)`. -/
theorem P1_add_self :
    ECPoint.affine P1_5077 + ECPoint.affine P1_5077 =
      ECPoint.affine twiceP1_5077 := by
  change ECPoint.add (ECPoint.affine P1_5077) (ECPoint.affine P1_5077) = _
  rw [ECPoint.add, if_pos rfl]
  have hy : P1_5077.y ≠ 0 := by norm_num [P1_5077]
  rw [dif_neg hy]
  congr 1
  apply RationalPoint.ext
  · norm_num [RationalPoint.double, P1_5077, twiceP1_5077, E5077]
  · norm_num [RationalPoint.double, P1_5077, twiceP1_5077, E5077]

/-- Kernel check: `2P2 = (21, -191/2)`. -/
theorem P2_add_self :
    ECPoint.affine P2_5077 + ECPoint.affine P2_5077 =
      ECPoint.affine twiceP2_5077 := by
  change ECPoint.add (ECPoint.affine P2_5077) (ECPoint.affine P2_5077) = _
  rw [ECPoint.add, if_pos rfl]
  have hy : P2_5077.y ≠ 0 := by norm_num [P2_5077]
  rw [dif_neg hy]
  congr 1
  apply RationalPoint.ext <;>
    norm_num [RationalPoint.double, P2_5077, twiceP2_5077, E5077]

/-- Kernel check: `2Pm3 = (406, -16361/2)`. -/
theorem Pm3_add_self :
    ECPoint.affine Pm3_5077 + ECPoint.affine Pm3_5077 =
      ECPoint.affine twicePm3_5077 := by
  change ECPoint.add (ECPoint.affine Pm3_5077) (ECPoint.affine Pm3_5077) = _
  rw [ECPoint.add, if_pos rfl]
  have hy : Pm3_5077.y ≠ 0 := by norm_num [Pm3_5077]
  rw [dif_neg hy]
  congr 1
  apply RationalPoint.ext <;>
    norm_num [RationalPoint.double, Pm3_5077, twicePm3_5077, E5077]

/-- Algebraic invariants stored as certified data fields. -/
structure AlgebraicInvariants (E : EllipticCurve ℚ) where
  torsion_order : ℕ
  h_tors_pos : 0 < torsion_order
  tamagawa_product : ℕ
  h_tam_pos : 0 < tamagawa_product
  sha_order : ℕ
  real_period : ℝ
  h_period_pos : 0 < real_period

/-- Algebraic data attached to the LMFDB entry 5077a1.  This is data, not a BSD
proof: the analytic statement is intentionally outside this package. -/
noncomputable def invariants5077 : AlgebraicInvariants E5077 where
  torsion_order := 1
  h_tors_pos := by norm_num
  tamagawa_product := 1
  h_tam_pos := by norm_num
  sha_order := 1
  real_period := 2.8534169
  h_period_pos := by norm_num

/-- The explicit three-point basis data for the entry. -/
def basis5077 (i : Fin 3) : RationalPoint E5077 :=
  if i.val = 0 then P1_5077
  else if i.val = 1 then P2_5077
  else P3_5077

/-- The same basis data as projective points. -/
def projectiveBasis5077 (i : Fin 3) : ECPoint E5077 :=
  ECPoint.affine (basis5077 i)

@[simp] theorem basis5077_zero :
    basis5077 ⟨0, by norm_num⟩ = P1_5077 := by
  simp [basis5077]

@[simp] theorem basis5077_one :
    basis5077 ⟨1, by norm_num⟩ = P2_5077 := by
  simp [basis5077]

@[simp] theorem basis5077_two :
    basis5077 ⟨2, by norm_num⟩ = P3_5077 := by
  simp [basis5077]

/-- The integral point `(0,2)` maps to `P3_5077` under the short-model change of
coordinates. -/
def integralP3 : IntegralModelIntegerPoint where
  x := 0
  y := 2
  on_curve := by norm_num

theorem integralP3_toShort : integralP3.toShort = P3_5077 := by
  apply RationalPoint.ext <;> norm_num [integralP3, IntegralModelIntegerPoint.toShort,
    IntegralModelIntegerPoint.toRational, IntegralModelRationalPoint.toShort, P3_5077]

/-- The six Nagell--Lutz candidate coordinate pairs for integral torsion checks. -/
def nagellLutzCandidatePairs : Finset (ℤ × ℤ) :=
  {(-3, 0), (-3, -1), (1, 0), (1, -1), (2, 0), (2, -1)}

/-- The candidate point `(-3,0)` lies in the listed Nagell--Lutz set. -/
theorem neg_three_zero_mem_candidates : ((-3 : ℤ), (0 : ℤ)) ∈ nagellLutzCandidatePairs := by
  simp [nagellLutzCandidatePairs]

/-- The candidate point `(1,0)` lies in the listed Nagell--Lutz set. -/
theorem one_zero_mem_candidates : ((1 : ℤ), (0 : ℤ)) ∈ nagellLutzCandidatePairs := by
  simp [nagellLutzCandidatePairs]

/-- The candidate point `(2,0)` lies in the listed Nagell--Lutz set. -/
theorem two_zero_mem_candidates : ((2 : ℤ), (0 : ℤ)) ∈ nagellLutzCandidatePairs := by
  simp [nagellLutzCandidatePairs]

end CertifiedEC

end
