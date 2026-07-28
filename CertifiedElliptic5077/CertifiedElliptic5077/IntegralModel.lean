/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Tactic.IntervalCases
public import CertifiedElliptic5077.FiniteFieldCounts

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
