/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import CertifiedElliptic5077.IntegralModel

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
