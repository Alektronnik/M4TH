/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Tactic.NormNum.Prime
public import CertifiedElliptic5077.Basic

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
