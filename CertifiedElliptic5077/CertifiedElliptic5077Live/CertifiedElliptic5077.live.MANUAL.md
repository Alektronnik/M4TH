# CertifiedElliptic5077.live

**A single-file live presentation of certified algebraic data for the
LMFDB/Cremona elliptic-curve entry 5077a1, formalised in Lean 4 over Mathlib.**

**Author:** Bezalel Izquierdo Pérez
**License:** Apache 2.0
**Live file:** `CertifiedElliptic5077.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`CertifiedElliptic5077.live.lean`.  It presents the mathematical content in the
same order as the live Lean file.  Proof scripts are intentionally omitted here;
the live Lean file is the certificate.

---

## I. The Mathematical Problem

The package certifies concrete algebraic and finite computational data for the
elliptic curve entry 5077a1.

The integral model is

$$
y^2 + y = x^3 - 7x + 6.
$$

The associated short model is obtained by the change of variables

$$
Y = y + \frac{1}{2},
$$

giving

$$
Y^2 = x^3 - 7x + \frac{25}{4}.
$$

The package certifies:

- a reusable short-Weierstrass computational point type;
- affine and projective point operations;
- finite-field point counts at \(p = 2,3,5\);
- the integral discriminant \(\Delta = 5077\);
- the short-model discriminant;
- the exact integral-to-short coordinate change;
- a Nagell-Lutz candidate reduction;
- explicit rational points and their doubles.

It does not claim an analytic Birch and Swinnerton-Dyer theorem.  The package is
only the public algebraic and finite-data certificate layer.

The geometry of the two models is:

```text
Integral model:        y^2 + y = x^3 - 7x + 6

Change of variables:   Y = y + 1/2

Short model:           Y^2 = x^3 - 7x + 25/4
```

---

## II. Short-Weierstrass Core

> **Definition 1. Short Weierstrass model data.**
>
> The computational curve record stores the standard coefficients, although
> only `a4` and `a6` enter the short equation in this package.
>
> **In Lean:**
>
> ```lean
> structure CertifiedEC.EllipticCurve (K : Type) [Field K] where
>   a1 : K
>   a2 : K
>   a3 : K
>   a4 : K
>   a6 : K
> ```

> **Definition 2. Affine rational points.**
>
> A rational point is an affine pair satisfying
>
> $$
> y^2 = x^3 + a_4x + a_6.
> $$
>
> **In Lean:**
>
> ```lean
> structure CertifiedEC.RationalPoint
>     (E : EllipticCurve ℚ) where
>   x : ℚ
>   y : ℚ
>   on_curve : y ^ 2 = x ^ 3 + E.a4 * x + E.a6
> ```

> **Definition 3. Negation of an affine point.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.RationalPoint.neg
>     {E : EllipticCurve ℚ}
>     (P : RationalPoint E) : RationalPoint E
> ```

> **Definition 4. Addition by secant formula.**
>
> The package implements the explicit affine addition formula when the
> \(x\)-coordinates are distinct.
>
> **In Lean:**
>
> ```lean
> noncomputable def CertifiedEC.RationalPoint.addDistinct
>     {E : EllipticCurve ℚ}
>     (P Q : RationalPoint E) (hx : Q.x ≠ P.x) :
>     RationalPoint E
> ```

> **Definition 5. Doubling by tangent formula.**
>
> **In Lean:**
>
> ```lean
> noncomputable def CertifiedEC.RationalPoint.double
>     {E : EllipticCurve ℚ}
>     (P : RationalPoint E) (hy : P.y ≠ 0) :
>     RationalPoint E
> ```

> **Theorem 1. The secant formula is symmetric.**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.RationalPoint.addDistinct_comm
>     {E : EllipticCurve ℚ} (P Q : RationalPoint E)
>     (hQP : Q.x ≠ P.x) (hPQ : P.x ≠ Q.x) :
>     P.addDistinct Q hQP = Q.addDistinct P hPQ
> ```

> **Definition 6. Projective point type.**
>
> The projective point type adds the point at infinity.
>
> **In Lean:**
>
> ```lean
> inductive CertifiedEC.ECPoint (E : EllipticCurve ℚ) where
>   | infinity : ECPoint E
>   | affine (P : RationalPoint E) : ECPoint E
> ```

> **Definition 7. Projective addition.**
>
> **In Lean:**
>
> ```lean
> noncomputable def CertifiedEC.ECPoint.add
>     {E : EllipticCurve ℚ} :
>     ECPoint E → ECPoint E → ECPoint E
> ```

> **Theorem 2. Negation cancels a point.**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.ECPoint.neg_add_self
>     {E : EllipticCurve ℚ} (P : ECPoint E) :
>     -P + P = 0
> ```

> **Theorem 3. Projective addition is commutative.**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.ECPoint.add_comm
>     {E : EllipticCurve ℚ} (P Q : ECPoint E) :
>     P + Q = Q + P
> ```

> **Definition 8. Naive height.**
>
> **In Lean:**
>
> ```lean
> noncomputable def CertifiedEC.naiveHeight
>     {E : EllipticCurve ℚ} : ECPoint E → ℝ
> ```

---

## III. Finite-Field Counts

> **Definition 9. Reduction of the integral model modulo \(p\).**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.E5077Mod
>     (p : ℕ) [Fact p.Prime] :
>     WeierstrassCurve (ZMod p)
> ```

> **Definition 10. Affine points over \( \mathbb{F}_p \).**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.affinePointsFinset
>     (p : ℕ) [Fact p.Prime] :
>     Finset ((ZMod p) × (ZMod p))
> ```

> **Definition 11. Projective point count.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.N_p
>     (p : ℕ) [Fact p.Prime] : ℕ :=
>   (affinePointsFinset p).card + 1
> ```

> **Definition 12. Local Frobenius coefficient.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.a_p
>     (p : ℕ) [Fact p.Prime] : ℤ :=
>   (p : ℤ) + 1 - (N_p p : ℤ)
> ```

> **Theorem 4. Count over \( \mathbb{F}_2 \).**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.N_two : N_p 2 = 5
> theorem CertifiedEC.a_p_two : a_p 2 = -2
> ```

> **Theorem 5. Count over \( \mathbb{F}_3 \).**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.N_three : N_p 3 = 7
> theorem CertifiedEC.a_p_three : a_p 3 = -3
> ```

> **Theorem 6. Count over \( \mathbb{F}_5 \).**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.N_five : N_p 5 = 10
> theorem CertifiedEC.a_p_five : a_p 5 = -4
> ```

These finite certificates are kernel-checked with `decide`, avoiding trusted
compiled evaluation.

---

## IV. Integral and Short Models

> **Definition 13. The short model.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.E5077 : EllipticCurve ℚ where
>   a1 := 0
>   a2 := 0
>   a3 := 0
>   a4 := -7
>   a6 := 25 / 4
> ```

> **Definition 14. The integral model.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.E5077Integral : WeierstrassCurve ℤ :=
>   ⟨0, 0, 1, -7, 6⟩
> ```

> **Theorem 7. Integral discriminant.**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.delta_E5077_integral :
>     E5077Integral.Δ = 5077
> ```

> **Definition 15. Rational points on the integral model.**
>
> **In Lean:**
>
> ```lean
> structure CertifiedEC.IntegralModelRationalPoint where
>   x : ℚ
>   y : ℚ
>   on_curve : y ^ 2 + y = x ^ 3 - 7 * x + 6
> ```

> **Definition 16. Change to the short model.**
>
> The map is
>
> $$
> (x,y) \mapsto (x,y+1/2).
> $$
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.IntegralModelRationalPoint.toShort
>     (P : IntegralModelRationalPoint) :
>     RationalPoint E5077
> ```

> **Definition 17. Inverse change of variables.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.IntegralModelRationalPoint.ofShort
>     (P : RationalPoint E5077) :
>     IntegralModelRationalPoint
> ```

> **Definition 18. Equivalence of rational point models.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.IntegralModelRationalPoint.shortModelEquiv :
>     IntegralModelRationalPoint ≃ RationalPoint E5077
> ```

> **Definition 19. Integral points on the integral model.**
>
> **In Lean:**
>
> ```lean
> structure CertifiedEC.IntegralModelIntegerPoint where
>   x : ℤ
>   y : ℤ
>   on_curve : y ^ 2 + y = x ^ 3 - 7 * x + 6
> ```

> **Theorem 8. Cubic factorization.**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.IntegralModelIntegerPoint.cubic_factor
>     (x : ℤ) :
>     x ^ 3 - 7 * x + 6 = (x + 3) * (x - 1) * (x - 2)
> ```

> **Theorem 9. Nagell-Lutz candidate reduction.**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.IntegralModelIntegerPoint.coordinates_mem_nagellLutz_candidates
>     (P : IntegralModelIntegerPoint)
>     (hdiv : (2 * P.y + 1) ^ 2 ∣ (5077 : ℤ)) :
>     (P.x, P.y) ∈
>       ({(-3, 0), (-3, -1), (1, 0), (1, -1), (2, 0), (2, -1)}
>         : Finset (ℤ × ℤ))
> ```

> **Definition 20. Short discriminant.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.shortDiscriminant
>     (E : EllipticCurve ℚ) : ℚ :=
>   -16 * (4 * E.a4 ^ 3 + 27 * E.a6 ^ 2)
> ```

> **Theorem 10. Short discriminant of 5077a1.**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.shortDiscriminant_E5077 :
>     shortDiscriminant E5077 = 5077
> ```

---

## V. Certified 5077a1 Data

> **Definition 21. Certified rational points.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.P1_5077 : RationalPoint E5077
> def CertifiedEC.P2_5077 : RationalPoint E5077
> def CertifiedEC.Pm3_5077 : RationalPoint E5077
> def CertifiedEC.P3_5077 : RationalPoint E5077
> ```

The displayed coordinates are:

```text
P1  = (1,  1/2)
P2  = (2,  1/2)
Pm3 = (-3, 1/2)
P3  = (0,  5/2)
```

> **Definition 22. Certified doubles.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.twiceP1_5077 : RationalPoint E5077
> def CertifiedEC.twiceP2_5077 : RationalPoint E5077
> def CertifiedEC.twicePm3_5077 : RationalPoint E5077
> ```

The certified doubles are:

```text
2P1  = (14, 103/2)
2P2  = (21, -191/2)
2Pm3 = (406, -16361/2)
```

> **Theorem 11. Certified double of \(P_1\).**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.P1_add_self :
>     ECPoint.affine P1_5077 + ECPoint.affine P1_5077 =
>       ECPoint.affine twiceP1_5077
> ```

> **Theorem 12. Certified double of \(P_2\).**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.P2_add_self :
>     ECPoint.affine P2_5077 + ECPoint.affine P2_5077 =
>       ECPoint.affine twiceP2_5077
> ```

> **Theorem 13. Certified double of \(P_{-3}\).**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.Pm3_add_self :
>     ECPoint.affine Pm3_5077 + ECPoint.affine Pm3_5077 =
>       ECPoint.affine twicePm3_5077
> ```

> **Definition 23. Algebraic invariants as data.**
>
> These invariants are stored as certified data fields.  They are not an
> analytic BSD proof.
>
> **In Lean:**
>
> ```lean
> structure CertifiedEC.AlgebraicInvariants
>     (E : EllipticCurve ℚ) where
>   torsion_order : ℕ
>   h_tors_pos : 0 < torsion_order
>   tamagawa_product : ℕ
>   h_tam_pos : 0 < tamagawa_product
>   sha_order : ℕ
>   real_period : ℝ
>   h_period_pos : 0 < real_period
> ```

> **Definition 24. Three-point basis data.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.basis5077
>     (i : Fin 3) : RationalPoint E5077
> ```

> **Theorem 14. The integral point \((0,2)\) maps to \(P_3\).**
>
> **In Lean:**
>
> ```lean
> theorem CertifiedEC.integralP3_toShort :
>     integralP3.toShort = P3_5077
> ```

> **Definition 25. Nagell-Lutz candidate pairs.**
>
> **In Lean:**
>
> ```lean
> def CertifiedEC.nagellLutzCandidatePairs :
>     Finset (ℤ × ℤ) :=
>   {(-3, 0), (-3, -1), (1, 0), (1, -1), (2, 0), (2, -1)}
> ```

---

## VI. Architecture

The live file is fused in dependency order:

```text
Basic
  -> FiniteFieldCounts
    -> IntegralModel
      -> Entry5077a1
```

The package separates four layers:

- a reusable short-Weierstrass computational core;
- finite-field point counts;
- the integral and short models of 5077a1;
- concrete point and invariant certificates for the entry.

The mathematical spine is:

```text
y^2 + y = x^3 - 7x + 6
Y = y + 1/2
Y^2 = x^3 - 7x + 25/4
Delta = 5077
N_2 = 5, N_3 = 7, N_5 = 10
P1, P2, Pm3, P3 lie on E5077
2P1, 2P2, 2Pm3 are explicitly certified
```

---

## VII. Axiom Certificate

The representative certificate command is:

```text
echo 'import CertifiedElliptic5077
#print axioms CertifiedEC.delta_E5077_integral
#print axioms CertifiedEC.shortDiscriminant_E5077
#print axioms CertifiedEC.N_two
#print axioms CertifiedEC.N_three
#print axioms CertifiedEC.N_five
#print axioms CertifiedEC.P1_add_self
#print axioms CertifiedEC.P2_add_self
#print axioms CertifiedEC.Pm3_add_self
#print axioms CertifiedEC.integralP3_toShort' \
  | lake env lean --stdin
```

The current certificate is:

```text
'CertifiedEC.delta_E5077_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertifiedEC.shortDiscriminant_E5077' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertifiedEC.N_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertifiedEC.N_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertifiedEC.N_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertifiedEC.P1_add_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertifiedEC.P2_add_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertifiedEC.Pm3_add_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertifiedEC.integralP3_toShort' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There are no package-local axioms in these certificates.

---

## VIII. Reading Guide

For a first pass, read the file in this order:

1. `EllipticCurve`, `RationalPoint`, and the explicit addition formulas.
2. `N_p`, `a_p`, and the certified counts for \(p=2,3,5\).
3. `E5077Integral`, `E5077`, and the change of variables.
4. `delta_E5077_integral` and `shortDiscriminant_E5077`.
5. `P1_5077`, `P2_5077`, `Pm3_5077`, `P3_5077`.
6. `P1_add_self`, `P2_add_self`, `Pm3_add_self`.

The package is an algebraic and computational certificate.  It deliberately
does not claim an analytic BSD theorem.

---

## IX. Verification

The live file was checked with:

```text
lake env lean M4TH/CertifiedElliptic5077/CertifiedElliptic5077Live/CertifiedElliptic5077.live.lean
```

The package build command is:

```text
lake build CertifiedElliptic5077
```

Both checks are intended to be rerun before publication or Zulip discussion.
