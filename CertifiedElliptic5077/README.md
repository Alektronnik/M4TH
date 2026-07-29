# CertifiedElliptic5077

**A certified computational kit for the LMFDB/Cremona elliptic-curve entry
5077a1, formalised in Lean 4 over Mathlib with no package-local `axiom` and no
`sorry`.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main Statement

The package isolates a reusable computational layer for short Weierstrass
curves over `Q`, then certifies the concrete curve

```lean
y^2 + y = x^3 - 7*x + 6
```

and its short model

```lean
Y^2 = x^3 - 7*x + 25/4
```

with discriminant `5077`.  It includes the exact change of coordinates
`Y = y + 1/2`, finite local point counts at small primes, Nagell-Lutz candidate
reductions for integral points, and explicit rational points with checked
doubles.

```lean
theorem CertifiedEC.delta_E5077_integral
theorem CertifiedEC.shortDiscriminant_E5077
theorem CertifiedEC.N_two
theorem CertifiedEC.N_three
theorem CertifiedEC.N_five
theorem CertifiedEC.P1_add_self
theorem CertifiedEC.P2_add_self
theorem CertifiedEC.Pm3_add_self
theorem CertifiedEC.integralP3_toShort
```

## Structure

| File | Contents | Intended Mathlib PR |
|---|---|---|
| `CertifiedElliptic5077/Basic.lean` | short Weierstrass record, affine/projective point types, explicit secant/tangent formulas, naive heights | PR-1 |
| `CertifiedElliptic5077/FiniteFieldCounts.lean` | finite-field model of 5077a1 and certified counts for `p = 2, 3, 5` | PR-2 |
| `CertifiedElliptic5077/IntegralModel.lean` | integral model, short model, discriminants, coordinate equivalence, Nagell-Lutz candidate reduction | PR-3 |
| `CertifiedElliptic5077/Entry5077a1.lean` | explicit certified 5077a1 data: points, doubles, invariants, basis data and candidate list | PR-4 |
| `CertifiedElliptic5077.lean` | root module aggregating the package and generating `CertifiedElliptic5077.svg` | packaging |

## Build

This package is part of the **M4TH monorepo**.  Build the whole monorepo from
the root:

```bash
cd ..
lake build
```

Or build this package independently from its own directory:

```bash
lake build
```

## Axiom Certificate

After a successful build:

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

Every command should report only Lean's foundational axioms:
`propext`, `Classical.choice`, `Quot.sound`.

## Verification Status

This package certifies the 5077a1 integral model, its short model,
discriminant computations, finite local counts, explicit rational points and
checked additions.

The analytic Birch and Swinnerton-Dyer statement is intentionally not claimed
here.  This package certifies only the algebraic and finite computational data
listed above.

## Review Items

1. Replace the lightweight local `EllipticCurve`/`RationalPoint` API with
   Mathlib's mature Weierstrass-curve point API where possible.
2. Generalize the finite-field point-counting certificate from the three small
   primes to a reusable counted-affine-points interface.
3. Split the Nagell-Lutz candidate reduction from the 5077a1-specific entry so
   the divisibility argument can be reused for other integral models.
4. Minimize imports with the import linter before PR discussion.

## Naming Notes

| Mathematical object | This package |
|---|---|
| short model of 5077a1 | `CertifiedEC.E5077` |
| integral model of 5077a1 | `CertifiedEC.E5077Integral` |
| integral discriminant | `CertifiedEC.delta_E5077_integral` |
| short discriminant | `CertifiedEC.shortDiscriminant_E5077` |
| first rational point | `CertifiedEC.P1_5077` |
| second rational point | `CertifiedEC.P2_5077` |
| point from `(-3, 0)` | `CertifiedEC.Pm3_5077` |
| double of `P1_5077` | `CertifiedEC.twiceP1_5077` |
| double of `P2_5077` | `CertifiedEC.twiceP2_5077` |
| double of `Pm3_5077` | `CertifiedEC.twicePm3_5077` |
| Nagell-Lutz candidate reduction | `CertifiedEC.IntegralModelIntegerPoint` |
