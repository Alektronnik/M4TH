# XiLogResidue

**Logarithmic residue of the entire Riemann Xi variant and its dictionary with
Mathlib's meromorphic divisor, formalised in Lean 4 over Mathlib with no
package-local trusted constants and no incomplete proof placeholders.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main Statement

The package proves that the local logarithmic residue of the entire Xi variant
at a zero is its analytic multiplicity:

```lean
RiemannLogResidue.entireXi_logDeriv_residue_eq_multiplicity
```

It also relates the meromorphic divisor of `entireXi` on a critical box to the
same analytic multiplicity:

```lean
RiemannLogResidue.entireXi_divisor_eq_multiplicity
```

and identifies the finite divisor support in the critical box with the finite
set of nontrivial zeros counted by height, under the explicit safe-height and
boundary nonvanishing hypotheses:

```lean
RiemannLogResidue.entireXi_divisor_finset_eq_zerosUpToImFinset
```

The package is self-contained.  It depends only on Mathlib and does not import
any sibling package from this repository.

## Structure

```text
M4TH/XiLogResidue/
  README.md
  lakefile.toml
  XiLogResidue.lean
  XiLogResidue.svg
  XiLogResidue/
    Basic.lean
    LocalResidue.lean
    Divisor.lean
```

| File | Contents | Intended Mathlib PR |
|---|---|---|
| `XiLogResidue/Basic.lean` | `entireXi`, `criticalBox`, `zerosUpToImFinset`, analytic multiplicity | `NumberTheory/LSeries` |
| `XiLogResidue/LocalResidue.lean` | local logarithmic residue equals analytic multiplicity | coordinated with meromorphic divisor API |
| `XiLogResidue/Divisor.lean` | dictionary between `MeromorphicOn.divisor` and analytic multiplicity | coordinated with ProjectVD/Kebekus divisor infrastructure |

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
echo 'import XiLogResidue
#print axioms RiemannLogResidue.entireXi_logDeriv_residue_eq_multiplicity
#print axioms RiemannLogResidue.entireXi_logResidue_equals_multiplicity
#print axioms RiemannLogResidue.entireXi_divisor_eq_multiplicity
#print axioms RiemannLogResidue.entireXi_divisor_finset_eq_zerosUpToImFinset' \
  | lake env lean --stdin
```

Every command must report only the standard foundational axioms used by Mathlib:

```text
[propext, Classical.choice, Quot.sound]
```

Any additional foundational dependency is a defect.

## Verification Status

This package is self-contained and depends only on Mathlib.  It contains no
package-local trusted constant, no incomplete proof placeholder, and no trusted
compiled decision procedure.

## Review Items

- Coordinate with the Mathlib meromorphic-divisor maintainers before proposing
  a general abstraction.
- Decide whether the first PR should expose the concrete Xi instance or first
  generalize the local logarithmic-residue lemma.
- The support-finset theorem is intentionally conditional on safe height and
  boundary nonvanishing; it does not claim a zero-free boundary theorem by
  itself.
