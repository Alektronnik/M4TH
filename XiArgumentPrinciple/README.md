# XiArgumentPrinciple

**Critical-box argument-principle chain for the entire Riemann Xi variant,
formalised in Lean 4 over Mathlib with the external rectangular residue
ingredient exposed as explicit hypotheses.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main Statement

The package defines the critical-box contour integral of `entireXiLogDeriv` and
packages the argument-principle counting step:

```lean
RiemannArgumentPrinciple.contour_winding_equals_count_of_safe
```

The theorem is conditional on:

```lean
RiemannArgumentPrinciple.ArgumentPrincipleBridge T
```

This bridge records the external rectangular argument-principle facts:

- Cauchy index `+1` for points inside the critical box;
- Cauchy index `0` outside the critical box;
- residue sum equals the local multiplicity sum.

These are explicit hypotheses, not trusted declarations.  This keeps the
package publication-safe while marking the exact analytic interface expected
from a future PNT+/Mathlib rectangular-residue dependency.

## Structure

```text
M4TH/XiArgumentPrinciple/
  README.md
  lakefile.toml
  XiArgumentPrinciple.lean
  XiArgumentPrinciple.svg
  XiArgumentPrinciple/
    Basic.lean
    Contour.lean
    Counting.lean
```

| File | Contents |
|---|---|
| `XiArgumentPrinciple/Basic.lean` | `entireXi`, critical box, safe height, zero finset, multiplicity count |
| `XiArgumentPrinciple/Contour.lean` | edge parametrizations, contour integral, rectangular integral equivalence |
| `XiArgumentPrinciple/Counting.lean` | typed argument-principle bridge and contour-counting theorem |

## Build

From the repository root:

```text
lake build XiArgumentPrinciple
```

## Certificate

After a successful build:

```text
echo 'import XiArgumentPrinciple
#print axioms RiemannArgumentPrinciple.entireXiContourIntegral_eq_rectangleIntegral
#print axioms RiemannArgumentPrinciple.contour_winding_index_one_of_safe
#print axioms RiemannArgumentPrinciple.contour_residue_sum_equals_N_of_safe
#print axioms RiemannArgumentPrinciple.contour_winding_equals_count_of_safe' \
  | lake env lean --stdin
```

Expected foundational output:

```text
[propext, Classical.choice, Quot.sound]
```

## Verification Status

The package is self-contained and depends only on Mathlib.  It contains no
package-local trusted declaration, no incomplete proof placeholder, and no
trusted compiled decision procedure.

## Review Items

- Replace `ArgumentPrincipleBridge` with imported rectangular residue theorems
  once the target dependency is fixed.
- Keep the bridge as a named interface while coordinating with PNT+/Mathlib
  maintainers.
- Do not merge this package with `XiLogResidue`; both packages are intentionally
  self-contained until PR deduplication.
