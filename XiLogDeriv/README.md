# XiLogDeriv

**Logarithmic-derivative expansion of the entire Riemann Xi variant, the
digamma identity for `Gammaℝ`, and continuity wrappers for `Complex.digamma`,
formalised in Lean 4 over Mathlib with no package-local `axiom` and no
`sorry`.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main Statement

The package isolates the analytic API needed to split the logarithmic derivative
of the entire Xi variant into its three formal components:

```lean
entireXiLogDeriv s =
  entireXiPolynomialLogDeriv s +
  gammaRFactorLogDeriv s +
  riemannZetaLogDeriv s
```

and proves the archimedean digamma identity

```lean
gammaRFactorLogDeriv s =
  -(1 / 2) * log (Real.pi : ℂ) + (1 / 2) * digamma (s / 2)
```

under the explicit hypothesis `Complex.Gammaℝ s ≠ 0`.

The package is a standalone extraction of the public, zero-axiom layer of the
Riemann-von Mangoldt contour series.  It does not import any sibling package
from this repository and does not cite unpublished source files.

## Structure

```text
M4TH/XiLogDeriv/
  README.md
  lakefile.toml
  XiLogDeriv.lean
  XiLogDeriv.svg
  XiLogDeriv/
    Basic.lean
    GammaR.lean
    DigammaContinuity.lean
    Expansion.lean
```

| File | Contents | Intended Mathlib PR |
|---|---|---|
| `XiLogDeriv/Basic.lean` | `entireXi`, polynomial factor, logarithmic derivatives, first-stage expansion | `NumberTheory/LSeries` |
| `XiLogDeriv/GammaR.lean` | `Gammaℝ` nonvanishing, differentiability, `Gammaℝ` digamma identity | `Analysis/SpecialFunctions/Gamma` |
| `XiLogDeriv/DigammaContinuity.lean` | continuity wrappers for `digamma` away from poles and on contour edges | `Analysis/SpecialFunctions/Gamma` |
| `XiLogDeriv/Expansion.lean` | full expansion of `entireXiLogDeriv` with and without digamma substitution | `NumberTheory/LSeries` |

The namespace is `RiemannLogDeriv`, not `Riemann`, so this standalone package
can coexist with `ZetaZeroCounting` in the same Lake workspace.  In a Mathlib
PR, names should be moved to the final namespace agreed with reviewers.

## Build

```
lake update
lake exe cache get
lake build XiLogDeriv
```

## Axiom Certificate

After a successful build:

```text
echo 'import XiLogDeriv
#print axioms RiemannLogDeriv.logDeriv_entireXiPolynomialFactor_eq
#print axioms RiemannLogDeriv.Complex_Gammaℝ_ne_zero_of_im_ne_zero
#print axioms RiemannLogDeriv.gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma
#print axioms RiemannLogDeriv.digamma_top_edge_continuousOn_Icc
#print axioms RiemannLogDeriv.entireXiLogDeriv_full_expansion_with_digamma' \
  | lake env lean --stdin
```

Every command must report only the standard foundational axioms used by Mathlib:

```text
[propext, Classical.choice, Quot.sound]
```

Any additional axiom is a defect.

## Verification Status

This package is self-contained and depends only on Mathlib.  It contains no
package-local axiom, no `sorry`, and no trusted compiled decision procedure.

Current local status: `lake build XiLogDeriv` succeeds, and the advertised
axiom certificate reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Review Items

- Decide with Mathlib reviewers whether the `Gammaℝ` nonvanishing and
  differentiability lemmas should live directly under `Complex`.
- Decide whether the full Xi expansion should import an eventual shared
  `entireXi` API from the zero-counting series, or keep the local definition
  until the PR series is merged.
- The theorem `entireXiLogDeriv_full_expansion_on_regular_boundary` exposes
  the nonvanishing hypotheses explicitly.  Later contour packages can discharge
  them from safe-height and boundary hypotheses.

