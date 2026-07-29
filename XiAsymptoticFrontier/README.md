# XiAsymptoticFrontier

**Typed analytic frontier for the Riemann-von Mangoldt contour synthesis,
formalised in Lean 4 over Mathlib without trusted analytic declarations.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main Statement

The package replaces residual analytic assumptions by an explicit typed
frontier:

```lean
RiemannAsymptoticFrontier.AnalyticFrontier N Nsafe C
```

and proves the conditional synthesis:

```lean
RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_bridge
```

This says that if the typed contour frontier holds, then the multiplicity
zero-counting function is asymptotic to the classical Riemann-von Mangoldt main
term:

```lean
IsEquivalent atTop N vonMangoldtMainTerm
```

## Structure

```text
M4TH/XiAsymptoticFrontier/
  README.md
  lakefile.toml
  XiAsymptoticFrontier.lean
  XiAsymptoticFrontier.svg
  XiAsymptoticFrontier/
    Basic.lean
    Frontier.lean
    Synthesis.lean
```

| File | Contents |
|---|---|
| `XiAsymptoticFrontier/Basic.lean` | main term, normalized contour real part |
| `XiAsymptoticFrontier/Frontier.lean` | typed analytic frontier and negligible residual package |
| `XiAsymptoticFrontier/Synthesis.lean` | conditional Riemann-von Mangoldt synthesis |

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

## Certificate

After a successful build:

```text
echo 'import XiAsymptoticFrontier
#print axioms RiemannAsymptoticFrontier.residual_negligible
#print axioms RiemannAsymptoticFrontier.safe_counting_equiv_main
#print axioms RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_frontier
#print axioms RiemannAsymptoticFrontier.riemann_von_mangoldt_from_contour_bridge' \
  | lake env lean --stdin
```

Expected foundational output:

```text
[propext, Classical.choice, Quot.sound]
```

## Verification Status

This package is self-contained and depends only on Mathlib.  It contains no
package-local trusted declaration, no incomplete proof placeholder, and no
trusted compiled decision procedure.

## Review Items

- Connect `ContourComponents` to the concrete contour integrals of the preceding
  packages once the PNT+/Mathlib rectangular-residue dependency is fixed.
- Replace individual fields of `AnalyticFrontier` by imported theorems as the
  analytic estimates are formalised.
- Keep the synthesis theorem conditional and explicit until all frontier fields
  are independently proved.
