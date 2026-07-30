# Poincare4D

**Smooth surgery chains, coupled Ricci-gauge flow contracts, and the conditional
smooth 4D Poincare theorem. Formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Perez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main Statement

The package defines smooth surgery data, finite surgery chains, and the
conditional smooth 4D Poincare theorem. The analytic PDE input (short-time
existence, parabolic regularity, Ricci-gauge equivalence) is exposed as
explicit typed hypotheses; no package-local axioms are introduced.

```lean
Poincare4D.smoothPoincare4D_conditional
```

The theorem is conditional on:

```lean
Poincare4D.H1.DeTurckIdentity
Poincare4D.H1.ParabolicShortTimeExistence
Poincare4D.H1.TimeDependentFlowExists
Poincare4D.H1.PullbackInvariance
```

These record the exact PDE facts the classical proof would invoke; they are
named, typed, and individually dischargeable.

## Package Structure

```
Poincare4D/
  README.md
  lakefile.toml
  Poincare4D.lean           (root aggregator + SVG generator)
  Poincare4D.svg
  Poincare4D/
    Basic.lean                       (topology, manifolds, metrics)
    Flow.lean                        (coupled Ricci-gauge flow contracts)
    Surgery.lean                     (surgery data, chains, preservation)
    Conditional.lean                 (conditional theorem + symmetric program)
  Poincare4DLive/
    Poincare4D.live.lean
    Poincare4D.live.MANUAL.md
```

## Build

```bash
# From the M4TH monorepo root
lake build Poincare4D

# Or standalone (from this package directory)
lake update
lake exe cache get
lake build
```

## Axiom Certificate

```bash
echo 'import Poincare4D
#print axioms Poincare4D.smoothPoincare4D_conditional' | lake env lean --stdin
```

Expected output: `[propext, Classical.choice, Quot.sound]`

## Verification

- Zero `axiom`, zero `sorry`, zero `native_decide`
- All analytic PDE inputs are explicit `Prop` hypotheses
- The conditional theorem carries the clean certificate
