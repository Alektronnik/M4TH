# SU3Wilson

**The group `SU(3)`, the normalized trace bound, and positivity of Wilson
plaquette actions, formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main statement

The package constructs `SU(3)` as concrete `3 x 3` complex matrices satisfying
the special-unitary equations, proves its group structure, and establishes the
trace bound

```lean
theorem Physics.YangMills.su3_trace_re_bound (U : SU3) :
    -1 <= (matrixTraceSU3 U).re / 3 ∧ (matrixTraceSU3 U).re / 3 <= 1
```

From this, every Wilson plaquette term lies in `[0, 2]`, and the Wilson action
is nonnegative for nonnegative coupling:

```lean
theorem Physics.YangMills.wilsonTerm_nonneg
theorem Physics.YangMills.wilsonTerm_le_two
theorem Physics.YangMills.WilsonAction_nonneg
theorem Physics.YangMills.WilsonAction4D_nonneg
```

The 4D layer constructs plaquettes directly from link variables:

```lean
noncomputable def Physics.YangMills.plaquette4D
theorem Physics.YangMills.plaquette4D_diagonal
theorem Physics.YangMills.plaquette4D_trace_re_symm
```

## Structure

| File | Contents | Intended Physlib/Mathlib PR |
|---|---|---|
| `SU3Wilson/SU3.lean` | concrete `SU3`, group instance, trace and normalized real trace bound | PR-1 |
| `SU3Wilson/Wilson.lean` | finite lattice gauge field, `latticeSum`, Wilson term/action, positivity | PR-2 |
| `SU3Wilson/Lattice4D.lean` | constructive 4D sites, directions, links, plaquettes, Wilson action | PR-3 |
| `SU3Wilson.lean` | root module aggregating the package | packaging |

The likely destination is Physlib for the lattice-gauge convention.  If Mathlib
already has a suitable `Matrix.specialUnitaryGroup`, the PR version should be
rewritten on top of it and keep this package's contribution as the trace bound
and Wilson positivity layer.

## Build

```
# Mathlib is already pinned in lakefile.toml (rev fabf563a, Lean 4 v4.31.0).
lake update
lake exe cache get
lake build SU3Wilson
```

## Axiom certificate

After a successful build:

```
echo 'import SU3Wilson
#print axioms Physics.YangMills.su3_trace_re_bound
#print axioms Physics.YangMills.wilsonTerm_nonneg
#print axioms Physics.YangMills.WilsonAction_nonneg
#print axioms Physics.YangMills.plaquette4D_diagonal
#print axioms Physics.YangMills.WilsonAction4D_nonneg' \
  | lake env lean --stdin
```

Every command must report only Lean's foundational axioms:
`propext`, `Classical.choice`, `Quot.sound`.  Any other axiom is a defect.

## Verification status

This package is organised as a standalone contribution: standalone Lake package
layout, English docstrings, per-file headers, explicit finite lattice data, and
no imported private corpus modules.  `LatticeGaugeField` stores its link and
plaquette functions, and the 4D layer constructs plaquettes from link variables.

The Mathlib revision is already pinned for reproducibility.
axiom certificate before Zulip discussion or a pull request.

## Review items

1. Check whether `Matrix.specialUnitaryGroup` should replace the local `SU3`
   subtype in the upstream version.
2. Consider generalizing the trace bound to `SU(n)`:
   `|Re (Tr U)| <= n`, then specialize to `n = 3`.
3. The finite-lattice layer intentionally uses explicit plaquette data rather
   than global assumptions.  Physlib reviewers may prefer a bundled structure
   closer to their lattice-gauge API.
4. Import lists are generous; minimise with the import linter before PRs.

## Naming notes

| Concept | Name in this package |
|---|---|
| `SU3` | unchanged |
| `matrixTraceSU3` | unchanged |
| `oneSU3` | unchanged |
| `su3_trace_re_bound` | unchanged |
| `Lattice` | unchanged |
| `Direction` | unchanged |
| `getLink`, `Plaquette`, `Plaquette_diagonal` | replaced by fields of `LatticeGaugeField` |
| `latticeSum` | unchanged, now parameterized by explicit gauge-field data |
| `wilsonTerm` | unchanged, now uses `field.plaquette` |
| `WilsonAction` | unchanged, now uses explicit gauge-field data |
| `Lattice4D`, `Dir4`, `LinkVars4D` | unchanged |
| `plaquette4D`, `plaquette4D_diagonal` | unchanged |
| `wilsonTerm4D`, `WilsonAction4D` | unchanged |
| `timeReflection4D_on_links` | definition retained; time-reflection invariance is not claimed here |
