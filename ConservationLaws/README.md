# ConservationLaws

**Weak solutions of scalar conservation laws, shock waves, Rankine–Hugoniot and
the Lax entropy condition, formalised in Lean 4 over Mathlib — with zero axioms
and zero `sorry`.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main statement

For the scalar conservation law `∂ₜ u + ∂ₓ (f (u)) = 0` on `(0, T) × ℝ` with an
**arbitrary** flux `f : ℝ → ℝ`, the distributional residual of the travelling
step `shockProfile uL uR s` against any smooth compactly supported test function
collapses exactly to the boundary integral of the Rankine–Hugoniot deficit along
the moving interface:

```
theorem ConservationLaw.hasShockIntegralReduction (f : ℝ → ℝ) (T uL uR s : ℝ) :
    ∀ φ : TestFunction T,
      weakResidual f (shockProfile uL uR s) φ =
        ∫ t in Ioo 0 T, ((f uL - f uR) - s * (uL - uR)) * φ t (s * t)
```

Consequently the step is a weak solution **iff** its speed satisfies
Rankine–Hugoniot (`isWeakSolution_shockProfile_of_rankineHugoniot`).  For the
Burgers flux `u ^ 2 / 2` the package additionally proves the Lax entropy theory
and the classical non-uniqueness pathology: the expansion step is a genuine weak
solution that violates the Lax condition and produces strictly positive entropy
dissipation (`expansion_midpoint_is_weak_but_not_entropic`).

## Structure

```
M4TH/ConservationLaws/
  README.md
  lakefile.toml
  ConservationLaws.lean
  ConservationLaws/
    TestFunction.lean
    WeakSolution.lean
    Galilean.lean
    ShockProfile.lean
    ShockReduction.lean
    Burgers.lean
```

| File | Contents | Intended Mathlib PR |
|---|---|---|
| `ConservationLaws/TestFunction.lean` | Test functions on the cylinder, partial derivatives, improper FTC, integrability | PR-1 (structure) + PR-2 (calculus) |
| `ConservationLaws/WeakSolution.lean` | `weakIntegrand`, `weakResidual`, `IsWeakSolution` for general flux; zero solution | PR-1 |
| `ConservationLaws/Galilean.lean` | Galilean frame, chain rule, joint derivatives, Fubini cancellation on half-planes | PR-3 |
| `ConservationLaws/ShockProfile.lean` | `shockProfile`, `RankineHugoniot`, local integrability, spatial split, shock classification | PR-4 |
| `ConservationLaws/ShockReduction.lean` | Spatial shifts, time marginals, half-plane collapses, **`hasShockIntegralReduction`** | PR-5 |
| `ConservationLaws/Burgers.lean` | Burgers flux, midpoint speed, Lax condition, entropy pair, admissibility and non-uniqueness, certificates | PR-6 |

Each file compiles on top of the previous ones only; the PR series can be opened
in this order, each self-contained and useful on its own.

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

## Axiom certificate

After a successful build:

```
echo 'import ConservationLaws
#print axioms ConservationLaw.hasShockIntegralReduction
#print axioms ConservationLaw.isWeakSolution_shockProfile_of_rankineHugoniot
#print axioms ConservationLaw.expansion_midpoint_is_weak_but_not_entropic' \
  | lake env lean --stdin
```

Every command must report **only** the foundational axioms of Lean:
`propext`, `Classical.choice`, `Quot.sound`.  Any other axiom is a defect.

## Verification status

The package is organised as a standalone Mathlib-style contribution: English
documentation, package-relative imports, per-file copyright headers, module
docstrings, and a root collector file `ConservationLaws.lean`.

Before any Zulip announcement or pull request, run `lake build
ConservationLaws` against the pinned Mathlib revision and re-run the axiom
certificate.  Known review items are listed below.

## Review items (flagged for the PR conversation)

1. `planeMeasure` is definitionally `volume` on `ℝ × ℝ` (`setIntegral_plane` is
   `rfl`); reviewers may prefer inlining it via
   `MeasureTheory.Measure.volume_eq_prod`.
2. `hasDerivAt_prodMk`, `fderiv_coord_fst`, `fderiv_coord_snd`,
   `fderiv_apply_decomp` may duplicate existing Mathlib lemmas; deduplicate at
   review time.
3. Import lists are generous; minimise with the import linter before opening
   each PR.
4. Hypotheses on the flux enter only where genuinely needed (`f 0 = 0` for the
   zero solution); the entropy theory is currently stated for the Burgers flux
   and nonnegative states — the convex-flux generalisation is future work.

## Naming notes

The package uses descriptive Mathlib-style names under the namespace
`ConservationLaw`.  The public API is intentionally split by topic so each file
can be reviewed independently in the PR sequence above.
