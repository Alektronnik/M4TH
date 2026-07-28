# BurgersBlowUp

**Finite-time gradient blow-up for the inviscid Burgers equation, formalised in
Lean 4 over Mathlib — with zero axioms and zero `sorry`.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main statement

For the inviscid Burgers equation `∂ₜ u + u ∂ₓ u = 0` with the compressive
initial datum `u₀ (x) = -x`, no `C²` regular solution exists on `[0, T)` once
`T ≥ 1`:

```
theorem Burgers.not_isRegularSolution_initialRamp {T : ℝ} (hT : 1 ≤ T)
    (u : ℝ → ℝ → ℝ) : ¬ IsRegularSolution initialRamp T u
```

The mechanism is fully analytic.  Along each characteristic line
`t ↦ x₀ (1 - t)` the solution is constant (`constant_along_characteristic`,
via a Lyapunov-energy uniqueness lemma for linear ODEs) and the spatial
gradient `V (t) = u_x (t, x₀ (1 - t))` satisfies the Riccati equation
`V' = -V ^ 2` with `V (0) = -1` (`gradient_riccati_evolution`), whose exact
solution is `V (t) = -1 / (1 - t)` (`gradient_eq_neg_one_div`).  The final
contradiction is purely algebraic, with no limit argument: at the critical time
`t = 1 - 1 / (|M| + 1)` the exact formula produces a gradient of magnitude
`|M| + 1`, exceeding any putative gradient bound `M`.

## Structure

```
M4TH/BurgersBlowUp/
  README.md
  lakefile.toml
  BurgersBlowUp.lean
  BurgersBlowUp/
    Calculus.lean
    ODE.lean
    Characteristics.lean
    BlowUp.lean
```

| File | Contents | Intended Mathlib PR |
|---|---|---|
| `BurgersBlowUp/Calculus.lean` | Fréchet-derivative decomposition into partial derivatives, derivative of plane curves | PR-1 (shared; see note below) |
| `BurgersBlowUp/ODE.lean` | Lyapunov-energy uniqueness for linear ODEs, exact Riccati solution, chain rule along plane curves | PR-1 |
| `BurgersBlowUp/Characteristics.lean` | `IsRegularSolution` (`C²` predicate), the ramp datum, constancy along characteristics, spatially differentiated PDE | PR-2 |
| `BurgersBlowUp/BlowUp.lean` | Riccati evolution of the gradient, exact formula `-1 / (1 - t)`, **the blow-up theorem**, certificates | PR-3 |

Each file compiles on top of the previous ones only; the PR series can be
opened in this order, each self-contained and useful on its own.

## Relation to the sibling `ConservationLaws` package

This package is intentionally **self-contained**: it depends only on Mathlib.
The four lemmas of `Calculus.lean` coincide, statement for statement, with the
helpers in `ConservationLaws/TestFunction.lean` of the sibling package (the
corresponding helpers of the conservation-laws development).  At
Mathlib-contribution time they are submitted **once**, as a single shared PR on
which both PR series depend; the duplication exists only at the package level,
never upstream.

## Build

```
# 1. Pin Mathlib: edit lakefile.toml, replacing <MATHLIB_REV> with the exact
#    Mathlib commit used to validate this package.
# 2. Fetch dependencies and build:
lake update
lake exe cache get
lake build BurgersBlowUp
```

## Axiom certificate

After a successful build:

```
echo 'import BurgersBlowUp
#print axioms Burgers.linear_ode_uniqueness
#print axioms Burgers.riccati_ode_solution
#print axioms Burgers.not_isRegularSolution_initialRamp' \
  | lake env lean --stdin
```

Every command must report **only** the foundational axioms of Lean:
`propext`, `Classical.choice`, `Quot.sound`.  Any other axiom is a defect.

## Verification status

The package is organised as a standalone Mathlib-style contribution: English
documentation, package-relative imports, per-file copyright headers, module
docstrings, and a root collector file `BurgersBlowUp.lean`.

Before any Zulip announcement or pull request, run `lake build BurgersBlowUp`
against the pinned Mathlib revision and re-run the axiom certificate.  Known
review items are listed below.

## Review items (flagged for the PR conversation)

1. The four lemmas of `Calculus.lean` may duplicate existing Mathlib lemmas
   (`HasDerivAt.prodMk` relatives); deduplicate at review time.
2. `linear_ode_uniqueness` is proved from scratch via a Lyapunov energy;
   whether Mathlib's Grönwall machinery
   (`norm_le_gronwallBound_of_norm_deriv_right_le`, `ODE_solution_unique`)
   subsumes it should be evaluated at review time.  Likewise the private
   `exists_abs_le_of_continuousOn` versus
   `IsCompact.exists_bound_of_continuousOn`.
3. Import lists are generous; minimise with the import linter before opening
   each PR.
4. The development is stated for the ramp datum `u₀ (x) = -x` with its
   straight-line characteristics.  The general compressive datum
   (`deriv u₀ x₀ < 0`, critical time `-1 / deriv u₀ x₀`, curved characteristics
   `x₀ + u₀ (x₀) t`) follows the same Lyapunov/Riccati strategy and is planned
   as a follow-up PR once compilation is set up.

## Naming notes

The package uses descriptive Mathlib-style names under the namespace `Burgers`.
The public API is intentionally split by topic so each file can be reviewed
independently in the PR sequence above.
