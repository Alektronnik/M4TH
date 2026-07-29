# KdV

**Exact one-soliton profile and conservation laws for the Korteweg-de Vries
equation, formalised in Lean 4 over Mathlib — with zero axioms and zero
`sorry`.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main statement

For the normalization

```
u_t + u u_x + u_xxx = 0
```

the travelling-wave ansatz `u(t, x) = f (x - c t)` reduces the PDE to the
stationary soliton ODE

```
-c f' + f f' + f''' = 0
```

and the classical one-soliton profile

```
f(x) = 3 c sech^2 ((sqrt c / 2) x)
```

satisfies that ODE for every `c > 0`:

```lean
theorem KdV.soliton_satisfies_kdv (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    -c * deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) ξ +
      (3 * c * sech (Real.sqrt c / 2 * ξ) ^ 2) *
        deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) ξ +
      deriv (fun y => deriv (fun z =>
        deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) z) y) ξ = 0
```

For compactly supported smooth KdV solutions, the package also proves the rate
forms of mass and quadratic energy conservation:

```lean
theorem KdV.ConservedSolution.massRate_conserved
theorem KdV.ConservedSolution.energyRate_conserved
```

## Structure

| File | Contents | Intended Mathlib PR |
|---|---|---|
| `KdV/Basic.lean` | `IsSolution`, `TravellingWave`, affine chain rules, travelling-wave reduction | PR-2 |
| `KdV/Hyperbolic.lean` | `sech`, `solitonProfile`, `sech^2 = 1 - tanh^2`, derivatives of `sech` and `tanh` composites | PR-1 |
| `KdV/Soliton.lean` | explicit first/third derivatives of the squared-sech profile and **`soliton_satisfies_kdv`** | PR-3 |
| `KdV/ConservationLaws.lean` | compact-support integration identities, `ConservedSolution`, mass and energy conservation | PR-4 |
| `KdV.lean` | root module aggregating the package | packaging |

Each file compiles on top of the previous ones only; the PR series can be opened
in this order, with the special-function calculus split off before the
PDE-specific files.

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
echo 'import KdV
#print axioms KdV.travellingWave_reduction
#print axioms KdV.soliton_satisfies_kdv
#print axioms KdV.ConservedSolution.massRate_conserved
#print axioms KdV.ConservedSolution.energyRate_conserved' \
  | lake env lean --stdin
```

Every command must report **only** the foundational axioms of Lean:
`propext`, `Classical.choice`, `Quot.sound`.  Any other axiom is a defect.

## Verification status

This package is organised as a standalone Mathlib-style contribution: English
documentation, Mathlib naming conventions, per-file copyright headers and module
docstrings, a standalone Lake package, and an explicit split between reusable
hyperbolic-function calculus and KdV-specific PDE results.

The Mathlib revision is already pinned for reproducibility.
axiom certificate before Zulip discussion or a pull request.

## Review items (flagged for the PR conversation)

1. Check whether Mathlib already has a named `Real.sech` or derivative lemmas in
   `Analysis/SpecialFunctions/Trigonometric/DerivHyp`; contribute only the
   genuinely missing `sech` API.
2. Replace `integral_deriv_eq_zero` with any existing compact-support theorem if
   Mathlib already has one; otherwise contribute it in maximal generality before
   the KdV-specific conservation file.
3. The current conservation lemmas prove the cases needed for mass and energy.
   The protocol recommends generalising `∫ u^k u_x = 0` for all natural `k` as a
   more valuable library lemma before upstreaming.
4. Import lists are generous; minimise with the import linter before opening
   each PR.

## Naming notes

| Concept | Name in this package |
|---|---|
| Smooth KdV solution predicate | `IsSolution` |
| Travelling-wave profile field | `TravellingWave.profile` |
| Time derivative of the ansatz | `travellingWave_deriv_time` |
| Spatial derivative of the ansatz | `travellingWave_deriv_space` |
| Third spatial derivative of the ansatz | `travellingWave_deriv_space3` |
| Travelling-wave reduction | `travellingWave_reduction` |
| Hyperbolic secant | `sech` |
| Soliton profile | `solitonProfile` |
| Squared-sech identity | `sech_sq_eq_one_sub_tanh_sq` |
| Exact soliton theorem | `soliton_satisfies_kdv` |
| Compact-support solution structure | `ConservedSolution` |
| Time and spatial derivatives | `ut`, `ux`, `uxxx` |
| Mass conservation rate | `ConservedSolution.massRate_conserved` |
| Energy conservation rate | `ConservedSolution.energyRate_conserved` |
