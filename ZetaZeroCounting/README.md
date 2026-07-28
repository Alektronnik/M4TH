# ZetaZeroCounting

**Zero-counting infrastructure for the Riemann zeta function — the counting
function N(T) with multiplicities, safe heights, and the asymptotic theory of
the von Mangoldt main term — formalised in Lean 4 over Mathlib, with zero
axioms and zero `sorry`.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main statement

For the entire Xi function `entireXi s = s (s - 1) completedRiemannZeta₀ s + 1`
(nonvanishing at the corners `0, 1`, agreeing with
`s (s - 1) completedRiemannZeta s` elsewhere), the package defines the
canonical zero-counting function of the Riemann–von Mangoldt theory,

```
noncomputable def Riemann.zeroCountingFun (T : ℝ) : ℝ :=
  Nat.cast ((zerosUpToImFinset T).sum entireXiZeroMultiplicity)
```

summing the **analytic multiplicities** (`analyticOrderNatAt`) of the
nontrivial zeros with `0 < Im s ≤ T`, and proves unconditionally: finiteness
and discreteness of the counting domain (via Mathlib's `ZetaZeros` and the
isolated-zeros principle), multiplicity `≥ 1` at every counted zero, hence
`distinctZeroCount ≤ zeroCountingFun` with equality under the classical
simplicity hypothesis; the symmetry `s ↦ 1 - s` of the nontrivial zeros and
the functional equation of `ξ`; **density of safe heights** (every interval
`(T, T + ε]` contains a height avoided by all zero ordinates); unconditional
nonvanishing of `ξ` on the top edge at safe heights and on both vertical
edges away from the corners; and the full asymptotic theory of the main term
`(T / 2π)(log (T / 2π) - 1)`, including `T = o(mainTerm)` and
`log = o(mainTerm)`.

The Riemann–von Mangoldt theorem itself,
`distinctZeroCount ~ vonMangoldtMainTerm`, is **stated** as the typed `Prop`
`Riemann.RiemannVonMangoldtCounting` and never assumed: its proof belongs to
the argument-principle series over the critical box (the sibling contour
packages), and the one consequence recorded here takes it as an explicit
hypothesis.

## Structure

The whole package is contained in this directory:

```
M4TH/ZetaZeroCounting/
  README.md
  ZetaZeroCounting.lean
  ZetaZeroCounting/
    Xi.lean
    ZeroCounting.lean
    SafeHeights.lean
    MainTerm.lean
```

| File | Contents | Intended Mathlib PR |
|---|---|---|
| `ZetaZeroCounting.lean` | Root module re-exporting the package | package root |
| `ZetaZeroCounting/Xi.lean` | `riemannXi`, `entireXi`, nontrivial zeros, zero symmetry, functional equation, completed-zeta glue, two-way zero dictionary | PR-1 |
| `ZetaZeroCounting/ZeroCounting.lean` | Critical box, finiteness of the counting domain, discreteness and multiplicities, `zeroCountingFun`, `distinctZeroCount`, comparisons | PR-2 (domain + finiteness) and PR-3 (multiplicity count) |
| `ZetaZeroCounting/SafeHeights.lean` | `IsSafeHeight`, forbidden heights, density of safe heights, edge nonvanishing | PR-4 |
| `ZetaZeroCounting/MainTerm.lean` | Main term, asymptotic equivalences, domination lemmas, the typed counting statement, certificates | PR-5 |

Each file compiles on top of the previous ones only; the PR series can be
opened in this order, each self-contained and useful on its own.

For a Mathlib PR, the intended final location is
`Mathlib/NumberTheory/LSeries/ZetaZeroCounting.lean` and
`Mathlib/NumberTheory/LSeries/ZetaZeroCounting/*.lean`, with imports renamed
accordingly.

## Relation to sibling packages

This package is intentionally **self-contained**: it depends only on Mathlib.
The `criticalBox` family of `ZeroCounting.lean` will also be needed by the
contour package of the argument-principle series; as with the
`ConservationLaws`/`BurgersBlowUp` pair, the duplication exists only at the
package level and is resolved at Mathlib-PR time by a single shared PR.

## Build

```
lake update
lake exe cache get
lake build ZetaZeroCounting
```

## Axiom certificate

After a successful build:

```
echo 'import ZetaZeroCounting
#print axioms Riemann.zerosUpToIm_finite
#print axioms Riemann.distinctZeroCount_le_zeroCountingFun
#print axioms Riemann.one_sub_mem_nontrivialZeros
#print axioms Riemann.exists_safe_height_above
#print axioms Riemann.T_isLittleO_vonMangoldtMainTerm' \
  | lake env lean --stdin
```

Every command must report **only** the foundational axioms of Lean:
`propext`, `Classical.choice`, `Quot.sound`.  Any other axiom is a defect.

## Verification status

This package has been prepared as a self-contained Mathlib-oriented component:
English throughout, Mathlib naming conventions, per-file copyright headers,
module docstrings, and no package-local axioms. The Riemann-von Mangoldt
counting theorem is deliberately recorded only as the typed `Prop`
`RiemannVonMangoldtCounting`; the package does not assume it. The only
consequence involving that statement takes it as an explicit hypothesis.

Current local status: `lake build ZetaZeroCounting` succeeds, and the axiom
certificate reports only `propext`, `Classical.choice`, and `Quot.sound` for
the package's advertised declarations.

## Review items (flagged for the PR conversation)

1. Final global names are a review decision with the Mathlib zeta authors
   (Loeffler, Stoll): this package currently uses the `Riemann` namespace;
   candidates such as `riemannZeta.zeroCountingFun` and the fate of
   `vonMangoldtMainTerm` (no collision with `ArithmeticFunction.vonMangoldt`
   inside the namespace, but the global name should be negotiated) are open.
2. Whether `zeroCountingFun` should be defined through
   `MeromorphicOn.divisor` (Kebekus) instead of `analyticOrderNatAt` is a
   design question for review; the divisor comparison belongs to the residue
   package of this series.
3. Overlap with the StrongPNT project (zero-free regions, log-derivative
   bounds) must be checked on Zulip before opening PR-4.
4. Import lists are generous; minimise with the import linter before opening
   each PR.
5. The `criticalBox` family is shared with the future contour package
   (single shared PR at Mathlib time).

## Naming notes

The package uses Mathlib-style descriptive names for public declarations:
`nontrivialZeros`, `zeroCountingFun`, `distinctZeroCount`,
`one_sub_mem_nontrivialZeros`, and
`distinctZeroCount_le_zeroCountingFun`. Final names should be confirmed with
the Mathlib reviewers before opening the corresponding PRs.
