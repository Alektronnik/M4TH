# SU3Concrete

**Concrete `su(3)` from Gell-Mann matrices: adjoint representation, Killing
form, Cartan generators and Casimirs, formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main statement

The package constructs the compact real Lie algebra `su(3)` concretely as
anti-Hermitian trace-zero `3 × 3` complex matrices, with Gell-Mann generators
`Tᵃ = iλₐ`.  It proves the core identities needed by the Yang-Mills mass-gap
corpus:

```lean
theorem Physics.YangMills.gellMannGenerator_antiHermitian
theorem Physics.YangMills.generator_commutator_matrix
theorem Physics.YangMills.structureConstant_jacobi
theorem Physics.YangMills.adjointCasimir_diagonal
theorem Physics.YangMills.killingFormBasis_diagonal
theorem Physics.YangMills.generator_trace_fundamental
theorem Physics.YangMills.fundamentalCasimir_diagonal
```

The convention is anti-Hermitian:

```
Tᵃ = i λₐ
[Tᵃ, Tᵇ] = -2 f^{abc} Tᶜ
κ(Tᵃ, Tᵇ) = -3 δᵃᵇ
∑ₐ TᵃTᵃ = -(16/3) I₃
```

## Structure

| File | Contents | Intended Physlib/Mathlib PR |
|---|---|---|
| `SU3Concrete/GellMann.lean` | `Matrix3x3`, Hermitian Gell-Mann matrices, anti-Hermitian generators, `LieAlgebraSU3` | PR-1 |
| `SU3Concrete/LieAlgebra.lean` | `su(3)` as a real submodule, matrix commutator, `LieRing` and `LieAlgebra ℝ` instances | PR-2 |
| `SU3Concrete/StructureConstants.lean` | explicit `f^{abc}`, antisymmetry, cyclicity, Jacobi and Casimir certificates | PR-3 |
| `SU3Concrete/Commutator.lean` | 64-entry Gell-Mann commutator table and relation to structure constants | PR-4 |
| `SU3Concrete/Representation.lean` | adjoint matrices, adjoint Casimir, Killing form, Cartan pair, fundamental trace identity and Casimir | PR-5 |
| `SU3Concrete.lean` | root module aggregating the package | packaging |

The most likely destination is Physlib for the physics convention and Gell-Mann
API.  Generic matrix/Lie-algebra lemmas can be split into Mathlib PRs if the
reviewers prefer.

## Build

```
# Mathlib is already pinned in lakefile.toml (rev fabf563a, Lean 4 v4.31.0).
lake update
lake exe cache get
lake build SU3Concrete
```

## Axiom certificate

After a successful build:

```
echo 'import SU3Concrete
#print axioms Physics.YangMills.gellMannGenerator_antiHermitian
#print axioms Physics.YangMills.generator_commutator_matrix
#print axioms Physics.YangMills.structureConstant_jacobi
#print axioms Physics.YangMills.adjointCasimir_diagonal
#print axioms Physics.YangMills.killingFormBasis_diagonal
#print axioms Physics.YangMills.fundamentalCasimir_diagonal' \
  | lake env lean --stdin
```

Every command must report only Lean's foundational axioms:
`propext`, `Classical.choice`, `Quot.sound`.  Any other axiom is a defect.

## Verification status

This package is organised as a standalone contribution: standalone Lake package layout,
English docstrings, per-file headers, and no imported private corpus modules.

The package does not declare axioms for the structure constants or the
commutator table.  The commutator table is certified by finite case analysis;
the structure-constant contractions are certified by kernel-checked finite
integer computations.

After fixing the Mathlib pin in `lakefile.toml`, run `lake build` and re-run the
axiom certificate before any Zulip announcement or pull request.

## Review items

1. The finite certificates in `SU3Concrete/StructureConstants.lean` are now
   kernel-pure but moderately expensive.  If CI is slow, replace them with a
   small verified reflection procedure, not axioms.
2. Check Physlib's existing matrix conventions for Pauli/Gell-Mann generators
   and align names before upstreaming.
3. Decide destination split: concrete Gell-Mann physics API likely belongs in
   Physlib; generic submodule/Lie bracket lemmas may belong in Mathlib.
4. Import lists are generous; minimise with the import linter before PRs.

## Naming notes

| Source name | This package |
|---|---|
| `Matrix3x3` | unchanged |
| `gellMannLambda8` | unchanged |
| `gellMannHermitian` | unchanged |
| `gellMannGenerator` | unchanged |
| `LieAlgebraSU3` | unchanged |
| `gellMannLieAlgebra` | unchanged |
| `structureConstant` | unchanged, now with theorem certificates |
| `structureConstant_antisymm`, `structureConstant_cyclic`, `structureConstant_jacobi`, `structureConstant_casimir` | theorem certificates, not axioms |
| `gellMannCommutatorMatrix` | unchanged |
| `generator_commutator_matrix` | theorem certificate, not axiom |
| `gellMann_commutator_structure` | theorem certificate, not axiom |
| `adjointMatrix`, `adjointCasimir` | unchanged |
| `killingFormBasis` | unchanged |
| `cartanIndex1`, `cartanIndex2` | unchanged |
| `generator_trace_fundamental`, `fundamentalCasimir` | unchanged |
