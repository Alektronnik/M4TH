# MertensPNT

**Mertens' theorems: the unconditional correction/product layer and the
conditional PNT+ closure, formalised in Lean 4 over Mathlib with no
package-local `axiom` and no `sorry`.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main Statement

The package defines

```lean
ErdosReciprocals.partialSum n
ErdosReciprocals.partialProduct n
ErdosReciprocals.mertensConstant
ErdosReciprocals.mertensResidual n
```

and proves the unconditional compensated convergence of the Euler product:

```lean
theorem ErdosReciprocals.mertens_product_convergence
theorem ErdosReciprocals.tendsto_partialProduct_mul_exp_partialSum
theorem ErdosReciprocals.tendsto_partialProduct_mul_exp_partialSum_add_gamma
theorem ErdosReciprocals.partialProduct_tendsto_zero
```

The PNT+ boundary is kept in conditional form:

```lean
def ErdosReciprocals.MertensSecondTheorem : Prop
def ErdosReciprocals.MertensResidualVanishes : Prop

theorem ErdosReciprocals.mertens_second_theorem_iff_residual_vanishes
theorem ErdosReciprocals.mertens_euler_closure_conditional
```

## Structure

| File | Contents | Intended Mathlib/PNT+ PR |
|---|---|---|
| `MertensPNT/Basic.lean` | `partialSum`, `partialLogSum`, `partialProduct`, harmonic/product bounds, divergence, Chebyshev bridges and first Erdos lemmas | PR-1 |
| `MertensPNT/MertensConstant.lean` | Meissel-Mertens correction series, summability, `mertensConstant`, and one-sided asymptotic boundary | PR-2 |
| `MertensPNT/ErdosBlocks.lean` | explicit Erdos block endpoints, iterated subsequence, rate and log-sum growth certificates | PR-3 |
| `MertensPNT/MertensBridge.lean` | finite correction identity and unconditional compensated convergence of the Euler product | PR-4 |
| `MertensPNT/TTAOData.lean` | kernel-checked computational tables: primorial products, wheel sieves, sieve checkpoints | CertifiedData |
| `MertensPNT/Connections.lean` | subsequence/product connections, residual definitions and empirical bridge statements | PR-5 / data bridge |
| `MertensPNT/PNTFrontier.lean` | conditional PNT+ statements and Euler-product closure from `MertensSecondTheorem` | PNT+ coordination |
| `MertensPNT.lean` | root module aggregating the package and generating `MertensPNT.svg` | packaging |

## Build

```text
# Mathlib is already pinned in lakefile.toml (rev fabf563a, Lean 4 v4.31.0).
lake update
lake exe cache get
lake build MertensPNT
```

## Axiom Certificate

After a successful build:

```text
echo 'import MertensPNT
#print axioms ErdosReciprocals.mertens_product_convergence
#print axioms ErdosReciprocals.tendsto_partialProduct_mul_exp_partialSum_add_gamma
#print axioms ErdosReciprocals.mertens_second_theorem_iff_residual_vanishes
#print axioms ErdosReciprocals.mertens_euler_closure_conditional
#print axioms ErdosReciprocals.partialSum_erdosIter_ge_half_mul' \
  | lake env lean --stdin
```

Every command should report only Lean's foundational axioms:
`propext`, `Classical.choice`, `Quot.sound`.

## Verification Status

This package certifies the reusable `ErdosReciprocals` layer: the
Meissel-Mertens correction series, compensated Euler-product convergence,
Erdos block rates, finite computational data, and the conditional PNT+ closure.

The PNT+ closure remains conditional inside this standalone package.  This
package does not claim an unconditional Prime Number Theorem layer beyond the
formal hypotheses explicitly present in the Lean statements.

## Review Items

1. Coordinate first with Mathlib's prime-number-theorem development before
   upstreaming the PNT+ frontier names.
2. Remove pure re-export wrappers around Mathlib lemmas before a Mathlib PR.
3. Split the certified tables into a `CertifiedData` repository if reviewers do
   not want numerical data in the mathematics package.
4. Minimize imports with the import linter before PR discussion.

## Naming Notes

| Mathematical object | This package |
|---|---|
| reciprocal-prime partial sum | `ErdosReciprocals.partialSum` |
| logarithmic reciprocal-prime sum | `ErdosReciprocals.partialLogSum` |
| Euler product over primes | `ErdosReciprocals.partialProduct` |
| Meissel-Mertens prime correction | `ErdosReciprocals.mertensPrimeCorrection` |
| correction partial sum | `ErdosReciprocals.mertensPrimeCorrectionSum` |
| Mertens constant | `ErdosReciprocals.mertensConstant` |
| compensated correction | `ErdosReciprocals.partialMertensCorrection` |
| Euler-product convergence | `ErdosReciprocals.mertens_product_convergence` |
| compensated product limit | `ErdosReciprocals.tendsto_partialProduct_mul_exp_partialSum_add_gamma` |
| Erdos block data | `ErdosReciprocals.erdosBlockEnd`, `ErdosReciprocals.erdosIter` |
| residual layer | `ErdosReciprocals.mertensResidual`, `ErdosReciprocals.mertensScaledResidual` |
| conditional second theorem | `ErdosReciprocals.MertensSecondTheorem` |
| conditional Euler closure | `ErdosReciprocals.mertens_euler_closure_conditional` |
