# DiscreteAbelChebyshev

**Discrete Abel summation and a typed Chebyshev-to-prime-counting bridge,
formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main Statements

The package proves the finite Abel summation identity:

```lean
DiscreteAbelChebyshev.abel_summation
```

and applies it to the discrete Chebyshev bridge:

```lean
DiscreteAbelChebyshev.pi_approx_eq_abel
DiscreteAbelChebyshev.pi_approx_final
```

The residual sum estimate is not represented by a trusted declaration.  It is
exposed as the typed hypothesis:

```lean
DiscreteAbelChebyshev.ChebyshevErrorSumBound
```

and the final transfer theorem is conditional:

```lean
DiscreteAbelChebyshev.chebyshev_implies_prime_error
```

## Structure

```text
M4TH/DiscreteAbelChebyshev/
  README.md
  lakefile.toml
  DiscreteAbelChebyshev.lean
  DiscreteAbelChebyshev.svg
  DiscreteAbelChebyshev/
    Basic.lean
    ChebyshevBridge.lean
```

| File | Contents |
|---|---|
| `DiscreteAbelChebyshev/Basic.lean` | partial sums, finite Abel summation, `mangoldt`, `psi`, `invLog` |
| `DiscreteAbelChebyshev/ChebyshevBridge.lean` | exact bridge identities, reciprocal-log lemmas, conditional error transfer |

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
echo 'import DiscreteAbelChebyshev
#print axioms DiscreteAbelChebyshev.abel_summation
#print axioms DiscreteAbelChebyshev.pi_approx_final
#print axioms DiscreteAbelChebyshev.invLog_diff_bound
#print axioms DiscreteAbelChebyshev.chebyshev_implies_prime_error' \
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

- Compare `abel_summation` with `Finset.sum_Ioc_by_parts` and
  `Mathlib.NumberTheory.AbelSummation` before a Mathlib PR.
- Replace `ChebyshevErrorSumBound` by a proved theorem if the residual sum
  estimate is formalised.
- Keep the final transfer theorem conditional until the residual frontier is
  independently certified.

