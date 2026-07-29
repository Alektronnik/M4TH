# PrimeGapsSophie

**Sophie Germain primes and parity of higher-order prime gaps, formalised in
Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main Statements

The package defines Sophie Germain primes:

```lean
PrimeGapsSophie.IsSophieGermainPrime
```

and proves the elementary congruence API:

```lean
PrimeGapsSophie.sophie_germain_mod3_eq_2
PrimeGapsSophie.sophie_germain_mod6_eq_5
```

It also packages consecutive prime gaps using Mathlib's `Nat.nth Nat.Prime`:

```lean
PrimeGapsSophie.nthPrime
PrimeGapsSophie.primeGap
PrimeGapsSophie.primeGap_even
```

and proves parity for finite differences of any positive order over odd primes:

```lean
PrimeGapsSophie.nthOrderGap_even_of_odd_primes
```

## Structure

```text
PrimeGapsSophie/
  README.md
  lakefile.toml
  PrimeGapsSophie.lean
  PrimeGapsSophie.svg
  PrimeGapsSophie/
    SophieGermain.lean
    PrimeGap.lean
    HigherOrder.lean
```

| File | Contents |
|---|---|
| `PrimeGapsSophie/SophieGermain.lean` | Sophie Germain primes and congruences |
| `PrimeGapsSophie/PrimeGap.lean` | `nthPrime`, consecutive prime gaps, parity and lower bounds |
| `PrimeGapsSophie/HigherOrder.lean` | second, third, fourth, and N-th order finite-difference parity |

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
echo 'import PrimeGapsSophie
#print axioms PrimeGapsSophie.sophie_germain_mod6_eq_5
#print axioms PrimeGapsSophie.primeGap_even
#print axioms PrimeGapsSophie.secondOrderGap_even_of_odd_primes
#print axioms PrimeGapsSophie.nthOrderGap_even_of_odd_primes' \
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

- Deduplicate `sum_alternate_choose_eq_zero` against the strongest available
  alternating binomial lemma before proposing a Mathlib PR.
- Decide with reviewers whether `nthPrime` should remain as local notation or
  whether only lemmas about `Nat.nth Nat.Prime` should be contributed.
- Keep the original research framework based on affine prime-gap transforms
  outside this Mathlib-oriented package.

