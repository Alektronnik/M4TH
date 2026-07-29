# DirichletEta

**Dirichlet eta, the zeta-product identity in the half-plane `Re s > 1`, and
a typed frontier for the non-vanishing of `ζ` on the real interval `(0, 1)`.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0

## Main Statements

The package defines the alternating eta term and series:

```lean
DirichletEta.etaTerm
DirichletEta.dirichletEtaSeries
DirichletEta.dirichletEta
```

and proves the product identity in the classical domain of absolute
convergence:

```lean
DirichletEta.eta_eq_zeta_of_re_gt_one
```

It also proves positivity of the real alternating eta limit:

```lean
DirichletEta.alternating_zeta_real_pos
```

The continuation step needed to transport this positivity to `ζ(x)` on
`0 < x < 1` is not represented by a trusted declaration.  It is exposed as the
typed hypothesis:

```lean
DirichletEta.RiemannZetaAlternatingLimitIdentity
```

and the package proves:

```lean
DirichletEta.zeta_real_open_interval_nonvanishing_from_eta
```

## Structure

```text
M4TH/DirichletEta/
  README.md
  lakefile.toml
  DirichletEta.lean
  DirichletEta.svg
  DirichletEta/
    Basic.lean
    Analytic.lean
    Nonvanishing.lean
```

| File | Contents |
|---|---|
| `DirichletEta/Basic.lean` | eta terms, eta series, summability, even/odd splitting, product identity in `Re s > 1` |
| `DirichletEta/Analytic.lean` | differentiability of eta terms and analyticity of the zeta-product eta normalisation |
| `DirichletEta/Nonvanishing.lean` | real positivity and conditional non-vanishing of `ζ` on `(0, 1)` |

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
echo 'import DirichletEta
#print axioms DirichletEta.eta_eq_zeta_of_re_gt_one
#print axioms DirichletEta.analyticOn_dirichletEta
#print axioms DirichletEta.alternating_zeta_real_pos
#print axioms DirichletEta.zeta_real_open_interval_nonvanishing_from_eta' \
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

- Replace `RiemannZetaAlternatingLimitIdentity` by a direct theorem once the
  identity theorem proof is completed over the right half-plane.
- Compare naming and scope with existing zeta and Dirichlet-series APIs before
  proposing a Mathlib PR.
- Keep the real non-vanishing theorem conditional until the continuation bridge
  is formalised without additional hypotheses.

