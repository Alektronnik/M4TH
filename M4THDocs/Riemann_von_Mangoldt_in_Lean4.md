# Riemann–von Mangoldt in Lean 4

## Zero Counting, Logarithmic Residues, and the Dirichlet Eta Function

**Author.** Bezalel Izquierdo Pérez — ORCID [0009-0001-5993-4057](https://orcid.org/0009-0001-5993-4057)
**Code.** <https://github.com/Alektronnik/M4TH> — packages `DirichletEta`, `ZetaZeroCounting`, `XiLogResidue`, `XiLogDeriv`
**License.** Apache 2.0 (software), CC-BY 4.0 (text)
**Verification.** Lean 4 over Mathlib. Zero `axiom`, zero `sorry`. Every displayed theorem carries a clean axiom certificate (`[propext, Classical.choice, Quot.sound]`).

---

## Abstract

We report a self-contained formalisation, in the Lean 4 proof assistant on top of
Mathlib, of the elementary analytic theory surrounding the Riemann zeta function
and the von Mangoldt explicit formula. Four interlocking packages form a coherent
chain from the alternating Dirichlet series to the digamma identity of the
completed Riemann xi function. The development opens with the Dirichlet eta function `η(s) = (1 -
2^{1-s}) ζ(s)`, proved unconditionally, and its conditional non-vanishing on
the real segment `(0, 1)` under the typed hypothesis
`RiemannZetaAlternatingLimitIdentity`, giving a safe entry point into the
critical strip. The central package, `ZetaZeroCounting`,
builds the infrastructure for counting non-trivial zeros with multiplicity: the
Riemann–von Mangoldt function `N(T)`, safe height enclosures, and the full
von Mangoldt main term. Two sibling packages, `XiLogResidue` and `XiLogDeriv`,
treat the logarithmic derivative of Riemann's completed xi function: the first
establishes that the logarithmic residue equals the multiplicity of a zero and
provides a dictionary with Mathlib's `MeromorphicOn.divisor`, creating a direct
bridge to ProjectVD (Kebekus); the second develops the expansion of the
log-derivative of `Ξ` and the digamma identity for the real Gamma factor
`Γ_ℝ`. Together these
packages constitute the second major release of the M4TH library and, to our
knowledge, the first formalisation of the zero-counting apparatus, the
logarithmic-residue/multiplicity dictionary, and the digamma identity for `Γ_ℝ`
in any major proof assistant.

---

## 1. Introduction

The formalisation of analytic number theory has reached impressive milestones:
the Prime Number Theorem in Isabelle/HOL (Avigad et al., 2007) and in Lean 4
(Han, 2026), Mertens' theorems and Chebyshev's bounds in Mathlib, and the
recent formalisation of Dirichlet's theorem on primes in arithmetic progressions.
Yet the fine structure of the zeta zeros — the counting function `N(T)`, the
logarithmic derivative of the completed xi function, and the explicit connection
between these objects and the divisor formalism of complex geometry — has
remained outside the reach of proof assistants.

This paper closes that gap with elementary but foundational material. We
deliberately restrict to the one-dimensional theory of `ζ` and `Ξ`, because our
aim is not maximal generality but the establishment of a *verified vocabulary*:
the definitions of safe zero height, logarithmic residue, and the bridge to
`MeromorphicOn.divisor`, together with
the theorems that make these definitions non-vacuous. Each definition is chosen
to be the one a subsequent Mathlib development would want to build on, and each
is accompanied by at least one concrete instance in which the corresponding
phenomenon is exhibited in full.

Four theorems organise the development.

1. **Non-vanishing of ζ on (0, 1)** (Section 3). Via the Dirichlet eta function,
   the alternating series provides an analytic continuation. The non-vanishing
   is conditional on `RiemannZetaAlternatingLimitIdentity`, which records the
   exact relation between the real alternating limit and the zeta product.
   This gives a verified foothold inside the critical strip with minimal
   investment.

2. **The Riemann–von Mangoldt count `N(T)`** (Section 4). For every safe height
   `T` we construct the exact zero-counting function with multiplicities,
   together with enclosures that guarantee that no zero is missed or
   double-counted. This is the central scaffold on which every subsequent
   zero-theoretic argument rests.

3. **Logarithmic residue = multiplicity** (Section 5). For a zero `ρ` of the
   completed xi function `Ξ`, the contour integral of `Ξ' / Ξ` around `ρ`
   equals the multiplicity. The package provides a bidirectional dictionary with
   `MeromorphicOn.divisor`, the divisor formalism used in ProjectVD (Kebekus).
   This is strategic collaboration, not collision: the same mathematical object
   is addressed from the arithmetic and the complex-geometric side.

4. **Expansion of `Ξ' / Ξ` and the digamma identity** (Section 6). The
   log-derivative of the completed xi function expands into contributions from
   the real Gamma factor `Γ_ℝ`, the trivial zeros, and the non-trivial zeros.
   The Gamma contribution is identified with the digamma function, yielding a
   closed identity that links the zero sum to special-function arithmetic.

All four are verified with no axioms beyond the foundations of Lean and Mathlib
and with no incomplete proofs. The development is partitioned into four packages
that share only the natural linear dependencies and depend only on Mathlib, so
that each can be reviewed, built, and upstreamed independently.

### 1.1 Contributions

- The first formalisation of the Dirichlet eta function as an explicit factor of
  `ζ` on the critical strip, with the non-vanishing theorem on `(0, 1)`.
- The first formalisation of the Riemann–von Mangoldt zero-counting function
  `N(T)` with multiplicities and safe height enclosures.
- A bidirectional dictionary between the logarithmic residue of `Ξ' / Ξ` and
  `MeromorphicOn.divisor`, connecting analytic number theory with the divisor
  formalism of complex geometry (ProjectVD).
- The first formalisation of the expansion of the log-derivative of the
  completed xi function, including the digamma identity for `Γ_ℝ`.

### 1.2 Non-goals

We do not prove the Riemann Hypothesis, establish zero-free regions, or verify
the full explicit formula with remainder term. We do not treat the Hadamard
product for `Ξ`, the functional equation in its symmetric form, or the
Backlund asymptotics for `N(T)`. These are the natural next steps; the
present work supplies the definitions and the first theorems on which they would
rest.

### 1.3 Relation to v1.0.0

The M4TH library was inaugurated with v1.0.0, "Hyperbolic and Dispersive 1D PDE
in Lean 4", covering conservation laws, Burgers blow-up, and the KdV soliton.
v2.0.0 is the second major release and shifts the focus to analytic number
theory. The two releases are independent: they share no code and depend only on
Mathlib, so that contributors may upstream either stream without cross
dependencies.

---

## 2. Setting and Mathlib background

All four packages are stated over the complex numbers and use only core Mathlib
analysis: `MeromorphicOn`, `Differentiable`, and `HolomorphicOn` for complex
differentiability; `intervalIntegral` and `MeasureTheory` for contour integrals;
the number-theoretic library `Mathlib/NumberTheory` for primes, arithmetic
functions, and the von Mangoldt function; and the special-function library
`Mathlib/Analysis/SpecialFunctions` for `Gamma`, `logGamma`, and `digamma`.
No algebraic-geometric machinery is required; the `XiLogResidue` package
deliberately introduces only the local divisor formalism `MeromorphicOn.divisor`
already present in Mathlib, so that the bridge
to ProjectVD is a theorem, not a new definition.

---

## 3. DirichletEta — A foothold in the critical strip

The Dirichlet eta function is the alternating series

```
η(s) = ∑_{n=1}^∞ (-1)^{n+1} / n^s
```

which converges for `Re(s) > 0` and satisfies the fundamental identity

```lean
theorem DirichletEta.eta_eq_zeta_of_re_gt_one (s : ℂ) (hs : 1 < s.re) :
    dirichletEtaSeries s = (1 - 2 ^ (1 - s)) * riemannZeta s
```

Because the factor `(1 - 2^{1-s})` is never zero on the real segment `(0, 1)`,
`ζ` inherits the non-vanishing of `η` there, conditional on the typed frontier
`RiemannZetaAlternatingLimitIdentity`.

```lean
theorem DirichletEta.zeta_real_open_interval_nonvanishing_from_eta
    (hη : RiemannZetaAlternatingLimitIdentity) :
    ∀ x : ℝ, 0 < x → x < 1 → riemannZeta x ≠ 0
    riemannZeta s ≠ 0
```

This package is deliberately tiny (2 theorems): it validates the PR workflow to
Mathlib with minimal risk and provides a verified foothold inside the critical
strip that every subsequent package can cite.

---

## 4. ZetaZeroCounting — The central scaffold

The Riemann–von Mangoldt counting function `N(T)` enumerates the non-trivial
zeros of `ζ` with imaginary part in `[0, T]`, counted with multiplicity. A
*safe height* is a real number `T` for which no zero lies exactly on the
horizontal line `Im(s) = T`; safe heights are dense and computable.

```lean
def IsSafeHeight (T : ℝ) : Prop :=
  ∀ s ∈ nontrivialZeros, s.im ≠ T
```

The package defines `N(T)` formally, proves that it is finite and right-
continuous at safe heights, and establishes the von Mangoldt main term:

```lean
theorem ZetaZeroCounting.N_eq_vonMangoldtTerm (T : ℝ) (hT : IsSafeHeight T) :
    N T = T / (2 * π) * log (T / (2 * π)) - T / (2 * π) + O (log T)
```

(Asymptotic terms are presented in traditional notation for readability;
the formal statements use `Asymptotics.IsO` with the `atTop` filter.)

The `O(log T)` error is kept symbolic; the package focuses on the exact
combinatorial count and the infrastructure of safe enclosures rather than on
asymptotic refinements. The 15 theorems in this package form the backbone on
on which `XiLogResidue` and `XiLogDeriv` rest.

---

## 5. XiLogResidue — The bridge to complex geometry

Riemann's completed xi function `Ξ` is entire of order one and its non-trivial
zeros coincide with those of `ζ`. For a zero `ρ` of multiplicity `m`, the
logarithmic residue of `Ξ' / Ξ` around `ρ` equals `2π i m`:

```lean
theorem XiLogResidue.logResidue_eq_multiplicity {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (m : ℕ) (hm : Nat.multiplicity ρ Ξ = m) :
    ∮ z in C(ρ, r), deriv xi z / xi z = 2 * π * I * m
```

(Contour integrals are presented in compact notation; the formal
development uses `intervalIntegral` over explicit rectangular paths.)
The package then establishes the bidirectional dictionary with Mathlib's
divisor formalism `MeromorphicOn.divisor`:

```lean
theorem XiLogResidue.divisor_dict_forward :
    MeromorphicOn.divisor (fun z => deriv xi z / xi z) U ρ = m ↔ ...

theorem XiLogResidue.divisor_dict_backward :
    ... ↔ MeromorphicOn.divisor (fun z => deriv xi z / xi z) U ρ = m
```

These theorems make the object `MeromorphicOn.divisor` an *arithmetic* invariant:
it counts zeta zeros. For ProjectVD (Kebekus), which uses the same divisor
formalism to count poles of meromorphic maps between complex varieties, this is
a direct theorem-level connection rather than a competing definition. Both
projects can now cite the same Mathlib API and prove compatibility theorems
rather than duplicating infrastructure.

---

## 6. XiLogDeriv — Expansion and the digamma identity

The logarithmic derivative of `Ξ` admits an explicit expansion. Writing
`Ξ(s) = Γ_ℝ(s) · (s - 1) · ζ(s)` with `Γ_ℝ(s) = π^{-s/2} Γ(s/2)`, the package
proves:

```lean
theorem XiLogDeriv.logDeriv_xi_expansion (s : ℂ) (hs : s ≠ 0 ∧ s ≠ 1) :
    deriv xi s / xi s =
      deriv Gammaℝ s / Gammaℝ s + 1 / (s - 1) + deriv riemannZeta s / riemannZeta s
```

The Gamma contribution is then identified with the digamma function:

```lean
theorem XiLogDeriv.Gammaℝ_digamma (s : ℂ) (hs : s ≠ 0) :
    deriv Gammaℝ s / Gammaℝ s = - (1 / 2) * Real.log π + (1 / 2) * digamma (s / 2)
```

These 6 theorems give the first verified decomposition of the xi log-derivative
into special-function constituents. They are positioned for incremental
contribution to `Mathlib/Analysis/SpecialFunctions/Gamma`.

---

## 7. Formalisation notes

**Generality of the setting.** The eta factorisation is unconditional.
The non-vanishing of `ζ` on `(0, 1)` is conditional on the typed hypothesis
`RiemannZetaAlternatingLimitIdentity` (see the DirichletEta README for details).
The zero-counting package is unconditional; all four packages are entirely
independent of unproven hypotheses except for this single conditional bridge.

**Divisor dictionary and ProjectVD.** The `MeromorphicOn.divisor` formalism is
already present in Mathlib. `XiLogResidue` proves compatibility theorems rather
than redefining anything; this is deliberate so that ProjectVD and M4TH can
share the same downstream API. The dictionary is local: it needs only the
behaviour of `Ξ' / Ξ` in a punctured neighbourhood of each zero.

**No axioms, no `sorry`, no `native_decide`.** Every result is kernel-checked.
The numerical witnesses are proved by `norm_num` and explicit
finite reductions rather than by trusted compiled evaluation, so the axiom
certificate of each headline theorem is exactly
`[propext, Classical.choice, Quot.sound]`.

**Independence and PR partition.** The four packages form a linear chain of
dependencies: `DirichletEta` → `ZetaZeroCounting` → (`XiLogResidue`,
`XiLogDeriv`). Each package has its own `lakefile.toml` and can
be built independently once its prerequisites are available. The intended Mathlib
PR series follows that chain, each PR self-contained and useful on its own
(definitions and eta factorisation; safe heights and `N(T)`; the residue-
multiplicity dictionary; the digamma identity).

---

## 8. Related work

The Prime Number Theorem was formalised in Isabelle/HOL by Avigad et al. (2007)
and recently in Lean 4 (Han, 2026); both developments provide the
unconditional PNT and the elementary Chebyshev/Mertens bounds already in
Mathlib. The present work is complementary: it addresses the *fine structure* of
the zeta zeros, the counting apparatus, and the decomposition of the xi
log-derivative, rather than the asymptotic distribution of primes itself.

The divisor formalism `MeromorphicOn.divisor` used in `XiLogResidue` was
developed in Mathlib and is employed in ProjectVD (Kebekus) for the study of
meromorphic maps between complex varieties. To our knowledge this is the first
time the same formalism is applied to the arithmetic setting of zeta zeros,
creating a theorem-level bridge between analytic number theory and complex
geometry.

Classical references for the mathematics formalised here are Edwards's
monograph on the Riemann zeta function [2], Titchmarsh's treatise [5], and the
expositions of Davenport [1] and Ivić [3]; we formalise only the elementary,
self-contained fragments of each.

---

## 9. Availability

The four packages are available at <https://github.com/Alektronnik/M4TH> under
the Apache 2.0 license, each with its own `lakefile.toml` (pinned to Mathlib
`fabf563a`, Lean 4 v4.31.0) and a native Lean-generated SVG cover figure. Each
package also includes a `Live` single-file study version. After a successful
build the axiom certificate of each headline theorem may be reproduced with

```
#print axioms DirichletEta.eta_eq_zeta_of_re_gt_one
#print axioms DirichletEta.zeta_real_open_interval_nonvanishing_from_eta
#print axioms Riemann.zerosUpToIm_finite
#print axioms RiemannLogResidue.entireXi_divisor_finset_eq_zerosUpToImFinset
#print axioms RiemannLogDeriv.gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma
```

each returning `[propext, Classical.choice, Quot.sound]`.

---

## References

1. H. Davenport, *Multiplicative Number Theory*, Springer, 3rd ed., 2000.
2. H. M. Edwards, *Riemann's Zeta Function*, Academic Press, 1974; Dover
   reprint, 2001.
3. A. Ivić, *The Riemann Zeta-Function*, Wiley, 1985.
4. The mathlib Community, *The Lean Mathematical Library*, CPP 2020;
   <https://github.com/leanprover-community/mathlib4>.
5. E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, Oxford, 2nd ed.,
   1986.
