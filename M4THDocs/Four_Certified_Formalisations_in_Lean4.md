# Four Certified Formalisations in Lean 4

## Concrete su(3), the SU(3) Wilson Action, the Elliptic Curve 5077a1, and Prime-Gap Parity

**Author.** Bezalel Izquierdo Pérez — ORCID [0009-0001-5993-4057](https://orcid.org/0009-0001-5993-4057)
**Code.** <https://github.com/Alektronnik/M4TH> — packages `SU3Concrete`, `SU3Wilson`, `CertifiedElliptic5077`, `PrimeGapsSophie`
**License.** Apache 2.0 (software), CC-BY 4.0 (text)
**Verification.** Lean 4 over Mathlib. Zero `axiom`, zero `sorry`, zero `native_decide`. Every displayed theorem carries a clean axiom certificate (`[propext, Classical.choice, Quot.sound]`).

---

## Abstract

This release collects four independent, self-contained formalisations in the Lean 4 proof
assistant on top of Mathlib. Unlike the previous four M4TH releases, each of which pursued a
single mathematical arc, this one is deliberately heterogeneous: its four packages span gauge
theory, lattice field theory, arithmetic geometry, and elementary number theory, and are
bound together not by a common subject but by a common standard — each is proved without any
package-local `axiom`, without `sorry`, and without `native_decide`, so every headline
theorem carries the clean foundational certificate. The packages are presented in decreasing
order of scope and importance. `SU3Concrete` builds the compact real Lie algebra `su(3)`
concretely from the Gell-Mann matrices and proves the explicit structure-constant, Jacobi,
Killing-form and Casimir identities that the physics literature quotes but that no proof
assistant had certified in concrete form. `SU3Wilson` constructs `SU(3)` as concrete
matrices, proves the normalised trace bound, and derives the nonnegativity of the Wilson
plaquette action on a four-dimensional lattice. `CertifiedElliptic5077` provides a certified
computational kit for the Cremona/LMFDB elliptic curve 5077a1 — its integral and short
Weierstrass models, discriminant, finite-field point counts, and explicit rational points
with checked doublings. `PrimeGapsSophie` formalises Sophie Germain primes and the parity of
finite differences of arbitrary order over the primes.

---

## 1. Introduction

The first four M4TH releases were monographs: each took one theorem or one arc — scalar
conservation laws, the Riemann–von Mangoldt zero count, Mertens' theorems, the argument
principle over the critical box — and pursued it to a clean certificate. The present release
is, by contrast, a **miscellany**: four packages that matured independently and are published
together because each has reached the M4TH bar of verification, not because they share a
theme. We are explicit about this. The unifying thread is the standard — zero `axiom`, zero
`sorry`, zero `native_decide`, clean certificate — and the packages are ordered below by
scope and importance rather than by any logical dependency, of which there is none: all four
depend only on Mathlib and share no code.

Two of the four (`SU3Concrete`, `SU3Wilson`) are physics infrastructure aimed at Physlib and
at the constructive Yang-Mills programme; one (`CertifiedElliptic5077`) is a certified
arithmetic-geometry instance in the tradition of formalised concrete computations; and one
(`PrimeGapsSophie`) is elementary number theory extracted from a discrete calculus of prime
gaps. What they have in common is that each is a finished, kernel-checked artefact.

### 1.1 Contributions

- **Concrete `su(3)`** from the Gell-Mann generators `Tᵃ = iλₐ`: explicit structure constants
  `f^{abc}` with antisymmetry, cyclicity and the **Jacobi identity** proved by finite
  summation; the adjoint Casimir `= (-3)·I₈`; the Killing form `κ(Tᵃ,Tᵇ) = -3 δᵃᵇ`; and the
  fundamental Casimir `∑ₐ TᵃTᵃ = -(16/3)·I₃`. To our knowledge the first proof-assistant
  certification of these identities from a concrete Gell-Mann realisation.
- **SU(3) Wilson positivity**: the normalised-trace bound `-1 ≤ Re(tr U)/3 ≤ 1` for every
  `U ∈ SU(3)`, hence every Wilson plaquette term lies in `[0,2]`, hence the Wilson action is
  nonnegative for nonnegative coupling, on a constructive four-dimensional lattice.
- **Certified 5077a1**: the discriminant `= 5077`, the exact integral-to-short change of
  coordinates, finite-field point counts at `p = 2,3,5`, and explicit rational points with
  kernel-checked doublings, for the smallest-conductor rank-3 elliptic curve.
- **Prime-gap parity**: Sophie Germain primes with the congruences `p ≡ 2 (mod 3)` and
  `p ≡ 5 (mod 6)`, the evenness of ordinary prime gaps, and the **parity of finite
  differences of arbitrary order** over the odd primes.

### 1.2 Non-goals

`SU3Concrete` and `SU3Wilson` build the algebraic and lattice infrastructure of Yang-Mills;
they do not address the mass gap, reflection positivity of the full measure, or the
continuum limit. `CertifiedElliptic5077` certifies concrete data for one curve; it does not
prove its rank, the Birch–Swinnerton-Dyer conjecture, or Mordell–Weil in general.
`PrimeGapsSophie` proves parity and congruence facts; it does not address the infinitude of
Sophie Germain or twin primes. Each package is a certified foundation, not a resolution.

### 1.3 Relation to earlier releases

This is the fifth major release of M4TH, after v1.0.0 (hyperbolic and dispersive PDE),
v2.0.0 (Riemann–von Mangoldt zero counting), v3.0.0 (Mertens' theorems and compensated
Euler-product convergence), and v4.0.0 (the argument principle over the critical box). It is
the first release that is a collection rather than a single arc; as with all earlier
releases, every package depends only on Mathlib, carries its own `lakefile.toml`, and can be
reviewed, built, and upstreamed independently.

---

## 2. Setting and Mathlib background

The four packages use disjoint parts of Mathlib. The two gauge-theory packages work with
`Matrix (Fin 3) (Fin 3) ℂ`, the `LieRing`/`LieAlgebra ℝ` classes, and the special-unitary
equations; both place their public declarations in the `Physics.YangMills` namespace and are,
by design, separate packages whose small overlap is resolved at Physlib-PR time exactly as
with the `ConservationLaws`/`BurgersBlowUp` pair. `CertifiedElliptic5077` uses `ℚ`-arithmetic,
finite fields `ZMod p`, and `Mathlib`'s Weierstrass and `decide`-based finite verification,
under the `CertifiedEC` namespace. `PrimeGapsSophie` uses `Nat.Prime`, `Nat.nth Nat.Prime`,
and modular arithmetic, under the `PrimeGapsSophie` namespace. No package imports any other.

---

## 3. SU3Concrete — the compact Lie algebra su(3) from Gell-Mann matrices

The package realises `su(3)` concretely as the anti-Hermitian trace-zero `3 × 3` complex
matrices, with the physics convention `Tᵃ = iλₐ` for the eight Gell-Mann matrices `λₐ`. It
proves the generator identities on which the whole gauge-theoretic edifice rests: each
generator is anti-Hermitian (`gellMannGenerator_antiHermitian`), the commutator is the
explicit matrix (`generator_commutator_matrix`), and the structure constants satisfy the
Jacobi identity as a finite sum over the eight-dimensional index:

```lean
theorem Physics.YangMills.structureConstant_jacobi (a b c d : Fin 8) :
    (∑ e : Fin 8, (structureConstant a b e * structureConstant c d e + …)) = 0
```

From the adjoint action it computes the adjoint Casimir and the Killing form in closed form,

```lean
theorem Physics.YangMills.adjointCasimir_diagonal :
    adjointCasimir = (-3) • (1 : Matrix (Fin 8) (Fin 8) ℝ)

theorem Physics.YangMills.killingFormBasis_diagonal (a b : Fin 8) :
    killingFormBasis a b = -3 * (if a = b then (1 : ℝ) else 0)
```

and in the fundamental representation it certifies the quadratic Casimir

```lean
theorem Physics.YangMills.fundamentalCasimir_diagonal :
    fundamentalCasimir = (-(16/3 : ℂ)) • (1 : Matrix3x3)
```

together with the trace normalisation and the Cartan pair. These are the numbers physicists
write down — `κ = -3δ`, `C₂(fund) = 16/3` in this normalisation — now proved from a concrete
Gell-Mann realisation rather than assumed. This is the largest package of the release
(forty-five theorems) and the one with the clearest destination: the concrete Gell-Mann and
structure-constant API is exactly the material a physics library needs and does not yet have
in concrete form.

---

## 4. SU3Wilson — the trace bound and Wilson-action positivity

The companion package constructs `SU(3)` as concrete `3 × 3` complex matrices satisfying the
special-unitary equations, equips it with its group instance, and proves the single analytic
fact that governs lattice gauge positivity — the normalised real-trace bound:

```lean
theorem Physics.YangMills.su3_trace_re_bound (U : SU3) :
    -1 ≤ (matrixTraceSU3 U).re / 3 ∧ (matrixTraceSU3 U).re / 3 ≤ 1
```

From this, each Wilson plaquette term is confined to `[0, 2]`
(`wilsonTerm_nonneg`, `wilsonTerm_le_two`), and therefore the Wilson action is nonnegative
for nonnegative coupling, both in the abstract finite-lattice formulation and in the
constructive four-dimensional lattice built from link variables:

```lean
theorem Physics.YangMills.WilsonAction_nonneg …
theorem Physics.YangMills.WilsonAction4D_nonneg (β : ℝ) (U : LinkVars4D Lt Lx Ly Lz)
    (hβ : 0 ≤ β) : 0 ≤ WilsonAction4D β U
```

The 4D layer constructs sites, directions, links and plaquettes explicitly and proves the
plaquette symmetries (`plaquette4D_diagonal`, `plaquette4D_trace_re_symm`). Positivity of the
Wilson action is the entry point to constructive lattice gauge theory; here it is a theorem,
derived from the trace bound, with no analytic assumption.

---

## 5. CertifiedElliptic5077 — a certified kit for the curve 5077a1

The elliptic curve 5077a1, `y² + y = x³ − 7x + 6`, is the smallest-conductor curve of
Mordell–Weil rank three, a standard test case in arithmetic geometry. The package isolates a
reusable computational layer for short Weierstrass curves over `ℚ` and then certifies the
concrete curve and its short model `Y² = x³ − 7x + 25/4` via the exact change of coordinates
`Y = y + 1/2`. It proves the discriminant,

```lean
theorem CertifiedEC.shortDiscriminant_E5077 : shortDiscriminant E5077 = 5077
```

the finite-field point counts at the first primes (each closed by kernel `decide`, e.g.
`N_five : N_p 5 = 10`), the Nagell–Lutz candidate reduction for integral points, and explicit
rational points with checked doublings:

```lean
theorem CertifiedEC.P1_add_self :
    ECPoint.affine P1_5077 + ECPoint.affine P1_5077 = ECPoint.affine twiceP1_5077
```

This is a certified-instance contribution in the tradition of formalised concrete
computations (the Mordell curves of CPP 2023, Ramanujan–Nagell): it does not prove the rank
or BSD, but every displayed datum — discriminant, counts, doublings, coordinate equivalence —
is kernel-checked rather than quoted from a table.

---

## 6. PrimeGapsSophie — Sophie Germain primes and higher-order gap parity

The smallest package formalises two elementary strands. First, Sophie Germain primes,

```lean
def PrimeGapsSophie.IsSophieGermainPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (2 * p + 1)
```

with the congruences they must satisfy: `p ≡ 2 (mod 3)` and, for `p ≥ 5`, `p ≡ 5 (mod 6)`
(`sophie_germain_mod3_eq_2`, `sophie_germain_mod6_eq_5`). Second, the parity theory of prime
gaps built on Mathlib's `Nat.nth Nat.Prime`: ordinary gaps between odd primes are even
(`primeGap_even`), and this extends to finite differences of arbitrary order:

```lean
theorem PrimeGapsSophie.nthOrderGap_even_of_odd_primes
    (N : ℕ) (hN : N > 0) (p : ℕ → ℕ) (h_prime : ∀ i, i ≤ N → Nat.Prime (p i)) … : …
```

The material is elementary and its natural home is a dedicated sequence library rather than
Mathlib core, but the parity of arbitrary-order finite differences over the primes is a clean
general statement that the ad hoc treatments in the recreational literature do not isolate.

---

## 7. Formalisation notes

**A release defined by its standard, not its subject.** The four packages have no common
theme; what they share is the verification bar. Each is proved with zero package-local
`axiom`, zero `sorry`, and — unlike some concrete-computation formalisations — zero
`native_decide`: the finite verifications in `CertifiedElliptic5077` use kernel `decide` and
`norm_num`, so the axiom certificate of every headline theorem is exactly
`[propext, Classical.choice, Quot.sound]`.

**Concrete versus abstract.** `SU3Concrete` and `SU3Wilson` deliberately work with explicit
`3 × 3` matrices rather than an abstract `SpecialUnitaryGroup`, because the physics content is
in the concrete Gell-Mann numbers and the explicit trace bound; if Mathlib or Physlib already
provides a suitable abstract group, the PR versions rewrite on top of it and keep the concrete
identities and the positivity layer as the contribution.

**Independence.** No package imports another. The two gauge packages share the
`Physics.YangMills` namespace and a little overlapping matrix vocabulary, resolved at PR time
by a single shared contribution.

---

## 8. Related work

The abstract theory of semisimple Lie algebras, root systems and Casimirs is in Mathlib; what
is new here is the **concrete** Gell-Mann realisation of `su(3)` with certified structure
constants, which the physics literature uses constantly and which Physlib (the merged
PhysLean/Lean-QuantumInfo library) had flagged as missing in concrete form. Lattice gauge
theory and the Wilson action have no prior formalisation known to us. For elliptic curves,
Mathlib provides `WeierstrassCurve` and the proved group law (Angdinata–Xu), and there is a
tradition of certified concrete computation (Best et al., Mordell curves, CPP 2023);
`CertifiedElliptic5077` is a certified instance in that tradition for a distinguished curve.
Sophie Germain primes and higher-order prime-gap parity are not in Mathlib; the governing
precedent is that Mathlib routes specific-sequence results to a dedicated library, which is
this package's likely destination.

---

## 9. Availability

The four packages are available at <https://github.com/Alektronnik/M4TH> under the Apache 2.0
license, each with its own `lakefile.toml` (pinned to Mathlib `fabf563a`, Lean 4 v4.31.0), a
native Lean-generated SVG cover figure, and a `Live` single-file study version. After a
successful build the axiom certificate of each headline theorem may be reproduced with

```
#print axioms Physics.YangMills.structureConstant_jacobi
#print axioms Physics.YangMills.fundamentalCasimir_diagonal
#print axioms Physics.YangMills.su3_trace_re_bound
#print axioms Physics.YangMills.WilsonAction4D_nonneg
#print axioms CertifiedEC.shortDiscriminant_E5077
#print axioms CertifiedEC.P1_add_self
#print axioms PrimeGapsSophie.sophie_germain_mod6_eq_5
#print axioms PrimeGapsSophie.nthOrderGap_even_of_odd_primes
```

each returning `[propext, Classical.choice, Quot.sound]`.

---

## References

1. J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, Cambridge, 3rd ed., 2020.
2. H. Georgi, *Lie Algebras in Particle Physics*, Westview, 2nd ed., 1999.
3. I. Montvay and G. Münster, *Quantum Fields on a Lattice*, Cambridge, 1994.
4. J. E. Cremona, *Algorithms for Modular Elliptic Curves*, Cambridge, 2nd ed., 1997; and the
   LMFDB, <https://www.lmfdb.org>.
5. J. H. Silverman, *The Arithmetic of Elliptic Curves*, Springer, 2nd ed., 2009.
6. The mathlib Community, *The Lean Mathematical Library*, CPP 2020;
   <https://github.com/leanprover-community/mathlib4>.
