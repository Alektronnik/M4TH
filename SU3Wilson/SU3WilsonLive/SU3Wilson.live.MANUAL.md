# SU3Wilson.live

**A single-file live presentation of concrete \(SU(3)\), normalized trace
bounds, and Wilson plaquette positivity, formalised in Lean 4 over Mathlib.**

**Author:** Bezalel Izquierdo Pérez
**License:** Apache 2.0
**Live file:** `SU3Wilson.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`SU3Wilson.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

Wilson lattice gauge theory attaches group-valued link variables to the edges
of a lattice and builds plaquette products around elementary squares.  For
gauge group \(SU(3)\), the local Wilson plaquette contribution has the form

$$
1 - \frac{\operatorname{Re}\operatorname{Tr}(P)}{3}.
$$

The package certifies the elementary positivity layer needed for this
construction:

$$
0 \leq 1 - \frac{\operatorname{Re}\operatorname{Tr}(P)}{3} \leq 2.
$$

It then lifts the local bound to finite lattice sums and to a constructive
four-dimensional lattice with explicit link variables.

The oriented plaquette is represented by the standard loop:

```text
       U_mu(x+nu)^-1
    o <------------- o
    |               ^
    |               |
    v               |
    o ------------> o
          U_mu(x)
```

The corresponding product is

$$
P_{\mu\nu}(x)
= U_\mu(x)\,U_\nu(x+\hat\mu)\,
  U_\mu(x+\hat\nu)^{-1}\,U_\nu(x)^{-1}.
$$

---

## II. Concrete \(SU(3)\)

> **Definition 1. Complex \(3 \times 3\) matrices.**
>
> **In Lean:**
>
> ```lean
> abbrev Physics.YangMills.WilsonMatrix3x3 :=
>   Matrix (Fin 3) (Fin 3) ℂ
> ```

> **Definition 2. The concrete group \(SU(3)\).**
>
> An element is a \(3 \times 3\) complex matrix satisfying the special-unitary
> equations:
>
> $$
> UU^\ast = 1,\qquad \det(U)=1.
> $$
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.SU3 :=
>   { M : WilsonMatrix3x3 // M * M.conjTranspose = 1 ∧ M.det = 1 }
> ```

> **Theorem 1. The unitary condition.**
>
> **In Lean:**
>
> ```lean
> lemma Physics.YangMills.SU3.unitary_condition
>     (U : SU3) :
>     U.val * U.val.conjTranspose = 1
> ```

> **Theorem 2. The determinant condition.**
>
> **In Lean:**
>
> ```lean
> lemma Physics.YangMills.SU3.det_condition
>     (U : SU3) :
>     U.val.det = 1
> ```

> **Theorem 3. The reverse unitary identity.**
>
> For square matrices over a field, the condition \(UU^\ast=1\) yields
> \(U^\ast U=1\).
>
> **In Lean:**
>
> ```lean
> lemma Physics.YangMills.SU3.conjTranspose_mul_self
>     (U : SU3) :
>     U.val.conjTranspose * U.val = 1
> ```

> **Theorem 4. Closure under multiplication.**
>
> **In Lean:**
>
> ```lean
> lemma Physics.YangMills.SU3.mul_mem
>     (U V : SU3) :
>     U.1 * V.1 * (U.1 * V.1).conjTranspose = 1 ∧
>       (U.1 * V.1).det = 1
> ```

> **Theorem 5. Closure under inverse.**
>
> **In Lean:**
>
> ```lean
> lemma Physics.YangMills.SU3.inv_mem
>     (U : SU3) :
>     U.val.conjTranspose * U.val.conjTranspose.conjTranspose = 1 ∧
>       U.val.conjTranspose.det = 1
> ```

The live file then equips `SU3` with its group structure.

> **Definition 3. The matrix trace on \(SU(3)\).**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.matrixTraceSU3
>     (A : SU3) : ℂ :=
>   A.val.trace
> ```

> **Definition 4. The identity element.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.oneSU3 : SU3 := 1
> ```

> **Theorem 6. Trace of the identity.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.matrixTraceSU3_one :
>     matrixTraceSU3 oneSU3 = (3 : ℂ)
> ```

> **Theorem 7. Normalized real trace bound.**
>
> The central estimate is:
>
> $$
> -1 \leq \frac{\operatorname{Re}\operatorname{Tr}(U)}{3}
> \leq 1.
> $$
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.su3_trace_re_bound
>     (U : SU3) :
>     -1 <= (matrixTraceSU3 U).re / 3 ∧
>       (matrixTraceSU3 U).re / 3 <= 1
> ```

---

## III. Finite Wilson Plaquette Layer

> **Definition 5. A finite lattice.**
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.Lattice (V : Nat) : Type :=
>   Fin V
> ```

> **Definition 6. Direction labels.**
>
> **In Lean:**
>
> ```lean
> abbrev Physics.YangMills.Direction := Nat
> ```

> **Definition 7. A finite lattice gauge field.**
>
> The structure contains explicit links, explicit plaquettes, and the diagonal
> plaquette law.
>
> **In Lean:**
>
> ```lean
> structure Physics.YangMills.LatticeGaugeField (V : Nat) where
>   link : Lattice V → Direction → SU3
>   plaquette : Lattice V → Direction → Direction → SU3
>   plaquette_diagonal : ∀ x μ, plaquette x μ μ = oneSU3
> ```

> **Definition 8. The normalized finite lattice sum.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.latticeSum
>     {V : Nat} (_field : LatticeGaugeField V)
>     (f : Fin V → Direction → Direction → ℝ) : ℝ
> ```

> **Theorem 8. Nonnegativity of the lattice sum.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.latticeSum_nonneg
>     {V : Nat} (field : LatticeGaugeField V)
>     (f : Fin V → Direction → Direction → ℝ)
>     (hf : ∀ x μ ν, 0 ≤ f x μ ν) :
>     0 ≤ latticeSum field f
> ```

> **Definition 9. The Wilson plaquette term.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.wilsonTerm
>     {V : Nat} (field : LatticeGaugeField V)
>     (x : Fin V) (μ ν : Direction) : ℝ :=
>   1 - (matrixTraceSU3 (field.plaquette x μ ν)).re / 3
> ```

> **Theorem 9. Wilson terms are nonnegative.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.wilsonTerm_nonneg
>     {V : Nat} (field : LatticeGaugeField V)
>     (x : Fin V) (μ ν : Direction) :
>     0 ≤ wilsonTerm field x μ ν
> ```

> **Theorem 10. Wilson terms are bounded above by \(2\).**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.wilsonTerm_le_two
>     {V : Nat} (field : LatticeGaugeField V)
>     (x : Fin V) (μ ν : Direction) :
>     wilsonTerm field x μ ν ≤ 2
> ```

> **Definition 10. The finite Wilson action.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.WilsonAction
>     {V : Nat} (β : ℝ) (field : LatticeGaugeField V) : ℝ :=
>   β * latticeSum field (wilsonTerm field)
> ```

> **Theorem 11. The finite Wilson action is nonnegative.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.WilsonAction_nonneg
>     {V : Nat} (β : ℝ) (field : LatticeGaugeField V)
>     (hβ : 0 ≤ β) :
>     0 ≤ WilsonAction β field
> ```

---

## IV. Constructive Four-Dimensional Lattice

> **Definition 11. A finite Euclidean four-dimensional lattice.**
>
> **In Lean:**
>
> ```lean
> abbrev Physics.YangMills.Lattice4D
>     (Lt Lx Ly Lz : ℕ) :=
>   Fin Lt × Fin Lx × Fin Ly × Fin Lz
> ```

> **Definition 12. The four coordinate directions.**
>
> **In Lean:**
>
> ```lean
> abbrev Physics.YangMills.Dir4 := Fin 4
> def Physics.YangMills.dirT : Dir4 := 0
> def Physics.YangMills.dirX : Dir4 := 1
> def Physics.YangMills.dirY : Dir4 := 2
> def Physics.YangMills.dirZ : Dir4 := 3
> ```

> **Definition 13. Periodic successor.**
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.wrapSucc {n : ℕ}
>     (i : Fin n) : Fin n
> ```

> **Definition 14. Time reflection.**
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.timeReflection4D
>     {Lt Lx Ly Lz : ℕ}
>     (site : Lattice4D Lt Lx Ly Lz) :
>     Lattice4D Lt Lx Ly Lz
> ```

> **Definition 15. Shift in a coordinate direction.**
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.shift4D
>     {Lt Lx Ly Lz : ℕ}
>     (site : Lattice4D Lt Lx Ly Lz)
>     (μ : Dir4) : Lattice4D Lt Lx Ly Lz
> ```

> **Definition 16. Link variables.**
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.LinkVars4D
>     (Lt Lx Ly Lz : ℕ) : Type :=
>   Lattice4D Lt Lx Ly Lz → Dir4 → SU3
> ```

> **Definition 17. The constructive plaquette.**
>
> The plaquette is the ordered product
>
> $$
> U_\mu(x)\,U_\nu(x+\hat\mu)\,
> U_\mu(x+\hat\nu)^{-1}\,U_\nu(x)^{-1}.
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.plaquette4D
>     (U : LinkVars4D Lt Lx Ly Lz)
>     (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) : SU3
> ```

> **Theorem 12. Diagonal plaquettes are the identity.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.plaquette4D_diagonal
>     (U : LinkVars4D Lt Lx Ly Lz)
>     (site : Lattice4D Lt Lx Ly Lz) (μ : Dir4) :
>     plaquette4D U site μ μ = oneSU3
> ```

> **Theorem 13. Trace symmetry under reversing directions.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.plaquette4D_trace_re_symm
>     (U : LinkVars4D Lt Lx Ly Lz)
>     (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) :
>     (matrixTraceSU3 (plaquette4D U site μ ν)).re =
>       (matrixTraceSU3 (plaquette4D U site ν μ)).re
> ```

> **Definition 18. Four-dimensional lattice sum.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.latticeSum4D
>     (f : Lattice4D Lt Lx Ly Lz → Dir4 → Dir4 → ℝ) : ℝ
> ```

> **Definition 19. Four-dimensional Wilson term.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.wilsonTerm4D
>     (U : LinkVars4D Lt Lx Ly Lz)
>     (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) : ℝ :=
>   1 - (matrixTraceSU3 (plaquette4D U site μ ν)).re / 3
> ```

> **Theorem 14. Four-dimensional Wilson terms are nonnegative.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.wilsonTerm4D_nonneg
>     (U : LinkVars4D Lt Lx Ly Lz)
>     (site : Lattice4D Lt Lx Ly Lz) (μ ν : Dir4) :
>     0 ≤ wilsonTerm4D U site μ ν
> ```

> **Definition 20. Four-dimensional Wilson action.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.WilsonAction4D
>     (β : ℝ) (U : LinkVars4D Lt Lx Ly Lz) : ℝ :=
>   β * latticeSum4D (wilsonTerm4D U)
> ```

> **Theorem 15. Four-dimensional Wilson action is nonnegative.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.WilsonAction4D_nonneg
>     (β : ℝ) (U : LinkVars4D Lt Lx Ly Lz)
>     (hβ : 0 ≤ β) :
>     0 ≤ WilsonAction4D β U
> ```

> **Definition 21. Time reflection on link variables.**
>
> Temporal links are inverted after reflecting the site; spatial links are
> transported without inversion.
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.timeReflection4D_on_links
>     (U : LinkVars4D Lt Lx Ly Lz) :
>     LinkVars4D Lt Lx Ly Lz
> ```

---

## V. Architecture

The live file is fused in dependency order:

```text
SU3
  -> Wilson
    -> Lattice4D
```

The package separates three layers:

- concrete \(SU(3)\) matrix algebra;
- finite Wilson plaquette positivity;
- constructive four-dimensional lattice plaquettes.

The trace bound is the bridge from group theory to lattice positivity:

```text
U ∈ SU(3)
  -> -1 <= Re Tr(U) / 3 <= 1
  -> 0 <= 1 - Re Tr(P) / 3 <= 2
  -> WilsonAction >= 0 when beta >= 0
```

---

## VI. Axiom Certificate

The representative certificate command is:

```text
echo 'import SU3Wilson
#print axioms Physics.YangMills.su3_trace_re_bound
#print axioms Physics.YangMills.wilsonTerm_nonneg
#print axioms Physics.YangMills.WilsonAction_nonneg
#print axioms Physics.YangMills.plaquette4D_diagonal
#print axioms Physics.YangMills.WilsonAction4D_nonneg' \
  | lake env lean --stdin
```

The current certificate is:

```text
'Physics.YangMills.su3_trace_re_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Physics.YangMills.wilsonTerm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Physics.YangMills.WilsonAction_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Physics.YangMills.plaquette4D_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Physics.YangMills.WilsonAction4D_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There are no package-local axioms in these certificates.

---

## VII. Reading Guide

For a first pass, read the file in this order:

1. `SU3`, `matrixTraceSU3`, and `su3_trace_re_bound`.
2. `LatticeGaugeField`, `wilsonTerm`, and `WilsonAction`.
3. `Lattice4D`, `LinkVars4D`, and `plaquette4D`.
4. `plaquette4D_diagonal`, `wilsonTerm4D_nonneg`, and
   `WilsonAction4D_nonneg`.

The shortest mathematical spine of the package is:

```text
SU(3) = { U : Mat_3(C) | U U* = 1 and det U = 1 }
|Re Tr(U)| <= 3
0 <= 1 - Re Tr(P)/3 <= 2
WilsonAction(beta, U) = beta * sum plaquette terms
beta >= 0 -> WilsonAction(beta, U) >= 0
```

---

## VIII. Verification

The live file was checked with:

```text
lake env lean M4TH/SU3Wilson/SU3WilsonLive/SU3Wilson.live.lean
```

The package build command is:

```text
lake build SU3Wilson
```

Both checks are intended to be rerun before publication or Zulip discussion.
