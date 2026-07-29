# SU3Concrete.live

**A single-file live presentation of concrete \( \mathfrak{su}(3) \) from
Gell-Mann matrices, formalised in Lean 4 over Mathlib.**

**Author:** Bezalel Izquierdo Pérez
**License:** Apache 2.0
**Live file:** `SU3Concrete.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`SU3Concrete.live.lean`.  It presents the mathematical content in the same order
as the live Lean file.  Proof scripts are intentionally omitted here; the live
Lean file is the certificate.

---

## I. The Mathematical Problem

The Lie algebra \( \mathfrak{su}(3) \) is the compact real Lie algebra of
trace-zero anti-Hermitian \(3 \times 3\) complex matrices.

This package builds it concretely from the Gell-Mann matrices.  The convention
used throughout is the anti-Hermitian physics convention:

$$
T^a = i\lambda_a.
$$

With this normalization, the commutator has the form

$$
[T^a,T^b] = -2 f^{abc} T^c.
$$

The package certifies:

- the eight Gell-Mann generators;
- membership of the generators in \( \mathfrak{su}(3) \);
- the matrix commutator Lie algebra;
- explicit structure constants \(f^{abc}\);
- the finite Jacobi certificate for the structure constants;
- the Gell-Mann commutator table;
- the adjoint representation;
- the Killing form on the basis;
- the Cartan pair;
- the fundamental quadratic Casimir.

The geometric picture is the \(A_2\) root system in the Cartan plane:

```text
                  T8
                   ^
                   |
             U+    |    V+
                \  |  /
                 \ | /
       I- ---------+--------- I+   T3
                 / | \
                /  |  \
             V-    |    U-
```

---

## II. Gell-Mann Matrices

> **Definition 1. Complex \(3 \times 3\) matrices.**
>
> The package fixes the ambient matrix type.
>
> **In Lean:**
>
> ```lean
> abbrev Physics.YangMills.Matrix3x3 :=
>   Matrix (Fin 3) (Fin 3) ℂ
> ```

> **Definition 2. The unnormalised diagonal matrix for \(\lambda_8\).**
>
> The diagonal matrix \(\operatorname{diag}(1,1,-2)\) is separated out before
> applying the factor \(1/\sqrt{3}\).
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.gellMannLambda8 : Matrix3x3 :=
>   !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, -2]
> ```

> **Theorem 1. The \(\lambda_8\) numerator has trace zero.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.gellMannLambda8_trace_zero :
>     gellMannLambda8.trace = 0
> ```

> **Definition 3. The eight Hermitian Gell-Mann matrices.**
>
> The matrices \(\lambda_1,\ldots,\lambda_8\) are stored as a function on
> `Fin 8`.
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.gellMannHermitian :
>     Fin 8 → Matrix3x3
> ```

> **Definition 4. The anti-Hermitian generators.**
>
> The physics generators are
>
> $$
> T^a = i\lambda_a.
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.gellMannGenerator
>     (i : Fin 8) : Matrix3x3 :=
>   I • gellMannHermitian i
> ```

> **Theorem 2. The Hermitian matrices are traceless.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.gellMannHermitian_trace_zero
>     (i : Fin 8) :
>     (gellMannHermitian i).trace = 0
> ```

> **Theorem 3. The generators are anti-Hermitian.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.gellMannGenerator_antiHermitian
>     (i : Fin 8) :
>     (gellMannGenerator i).conjTranspose = -gellMannGenerator i
> ```

> **Theorem 4. The generators are traceless.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.gellMannGenerator_trace_zero
>     (i : Fin 8) :
>     (gellMannGenerator i).trace = 0
> ```

---

## III. The Concrete Lie Algebra

> **Definition 5. The concrete \( \mathfrak{su}(3) \) type.**
>
> The Lie algebra is represented as the subtype of anti-Hermitian trace-zero
> matrices.
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.LieAlgebraSU3 :=
>   { M : Matrix3x3 // M.conjTranspose = -M ∧ M.trace = 0 }
> ```

> **Definition 6. Gell-Mann generators as elements of \( \mathfrak{su}(3) \).**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.gellMannLieAlgebra
>     (i : Fin 8) : LieAlgebraSU3
> ```

> **Definition 7. Addition inside \( \mathfrak{su}(3) \).**
>
> Addition is certified to preserve anti-Hermiticity and trace zero.
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.lieAdd
>     (A B : LieAlgebraSU3) : LieAlgebraSU3
> ```

> **Definition 8. The matrix commutator.**
>
> The Lie bracket is the matrix commutator
>
> $$
> [A,B] = AB - BA.
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.lieCommutator
>     (A B : LieAlgebraSU3) : LieAlgebraSU3
> ```

> **Theorem 5. The commutator is anti-Hermitian.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.lieCommutator_antiHermitian
>     (A B : LieAlgebraSU3) :
>     (A.val * B.val - B.val * A.val).conjTranspose =
>       -(A.val * B.val - B.val * A.val)
> ```

> **Theorem 6. The commutator is traceless.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.lieCommutator_trace_zero
>     (A B : LieAlgebraSU3) :
>     (A.val * B.val - B.val * A.val).trace = 0
> ```

> **Definition 9. The real submodule of trace-zero anti-Hermitian matrices.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.lieAlgebraSU3Submodule :
>     Submodule ℝ Matrix3x3
> ```

The live file also provides the concrete `Zero`, `Add`, `Neg`, `Sub`, scalar
multiplication, `LieRing`, and `LieAlgebra ℝ` instances on `LieAlgebraSU3`.

---

## IV. Structure Constants

> **Definition 10. Rational numerator table.**
>
> The rational part of \(f^{abc}\) is encoded as an integer table.
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.structureConstantRatNum :
>     Fin 8 → Fin 8 → Fin 8 → ℤ
> ```

> **Definition 11. Square-root coefficient table.**
>
> The \(\sqrt{3}\)-part is also encoded as an integer table.
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.structureConstantSqrtCoeffNum :
>     Fin 8 → Fin 8 → Fin 8 → ℤ
> ```

> **Definition 12. The real structure constants.**
>
> The final real constants combine the rational and \(\sqrt{3}\) contributions:
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.structureConstant
>     (a b c : Fin 8) : ℝ
> ```

> **Definition 13. The commutator coefficients.**
>
> These are the coefficients appearing in the anti-Hermitian convention:
>
> $$
> [T^a,T^b] = -2 f^{abc} T^c.
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.commutatorStructureCoeff
>     (a b c : Fin 8) : ℝ
> ```

> **Theorem 7. Antisymmetry.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.structureConstant_antisymm
>     (a b c : Fin 8) :
>     structureConstant a b c = -structureConstant b a c
> ```

> **Theorem 8. Cyclic symmetry.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.structureConstant_cyclic
>     (a b c : Fin 8) :
>     structureConstant a b c = structureConstant b c a
> ```

> **Theorem 9. Jacobi identity for the structure constants.**
>
> The finite table satisfies the Jacobi contraction identity.
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.structureConstant_jacobi
>     (a b c d : Fin 8) :
>     (∑ e : Fin 8,
>       structureConstant a b e * structureConstant e c d +
>       structureConstant b c e * structureConstant e a d +
>       structureConstant c a e * structureConstant e b d) = 0
> ```

> **Theorem 10. The adjoint Casimir contraction.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.structureConstant_casimir
>     (c d : Fin 8) :
>     (∑ a : Fin 8, ∑ b : Fin 8,
>       structureConstant a c b * structureConstant a d b) =
>       if c = d then 3 else 0
> ```

> **Theorem 11. The commutator coefficient relation.**
>
> **In Lean:**
>
> ```lean
> abbrev Physics.YangMills.gellMann_commutator_relation
>     (a b c : Fin 8) :
>     commutatorStructureCoeff a b c =
>       -2 * structureConstant a b c
> ```

---

## V. The Gell-Mann Commutator

> **Definition 14. The concrete matrix commutator of generators.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.gellMannCommutatorMatrix
>     (a b : Fin 8) : Matrix3x3 :=
>   gellMannGenerator a * gellMannGenerator b -
>     gellMannGenerator b * gellMannGenerator a
> ```

> **Theorem 12. The definition unfolds to the matrix commutator.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.generator_commutator_matrix
>     (a b : Fin 8) :
>     gellMannCommutatorMatrix a b =
>       gellMannGenerator a * gellMannGenerator b -
>         gellMannGenerator b * gellMannGenerator a
> ```

> **Definition 15. The commutator as an element of \( \mathfrak{su}(3) \).**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.gellMannCommutatorLie
>     (a b : Fin 8) : LieAlgebraSU3
> ```

> **Theorem 13. The packaged commutator agrees with the Lie bracket.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.gellMann_commutator
>     (a b : Fin 8) :
>     gellMannCommutatorLie a b =
>       ⁅gellMannLieAlgebra a, gellMannLieAlgebra b⁆
> ```

> **Definition 16. Linear combination of Gell-Mann basis elements.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.gellMannLieCombination
>     (coeff : Fin 8 → ℝ) : LieAlgebraSU3
> ```

> **Theorem 14. The commutator equals the structure-constant combination.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.gellMann_commutator_structure
>     (a b : Fin 8) :
>     gellMannCommutatorLie a b =
>       gellMannCommutatorCombination a b
> ```

> **Theorem 15. Matrix Jacobi identity.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.gellMannCommutatorMatrix_jacobi
>     (a b c : Fin 8) :
>     gellMannCommutatorMatrix a b * gellMannGenerator c -
>       gellMannGenerator c * gellMannCommutatorMatrix a b +
>       gellMannCommutatorMatrix b c * gellMannGenerator a -
>       gellMannGenerator a * gellMannCommutatorMatrix b c +
>       gellMannCommutatorMatrix c a * gellMannGenerator b -
>       gellMannGenerator b * gellMannCommutatorMatrix c a = 0
> ```

---

## VI. Adjoint Representation and Killing Form

> **Definition 17. The adjoint representation matrix.**
>
> The adjoint matrix is defined by the structure constants:
>
> $$
> (\operatorname{ad} T^a)_{bc} = f^{abc}.
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.adjointMatrix
>     (a : Fin 8) : Matrix (Fin 8) (Fin 8) ℝ :=
>   fun b c => structureConstant a b c
> ```

> **Theorem 16. Adjoint matrices are antisymmetric.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.adjointMatrix_antisymm
>     (a : Fin 8) :
>     (adjointMatrix a)ᵀ = -adjointMatrix a
> ```

> **Theorem 17. The adjoint representation respects the bracket.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.adjoint_isLieHomomorphism
>     (a b : Fin 8) :
>     adjointMatrix a * adjointMatrix b -
>       adjointMatrix b * adjointMatrix a =
>       ∑ c : Fin 8,
>         commutatorStructureCoeff a b c • adjointMatrix c
> ```

> **Definition 18. The adjoint Casimir.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.adjointCasimir :
>     Matrix (Fin 8) (Fin 8) ℝ :=
>   ∑ a : Fin 8, adjointMatrix a * adjointMatrix a
> ```

> **Theorem 18. The adjoint Casimir is diagonal.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.adjointCasimir_diagonal :
>     adjointCasimir = fun i j => if i = j then -3 else 0
> ```

> **Definition 19. The Killing form on the Gell-Mann basis.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.killingFormBasis
>     (a b : Fin 8) : ℝ :=
>   (adjointMatrix a * adjointMatrix b).trace
> ```

> **Theorem 19. The Killing form is symmetric.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.killingFormBasis_symm
>     (a b : Fin 8) :
>     killingFormBasis a b = killingFormBasis b a
> ```

> **Theorem 20. The Killing form is diagonal in the basis.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.killingFormBasis_diagonal
>     (a b : Fin 8) :
>     killingFormBasis a b = if a = b then -3 else 0
> ```

---

## VII. Cartan Pair and Fundamental Casimir

> **Definition 20. Cartan indices.**
>
> The Cartan pair is represented by the third and eighth Gell-Mann generators.
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.cartanIndex1 : Fin 8 := 2
> def Physics.YangMills.cartanIndex2 : Fin 8 := 7
> ```

> **Theorem 21. The Cartan generators commute.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.cartanGenerators_commute :
>     gellMannCommutatorMatrix cartanIndex1 cartanIndex2 = 0
> ```

> **Definition 21. The Cartan generator set.**
>
> **In Lean:**
>
> ```lean
> def Physics.YangMills.cartanGeneratorSet : Finset (Fin 8) :=
>   {cartanIndex1, cartanIndex2}
> ```

> **Theorem 22. Fundamental trace normalization.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.generator_trace_fundamental
>     (a b : Fin 8) :
>     (gellMannGenerator a * gellMannGenerator b).trace =
>       if a = b then -2 else 0
> ```

> **Definition 22. The fundamental quadratic Casimir.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Physics.YangMills.fundamentalCasimir : Matrix3x3 :=
>   ∑ a : Fin 8, gellMannGenerator a * gellMannGenerator a
> ```

> **Theorem 23. The fundamental Casimir is scalar.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.fundamentalCasimir_diagonal :
>     fundamentalCasimir =
>       fun i j => if i = j then (-16 / 3 : ℂ) else 0
> ```

> **Theorem 24. The trace of the fundamental Casimir.**
>
> **In Lean:**
>
> ```lean
> theorem Physics.YangMills.fundamentalCasimir_trace :
>     fundamentalCasimir.trace = (-16 : ℂ)
> ```

---

## VIII. Architecture

The live file is fused in dependency order:

```text
GellMann
  -> LieAlgebra
    -> StructureConstants
      -> Commutator
        -> Representation
```

The package separates three layers:

- the concrete matrix model of \( \mathfrak{su}(3) \);
- the finite structure-constant certificates;
- the representation-theoretic consequences.

This separation is important for future review.  The concrete physics API may
belong in Physlib, while generic matrix and Lie-algebra infrastructure can be
split into Mathlib contributions if reviewers request it.

---

## IX. Axiom Certificate

The representative certificate command is:

```text
echo 'import SU3Concrete
#print axioms Physics.YangMills.gellMannGenerator_antiHermitian
#print axioms Physics.YangMills.generator_commutator_matrix
#print axioms Physics.YangMills.structureConstant_jacobi
#print axioms Physics.YangMills.adjointCasimir_diagonal
#print axioms Physics.YangMills.killingFormBasis_diagonal
#print axioms Physics.YangMills.fundamentalCasimir_diagonal' \
  | lake env lean --stdin
```

The current certificate is:

```text
'Physics.YangMills.gellMannGenerator_antiHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Physics.YangMills.generator_commutator_matrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'Physics.YangMills.structureConstant_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound]
'Physics.YangMills.adjointCasimir_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Physics.YangMills.killingFormBasis_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Physics.YangMills.fundamentalCasimir_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There are no package-local axioms in these certificates.

---

## X. Reading Guide

For a first pass, read the file in this order:

1. `gellMannHermitian` and `gellMannGenerator`.
2. `LieAlgebraSU3` and `lieCommutator`.
3. `structureConstant` and `structureConstant_jacobi`.
4. `gellMannCommutatorMatrix` and `gellMann_commutator_structure`.
5. `adjointMatrix`, `killingFormBasis`, and `fundamentalCasimir`.

The shortest mathematical spine of the package is:

```text
Tᵃ = iλₐ
Tᵃ ∈ su(3)
[Tᵃ,Tᵇ] = -2 f^{abc}Tᶜ
Jacobi(f)
ad(Tᵃ)_{bc} = f^{abc}
κ(Tᵃ,Tᵇ) = -3δᵃᵇ
Σₐ TᵃTᵃ = -(16/3)I₃
```

---

## XI. Verification

The live file was checked with:

```text
lake env lean M4TH/SU3Concrete/SU3ConcreteLive/SU3Concrete.live.lean
```

The package build command is:

```text
lake build SU3Concrete
```

Both checks are intended to be rerun before publication or Zulip discussion.
