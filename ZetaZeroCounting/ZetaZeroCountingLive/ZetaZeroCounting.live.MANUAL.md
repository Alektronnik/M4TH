# ZetaZeroCounting

**A single-file live presentation of zero-counting infrastructure for the
Riemann zeta function, formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0
- Companion file: `ZetaZeroCounting.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`ZetaZeroCounting.live.lean`.  It presents the mathematical content in a
classical theorem-style format: first the analytic idea, then the corresponding
Lean statement.  Proof scripts are intentionally omitted here; the live Lean
file is the certificate.

---

## I. The Mathematical Problem

The Riemann--von Mangoldt theory studies the number of nontrivial zeros of the
Riemann zeta function in the critical strip

$$
0 < \operatorname{Re}(s) < 1.
$$

The classical counting function is usually denoted by \(N(T)\): it counts zeros
whose imaginary part lies between \(0\) and \(T\), with multiplicity.  Its main
term is

$$
\frac{T}{2\pi}\left(\log\frac{T}{2\pi} - 1\right).
$$

The purpose of this package is not to prove the full Riemann--von Mangoldt
formula.  Instead, it builds the infrastructure needed for that theorem:

- the Xi functions used to remove the pole of zeta,
- the nontrivial zero set,
- a finite zero-counting domain,
- multiplicity-based and distinct zero counts,
- safe heights for contour integration,
- and the asymptotic theory of the von Mangoldt main term.

The package records the Riemann--von Mangoldt theorem itself only as a typed
proposition, never as an axiom.


The geometric object behind the later contour argument is the critical box:

```text
              Im(s)
                ^
                |
            iT  +-------------------+   1 + iT
                |                   |
                |    critical box   |
                |                   |
             0  +-------------------+   1
                0                   1  -> Re(s)
```

---

## II. Fundamental Definitions

> **Definition 1. The classical Riemann Xi function.**
>
> The package defines the classical Xi function by multiplying the completed
> zeta function by the factor that cancels its poles at \(0\) and \(1\):
>
> $$
> \xi(s) = \frac{1}{2}s(s-1)\Lambda(s).
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def Riemann.riemannXi (s : ℂ) : ℂ :=
>   (1 / 2) * s * (s - 1) * completedRiemannZeta s
> ```

> **Definition 2. The nontrivial zeros.**
>
> The nontrivial zeros are the zeros of \(\zeta\) lying strictly inside the
> critical strip:
>
> $$
> \{s \in \mathbb{C} : \zeta(s)=0,\ 0 < \operatorname{Re}(s) < 1\}.
> $$
>
> **In Lean:**
>
> ```lean
> def Riemann.nontrivialZeros : Set ℂ :=
>   {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}
> ```

> **Definition 3. The entire Xi variant.**
>
> For contour arguments, it is useful to work with an entire variant that is
> nonzero at the corners \(0\) and \(1\):
>
> $$
> \Xi_0(s) = s(s-1)\Lambda_0(s)+1.
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def Riemann.entireXi (s : ℂ) : ℂ :=
>   s * (s - 1) * completedRiemannZeta₀ s + 1
> ```

> **Definition 4. The critical box and the finite counting domain.**
>
> For a height \(T\), zeros are counted inside the critical strip with
> \(0 < \operatorname{Im}(s) \leq T\):
>
> $$
> \{s \in \mathbb{C} : \zeta(s)=0,\ 0<\operatorname{Re}(s)<1,\
> 0<\operatorname{Im}(s)\leq T\}.
> $$
>
> **In Lean:**
>
> ```lean
> def Riemann.zerosUpToIm (T : ℝ) : Set ℂ :=
>   {s : ℂ | s ∈ nontrivialZeros ∧ 0 < s.im ∧ s.im ≤ T}
> ```

> **Definition 5. The zero-counting function with multiplicity.**
>
> The canonical \(N(T)\) of the package sums the analytic multiplicities of the
> counted zeros of `entireXi`:
>
> $$
> N(T)=\sum_{\substack{\rho\in Z\\0<\operatorname{Im}(\rho)\leq T}}
> \operatorname{ord}_{\rho}(\Xi_0).
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def Riemann.zeroCountingFun (T : ℝ) : ℝ :=
>   Nat.cast ((zerosUpToImFinset T).sum entireXiZeroMultiplicity)
> ```

> **Definition 6. Safe heights.**
>
> A height \(T\) is safe when the horizontal line \(\operatorname{Im}(s)=T\)
> contains no nontrivial zero:
>
> $$
> \forall \rho\in Z,\quad \operatorname{Im}(\rho)\neq T.
> $$
>
> **In Lean:**
>
> ```lean
> def Riemann.IsSafeHeight (T : ℝ) : Prop :=
>   ∀ s ∈ nontrivialZeros, s.im ≠ T
> ```

---

## III. Fundamental Theorems

> **Theorem 1. Symmetry of the nontrivial zeros.**
>
> If \(s\) is a nontrivial zero, then so is \(1-s\).  This is the zero-set
> manifestation of the functional equation.
>
> **In Lean:**
>
> ```lean
> theorem Riemann.one_sub_mem_nontrivialZeros
>     (s : ℂ) (hs : s ∈ nontrivialZeros) :
>     1 - s ∈ nontrivialZeros
> ```

> **Theorem 2. Functional equation of Xi.**
>
> The classical Xi function satisfies the symmetry
>
> $$
> \xi(1-s)=\xi(s).
> $$
>
> **In Lean:**
>
> ```lean
> theorem Riemann.riemannXi_functional_equation (s : ℂ) :
>     riemannXi (1 - s) = riemannXi s
> ```

> **Theorem 3. The dictionary between zeta zeros and `entireXi` zeros.**
>
> Inside the open critical strip, zeros of zeta correspond to zeros of the
> entire Xi variant.
>
> **In Lean:**
>
> ```lean
> lemma Riemann.entireXi_eq_zero_of_mem_nontrivialZeros
>     (s : ℂ) (hs : s ∈ nontrivialZeros) :
>     entireXi s = 0
> ```
>
> ```lean
> lemma Riemann.mem_nontrivialZeros_of_entireXi_eq_zero
>     {s : ℂ} (hzero : entireXi s = 0)
>     (hband : 0 < s.re ∧ s.re < 1) :
>     s ∈ nontrivialZeros
> ```

> **Theorem 4. Finiteness of the zero-counting domain.**
>
> For every height \(T\), the set of nontrivial zeros with
> \(0<\operatorname{Im}(s)\leq T\) is finite.
>
> **In Lean:**
>
> ```lean
> theorem Riemann.zerosUpToIm_finite (T : ℝ) :
>     (zerosUpToIm T).Finite
> ```

> **Theorem 5. Multiplicity count dominates distinct count.**
>
> Counting zeros with analytic multiplicity always dominates counting them
> merely as distinct points:
>
> $$
> N_{\mathrm{distinct}}(T)\leq N(T).
> $$
>
> **In Lean:**
>
> ```lean
> theorem Riemann.distinctZeroCount_le_zeroCountingFun (T : ℝ) :
>     distinctZeroCount T ≤ zeroCountingFun T
> ```

> **Theorem 6. Equality under simplicity.**
>
> If every counted zero of `entireXi` is simple, then the multiplicity count and
> the distinct count agree.
>
> **In Lean:**
>
> ```lean
> theorem Riemann.zeroCountingFun_eq_distinctZeroCount_of_all_simple
>     (T : ℝ) (h : AllEntireXiZerosSimple) :
>     zeroCountingFun T = distinctZeroCount T
> ```

> **Theorem 7. Safe heights are dense above every positive height.**
>
> Every interval \((T,T+\varepsilon]\), with \(T>0\) and \(\varepsilon>0\),
> contains a safe height.
>
> **In Lean:**
>
> ```lean
> theorem Riemann.exists_safe_height_in_interval
>     (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
>     ∃ T', T < T' ∧ T' ≤ T + ε ∧ IsSafeHeight T'
> ```

> **Theorem 8. Nonvanishing on the top edge at a safe height.**
>
> At a safe height, the top edge of the critical box avoids the nontrivial zeros
> in the open strip.
>
> **In Lean:**
>
> ```lean
> lemma Riemann.riemannXi_ne_zero_on_top_edge_of_safeHeight
>     {T : ℝ} (_hT : 0 < T) (hSafe : IsSafeHeight T)
>     {s : ℂ} (hs : s ∈ criticalBoxTopEdge T)
>     (hs_re : 0 < s.re ∧ s.re < 1) :
>     riemannXi s ≠ 0
> ```

---

## IV. The von Mangoldt Main Term

The main term of the Riemann--von Mangoldt formula is formalised as

$$
M(T)=\frac{T}{2\pi}\left(\log\frac{T}{2\pi}-1\right).
$$

> **Definition 7. The classical main term.**
>
> **In Lean:**
>
> ```lean
> noncomputable def Riemann.vonMangoldtMainTerm (T : ℝ) : ℝ :=
>   (T / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) - 1)
> ```

> **Definition 8. The simplified asymptotic main term.**
>
> The simplified comparison function is
>
> $$
> M_0(T)=\frac{T}{2\pi}\log T.
> $$
>
> **In Lean:**
>
> ```lean
> noncomputable def Riemann.vonMangoldtMainTermSimplified (T : ℝ) : ℝ :=
>   (T / (2 * Real.pi)) * Real.log T
> ```

> **Theorem 9. The two main terms are asymptotically equivalent.**
>
> **In Lean:**
>
> ```lean
> theorem Riemann.vonMangoldt_mainTerm_simplified_equiv_classical :
>     IsEquivalent atTop
>       vonMangoldtMainTermSimplified
>       vonMangoldtMainTerm
> ```

> **Theorem 10. The main term tends to infinity.**
>
> **In Lean:**
>
> ```lean
> lemma Riemann.vonMangoldtMainTerm_tendsto_atTop :
>     Tendsto vonMangoldtMainTerm atTop atTop
> ```

> **Theorem 11. The main term dominates \(T\) and \(\log T\).**
>
> **In Lean:**
>
> ```lean
> lemma Riemann.T_isLittleO_vonMangoldtMainTerm :
>     (fun T : ℝ => T) =o[atTop] vonMangoldtMainTerm
> ```
>
> ```lean
> lemma Riemann.log_isLittleO_vonMangoldtMainTerm :
>     Real.log =o[atTop] vonMangoldtMainTerm
> ```

---

## V. The Riemann--von Mangoldt Statement

The package deliberately does **not** assume the Riemann--von Mangoldt theorem.
It records the theorem as a typed proposition:

$$
N_{\mathrm{distinct}}(T)\sim M(T).
$$

> **Definition 9. The typed counting statement.**
>
> **In Lean:**
>
> ```lean
> def Riemann.RiemannVonMangoldtCounting : Prop :=
>   IsEquivalent atTop distinctZeroCount vonMangoldtMainTerm
> ```

> **Theorem 12. Transfer to the simplified main term.**
>
> If the Riemann--von Mangoldt statement is supplied as a hypothesis, then the
> count is also asymptotic to the simplified main term.
>
> **In Lean:**
>
> ```lean
> theorem Riemann.riemannVonMangoldtCounting_simplified
>     (h : RiemannVonMangoldtCounting) :
>     IsEquivalent atTop distinctZeroCount vonMangoldtMainTermSimplified
> ```

This distinction is important: `RiemannVonMangoldtCounting` is a proposition,
not an axiom.  The package can reason conditionally from it, but it never
postulates it globally.

---

## VI. Scholium

The package is a preparatory layer for contour and argument-principle
formalisation.  The role of safe heights is geometric: a rectangular contour
around the critical box must avoid zeros on its boundary.  The finite forbidden
set of zero ordinates lets us perturb the top edge to a nearby height that
crosses no zero.

The role of `entireXi` is analytic: it replaces zeta by an entire function whose
zeros in the open critical strip match the nontrivial zeros of zeta, while
avoiding artificial corner zeros.  This makes multiplicity counting compatible
with Mathlib's analytic-order infrastructure.

The role of the main-term file is asymptotic: it isolates the real-variable
estimates for

$$
\frac{T}{2\pi}\left(\log\frac{T}{2\pi}-1\right),
$$

so later packages can focus on contour integrals rather than elementary
growth estimates.

---

## VII. Logical Certificate

This development contains no package-local axioms and no `sorry`.

The intended certificate commands are:

```lean
import ZetaZeroCounting

#print axioms Riemann.one_sub_mem_nontrivialZeros
#print axioms Riemann.distinctZeroCount_le_zeroCountingFun
#print axioms Riemann.exists_safe_height_in_interval
#print axioms Riemann.vonMangoldt_mainTerm_simplified_equiv_classical
```

The expected terminal output contains only the standard foundational axioms used
by Mathlib:

```text
'Riemann.one_sub_mem_nontrivialZeros' depends on axioms: [propext, Classical.choice, Quot.sound]
'Riemann.distinctZeroCount_le_zeroCountingFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'Riemann.exists_safe_height_in_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'Riemann.vonMangoldt_mainTerm_simplified_equiv_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Any additional package-local axiom would be a defect.

---

## VIII. Live File

For web inspection and study, use:

```text
ZetaZeroCounting.live.lean
```

That file is the fused single-file edition of the package in dependency order:

```text
Xi
ZeroCounting
SafeHeights
MainTerm
```

The manual explains the mathematical route.  The `.live.lean` file is the
machine-checkable certificate.


Reference paths:

- Live source: `ZetaZeroCounting.live.lean`
- Package root: `ZetaZeroCounting.lean`
- Source directory: `ZetaZeroCounting/`

---

## IX. Verification

The live file and the modular package are checked with:

```text
lake env lean ZetaZeroCounting/ZetaZeroCountingLive/ZetaZeroCounting.live.lean
lake build ZetaZeroCounting
```
