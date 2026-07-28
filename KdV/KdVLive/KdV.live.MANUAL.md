# KdV

**A single-file live presentation of the exact one-soliton profile and
conservation laws for the Korteweg-de Vries equation, formalised in Lean 4 over
Mathlib.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0
- Companion file: `KdV.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`KdV.live.lean`.  It presents the mathematical content in a classical
theorem-style format: first the analytic idea, then the corresponding Lean
statement.  Proof scripts are intentionally omitted here; the live Lean file is
the certificate.

---

## I. The Mathematical Problem

The Korteweg-de Vries equation in the normalization used by this package is

$$
u_t + u u_x + u_{xxx}=0.
$$

It is a dispersive nonlinear equation.  The nonlinear transport term \(u u_x\)
interacts with the third spatial derivative \(u_{xxx}\), allowing coherent
travelling waves whose shape is preserved by the evolution.

The central travelling-wave ansatz is

$$
u(t,x)=f(x-ct),
$$

where \(c\) is the wave speed.  Substituting this ansatz into KdV reduces the
PDE to the stationary third-order ODE

$$
-c f' + f f' + f''' = 0.
$$

The exact one-soliton profile treated in the package is

$$
f(x)=3c\,\operatorname{sech}^2\left(\frac{\sqrt c}{2}x\right),
\qquad c>0.
$$

The package also formalises the rate form of the two classical compact-support
conservation identities:

$$
\int_{\mathbb R} u_t(t,x)\,dx=0,
\qquad
\int_{\mathbb R} u(t,x)u_t(t,x)\,dx=0.
$$

The geometry of the soliton part is:

```text
       u
       ^
       |
  3c   |              ***
       |           **     **
       |         **         **
       |_______**_____________**______> x
              -ct             +ct

        profile f(x - ct) translates without changing shape
```

---

## II. Smooth KdV Solutions

> **Definition 1. Smooth KdV solution predicate.**
>
> A function \(u : \mathbb R \to \mathbb R \to \mathbb R\) is a KdV solution on
> the interval \([0,T)\) when it has the required differentiability and satisfies
>
> $$
> u_t + u u_x + u_{xxx}=0
> $$
>
> pointwise on that interval.
>
> **In Lean:**
>
> ```lean
> structure IsSolution (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop where
>   differentiable : Differentiable ℝ (fun p : ℝ × ℝ => u p.1 p.2)
>   differentiable_dx : ∀ t, Differentiable ℝ (fun x => deriv (u t) x)
>   differentiable_dxx : ∀ t, Differentiable ℝ (fun y => deriv (fun x => deriv (u t) x) y)
>   pde : ∀ t ∈ Set.Ico 0 T, ∀ x,
>     deriv (fun s => u s x) t + u t x * deriv (u t) x +
>       deriv (fun y => deriv (fun z => deriv (u t) z) y) x = 0
> ```

> **Definition 2. Travelling-wave profile.**
>
> A travelling wave with speed \(c\) is represented by a profile with enough
> differentiability to form the third-order stationary equation.
>
> **In Lean:**
>
> ```lean
> structure TravellingWave (c : ℝ) where
>   profile : ℝ → ℝ
>   differentiable : Differentiable ℝ profile
>   differentiable_deriv : Differentiable ℝ (fun x => deriv profile x)
>   differentiable_deriv2 : Differentiable ℝ (fun y => deriv (fun x => deriv profile x) y)
> ```

---

## III. Travelling-Wave Calculus

The ansatz \(u(t,x)=f(x-ct)\) requires three elementary derivative identities.

> **Theorem 1. Time derivative of the travelling-wave ansatz.**
>
> **In Lean:**
>
> ```lean
> lemma travellingWave_deriv_time (f : ℝ → ℝ) (c t x : ℝ) :
>     deriv (fun s => f (x - c * s)) t = -c * deriv f (x - c * t)
> ```

> **Theorem 2. Spatial derivative of the travelling-wave ansatz.**
>
> **In Lean:**
>
> ```lean
> lemma travellingWave_deriv_space (f : ℝ → ℝ) (c t x : ℝ) :
>     deriv (fun y => f (y - c * t)) x = deriv f (x - c * t)
> ```

> **Theorem 3. Third spatial derivative of the travelling-wave ansatz.**
>
> **In Lean:**
>
> ```lean
> lemma travellingWave_deriv_space3 (f : ℝ → ℝ) (c t x : ℝ) :
>     deriv (fun y => deriv (fun z => deriv (fun w => f (w - c * t)) z) y) x =
>       deriv (fun y => deriv (fun z => deriv f z) y) (x - c * t)
> ```

> **Theorem 4. Travelling-wave reduction.**
>
> If a KdV solution is given by a travelling-wave profile, then the profile
> satisfies the stationary soliton ODE.
>
> $$
> -c f' + f f' + f'''=0.
> $$
>
> **In Lean:**
>
> ```lean
> theorem travellingWave_reduction {T : ℝ} {u : ℝ → ℝ → ℝ} (sol : IsSolution T u)
>     (c : ℝ) (wave : TravellingWave c)
>     (h_wave : ∀ t x, u t x = wave.profile (x - c * t))
>     (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : ℝ) :
>     -c * deriv wave.profile (x - c * t) +
>       wave.profile (x - c * t) * deriv wave.profile (x - c * t) +
>       deriv (fun y => deriv (fun z => deriv wave.profile z) y) (x - c * t) = 0
> ```

---

## IV. Hyperbolic Calculus

The exact soliton is written using the hyperbolic secant.

> **Definition 3. Hyperbolic secant.**
>
> **In Lean:**
>
> ```lean
> noncomputable def sech (x : ℝ) : ℝ := 1 / Real.cosh x
> ```

> **Definition 4. The KdV soliton profile.**
>
> **In Lean:**
>
> ```lean
> noncomputable def solitonProfile (c x : ℝ) : ℝ :=
>   3 * c * sech (Real.sqrt c / 2 * x) ^ 2
> ```

> **Theorem 5. Nonvanishing of cosh.**
>
> **In Lean:**
>
> ```lean
> lemma cosh_ne_zero (x : ℝ) : Real.cosh x ≠ 0
> ```

> **Theorem 6. Nonvanishing of sech.**
>
> **In Lean:**
>
> ```lean
> lemma sech_ne_zero (x : ℝ) : sech x ≠ 0
> ```

> **Theorem 7. Squared-sech identity.**
>
> The identity
>
> $$
> \operatorname{sech}^2 x = 1-\tanh^2 x
> $$
>
> is the algebraic key used to collapse the final soliton ODE.
>
> **In Lean:**
>
> ```lean
> lemma sech_sq_eq_one_sub_tanh_sq (x : ℝ) :
>     sech x ^ 2 = 1 - Real.tanh x ^ 2
> ```

> **Theorem 8. Derivative of sech.**
>
> **In Lean:**
>
> ```lean
> lemma hasDerivAt_sech (x : ℝ) :
>     HasDerivAt sech (-sech x * Real.tanh x) x
> ```

> **Theorem 9. Derivative of scaled sech.**
>
> **In Lean:**
>
> ```lean
> lemma hasDerivAt_sech_mul (k x : ℝ) :
>     HasDerivAt (fun y => sech (k * y))
>       (-k * sech (k * x) * Real.tanh (k * x)) x
> ```

> **Theorem 10. Derivative of scaled tanh.**
>
> **In Lean:**
>
> ```lean
> lemma hasDerivAt_tanh_mul (k x : ℝ) :
>     HasDerivAt (fun y => Real.tanh (k * y))
>       (k * sech (k * x) ^ 2) x
> ```

> **Theorem 11. Derivative of squared scaled sech.**
>
> **In Lean:**
>
> ```lean
> lemma hasDerivAt_sech_sq_mul (k x : ℝ) :
>     HasDerivAt (fun y => sech (k * y) ^ 2)
>       (-2 * k * sech (k * x) ^ 2 * Real.tanh (k * x)) x
> ```

---

## V. The Exact Soliton

The derivative chain for

$$
3c\,\operatorname{sech}^2(kx)
$$

is formalised directly in Lean.

> **Theorem 12. First derivative of the soliton profile.**
>
> **In Lean:**
>
> ```lean
> lemma soliton_deriv1 (c k ξ : ℝ) :
>     deriv (fun x => 3 * c * sech (k * x) ^ 2) ξ =
>       -6 * c * k * sech (k * ξ) ^ 2 * Real.tanh (k * ξ)
> ```

> **Theorem 13. Third derivative of the soliton profile.**
>
> **In Lean:**
>
> ```lean
> lemma soliton_deriv3 (c k ξ : ℝ) :
>     deriv (fun y => deriv (fun z => deriv (fun x => 3 * c * sech (k * x) ^ 2) z) y) ξ =
>       24 * c * k ^ 3 * sech (k * ξ) ^ 2 * Real.tanh (k * ξ) *
>         (2 - 3 * Real.tanh (k * ξ) ^ 2)
> ```

> **Theorem 14. The exact soliton satisfies KdV.**
>
> For every positive speed \(c\), the classical profile
>
> $$
> f(x)=3c\,\operatorname{sech}^2\left(\frac{\sqrt c}{2}x\right)
> $$
>
> satisfies the stationary ODE
>
> $$
> -c f' + f f' + f'''=0.
> $$
>
> **In Lean:**
>
> ```lean
> theorem soliton_satisfies_kdv (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
>     -c * deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) ξ +
>       (3 * c * sech (Real.sqrt c / 2 * ξ) ^ 2) *
>         deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) ξ +
>       deriv (fun y => deriv (fun z =>
>         deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) z) y) ξ = 0
> ```

---

## VI. Compact-Support Conservation Laws

The conservation part separates the formal rates from the analytic hypotheses
needed to justify integration by parts.

> **Definition 5. Mass and quadratic energy.**
>
> **In Lean:**
>
> ```lean
> noncomputable def mass (u : ℝ → ℝ) : ℝ :=
>   ∫ x, u x
> ```
>
> ```lean
> noncomputable def energy (u : ℝ → ℝ) : ℝ :=
>   ∫ x, u x ^ 2 / 2
> ```

> **Definition 6. Time and spatial derivatives.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ut (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
>   deriv (fun s => u s x) t
> ```
>
> ```lean
> noncomputable def ux (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
>   deriv (u t) x
> ```
>
> ```lean
> noncomputable def uxxx (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
>   deriv (fun y => deriv (fun z => deriv (u t) z) y) x
> ```

> **Definition 7. Conserved compact-support solution.**
>
> A conserved solution is a KdV solution whose spatial slices have support in a
> fixed compact set and whose spatial regularity is sufficient for the third
> derivative integration-by-parts identities.
>
> **In Lean:**
>
> ```lean
> structure ConservedSolution (T : ℝ) (u : ℝ → ℝ → ℝ) where
>   solution : IsSolution T u
>   support_K : Set ℝ
>   support_K_compact : IsCompact support_K
>   support_subset : ∀ t ∈ Set.Ico 0 T, tsupport (fun x => u t x) ⊆ support_K
>   smooth_space : ∀ t ∈ Set.Ico 0 T, ContDiff ℝ 3 (fun x => u t x)
> ```

> **Theorem 15. Conservation of mass in rate form.**
>
> **In Lean:**
>
> ```lean
> theorem massRate_conserved (sol : ConservedSolution T u)
>     {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
>     ∫ x, KdV.ut u t x = 0
> ```

> **Theorem 16. Conservation of quadratic energy in rate form.**
>
> **In Lean:**
>
> ```lean
> theorem energyRate_conserved (sol : ConservedSolution T u)
>     {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
>     ∫ x, u t x * KdV.ut u t x = 0
> ```

---

## VII. Formal Architecture

The live file follows the same logical order as the modular package:

```text
KdV.live.lean
|
+-- Smooth KdV solution predicate
+-- Travelling-wave chain rules
+-- Reduction to the stationary soliton ODE
+-- Hyperbolic secant calculus
+-- Exact squared-sech soliton computation
+-- Compact-support conservation identities
```

The modular package uses separate source files for Mathlib review.  The live
file fuses those modules into a single text so that web readers can inspect the
entire development without navigating the package tree.

---

## VIII. Axiom Certificate

Run the certificate command:

```text
printf 'import KdV
#print axioms KdV.travellingWave_reduction
#print axioms KdV.soliton_satisfies_kdv
#print axioms KdV.ConservedSolution.massRate_conserved
#print axioms KdV.ConservedSolution.energyRate_conserved
' | lake env lean --stdin
```

The principal theorems depend only on Lean's standard foundational axioms:

```text
'KdV.travellingWave_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KdV.soliton_satisfies_kdv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KdV.ConservedSolution.massRate_conserved' depends on axioms: [propext, Classical.choice, Quot.sound]
'KdV.ConservedSolution.energyRate_conserved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No additional mathematical axiom is introduced by the package.

---

## IX. Scholium

This package has two independent mathematical cores.

The first core is the travelling-wave reduction and the exact soliton
calculation.  It turns the PDE into a one-variable identity and checks the
classical squared-sech profile by kernel-checked differentiation.

The second core is conservation.  It isolates the compact-support hypotheses
needed to integrate total derivatives to zero, then derives the rate forms of
mass and quadratic energy conservation from the KdV equation.

The live file is intentionally not the publication architecture.  The
publication architecture is modular.  The live file is the study certificate:
one coherent mathematical narrative, one Lean source, one place to audit the
whole argument.

---

## X. Verification

The live file and the modular package are checked with:

```text
lake env lean KdV/KdVLive/KdV.live.lean
lake build KdV
```
