# BurgersBlowUp

**A single-file live presentation of finite-time gradient blow-up for the
inviscid Burgers equation, formalised in Lean 4 over Mathlib.**

- Author: Bezalel Izquierdo Pérez
- ORCID: https://orcid.org/0009-0001-5993-4057
- Repository: https://github.com/Alektronnik/M4TH
- License: Apache 2.0
- Companion file: `BurgersBlowUp.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`BurgersBlowUp.live.lean`.  It presents the mathematical content in a classical
theorem-style format: first the analytic idea, then the corresponding Lean
statement.  Proof scripts are intentionally omitted here; the live Lean file is
the certificate.

---

## I. The Mathematical Problem

The inviscid Burgers equation is

$$
\partial_t u + u\,\partial_x u = 0.
$$

It is the simplest nonlinear transport equation in which smooth data can create
a singularity in finite time.  The characteristic speed is the solution itself:
points with larger \(u\) move faster, points with smaller \(u\) move slower, and
compressive initial data cause characteristics to collide.

This package treats the compressive ramp

$$
u_0(x)=-x.
$$

For this datum, the characteristic through \(x_0\) is the straight line

$$
x(t)=x_0(1-t).
$$

Along this line, the solution remains constant:

$$
u(t,x_0(1-t))=-x_0.
$$

The spatial gradient along the same characteristic satisfies the Riccati
equation

$$
V'(t)=-V(t)^2,
\qquad
V(0)=-1,
$$

whose exact solution is

$$
V(t)=-\frac{1}{1-t}.
$$

As \(t\) approaches \(1\), this gradient becomes unbounded.  The formal theorem
does not use a limiting argument.  Instead, it evaluates the exact formula at

$$
t=1-\frac{1}{|M|+1},
$$

where \(M\) is a hypothetical global gradient bound, and obtains a gradient of
magnitude \(|M|+1\), contradicting the bound.


The geometric mechanism is:

```text
        x
        ^
        |
   x0   *\
        | \
        |  \
        |   \
        |    *  collision at t = 1
        |
--------+---------------------> t
        0          1
```

---

## II. Calculus Along Curves

The method of characteristics requires a clean chain rule for functions of two
real variables evaluated along curves in the plane.

> **Theorem 1. Derivative into the product.**
>
> If two real-valued functions are differentiable, then the curve formed by
> pairing them is differentiable into \(\mathbb{R}\times\mathbb{R}\).
>
> **In Lean:**
>
> ```lean
> lemma Burgers.hasDerivAt_prodMk
>     {f : ℝ → ℝ} {g : ℝ → ℝ} {f' g' : ℝ} {s : ℝ}
>     (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
>     HasDerivAt (fun t => (f t, g t)) (f', g') s
> ```

> **Theorem 2. Coordinate recovery from the Fréchet derivative.**
>
> Evaluating the Fréchet derivative at \((1,0)\) and \((0,1)\) recovers the
> time and space partial derivatives.
>
> **In Lean:**
>
> ```lean
> lemma Burgers.fderiv_coord_fst (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
>     (h_diff : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) p) :
>     fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) p (1, 0) =
>       deriv (fun t => u t p.2) p.1
> ```
>
> ```lean
> lemma Burgers.fderiv_coord_snd (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
>     (h_diff : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) p) :
>     fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) p (0, 1) =
>       deriv (u p.1) p.2
> ```

> **Theorem 3. Linear decomposition of the Fréchet derivative.**
>
> For a direction \(dp=(dp_1,dp_2)\),
>
> $$
> D u(p)\,dp
> =
> dp_1\,\partial_t u(p)+dp_2\,\partial_x u(p).
> $$
>
> **In Lean:**
>
> ```lean
> lemma Burgers.fderiv_apply_decomp
>     (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (dp : ℝ × ℝ)
>     (h_diff : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) p) :
>     fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) p dp =
>       dp.1 * deriv (fun t => u t p.2) p.1 +
>         dp.2 * deriv (u p.1) p.2
> ```

> **Theorem 4. Chain rule along a plane curve.**
>
> If \(\gamma\) is a differentiable curve in the plane, then the derivative of
> \(u(\gamma(t))\) is the partial-derivative pairing with the velocity
> \(\gamma'(t)\).
>
> **In Lean:**
>
> ```lean
> lemma Burgers.hasDerivAt_comp_curve
>     (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) (s : ℝ) (dγ : ℝ × ℝ)
>     (h_deriv_γ : HasDerivAt γ dγ s)
>     (h_diff : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (γ s)) :
>     HasDerivAt (fun t => u (γ t).1 (γ t).2)
>       (dγ.1 * deriv (fun t' => u t' (γ s).2) (γ s).1 +
>         dγ.2 * deriv (u (γ s).1) (γ s).2) s
> ```

---

## III. ODE Ingredients

The analytic core of the development is an ODE uniqueness argument and an exact
solution of the Riccati equation.

> **Theorem 5. Linear ODE uniqueness.**
>
> If \(Y(0)=0\) and
>
> $$
> Y'(s)=-Y(s)f(s)
> $$
>
> on \([0,T)\), with \(f\) bounded, then \(Y\) vanishes on \([0,T]\).  The
> proof uses the Lyapunov energy
>
> $$
> W(s)=Y(s)^2\exp(-2Ms).
> $$
>
> **In Lean:**
>
> ```lean
> lemma Burgers.linear_ode_uniqueness
>     (Y : ℝ → ℝ) (f : ℝ → ℝ) (T : ℝ) (M : ℝ)
>     (hY_cont : ContinuousOn Y (Set.Icc 0 T))
>     (h_bound : ∀ s ∈ Set.Icc 0 T, |f s| ≤ M)
>     (h_zero : Y 0 = 0)
>     (h_deriv : ∀ s ∈ Set.Ico 0 T, HasDerivAt Y (- Y s * f s) s) :
>     ∀ t ∈ Set.Icc 0 T, Y t = 0
> ```

> **Theorem 6. Exact Riccati solution.**
>
> The Riccati equation
>
> $$
> V'(t)=-V(t)^2,\qquad V(0)=-1
> $$
>
> has the exact solution
>
> $$
> V(t)=-\frac{1}{1-t}
> $$
>
> for \(t\leq T<1\).
>
> **In Lean:**
>
> ```lean
> lemma Burgers.riccati_ode_solution
>     (V : ℝ → ℝ) (T : ℝ) (hT : T < 1)
>     (hV_cont : ContinuousOn V (Set.Icc 0 T))
>     (h_zero : V 0 = -1)
>     (h_deriv : ∀ s ∈ Set.Ico 0 T, HasDerivAt V (- (V s) ^ 2) s) :
>     ∀ t ∈ Set.Icc 0 T, V t = -1 / (1 - t)
> ```

---

## IV. Regular Solutions and Characteristics

The package works with a deliberately strong classical solution concept.  This
is the right setting for a blow-up theorem: the conclusion says that such a
regular solution cannot exist past the critical time.

> **Definition 1. Regular solution.**
>
> A regular solution satisfies the initial condition, joint differentiability,
> the Burgers PDE on \([0,T)\), enough differentiability to differentiate the
> equation in space, a Schwarz condition for mixed derivatives, and a global
> gradient bound.
>
> **In Lean:**
>
> ```lean
> structure Burgers.IsRegularSolution
>     (u₀ : ℝ → ℝ) (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop where
>   initial : ∀ x, u 0 x = u₀ x
>   differentiable : Differentiable ℝ (fun p : ℝ × ℝ => u p.1 p.2)
>   pde : ∀ t ∈ Set.Ico 0 T, ∀ x,
>     deriv (fun s => u s x) t + u t x * deriv (u t) x = 0
>   gradient_differentiable_slice : ∀ t ∈ Set.Icc 0 T,
>     Differentiable ℝ (fun x => deriv (u t) x)
>   schwarz : ∀ t ∈ Set.Ico 0 T, ∀ x,
>     deriv (fun t' => deriv (u t') x) t =
>       deriv (fun x' => deriv (fun s => u s x') t) x
>   gradient_differentiable :
>     Differentiable ℝ (fun p' : ℝ × ℝ => deriv (u p'.1) p'.2)
>   gradient_bounded :
>     ∃ M : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x, |deriv (u t) x| ≤ M
> ```

> **Definition 2. The compressive ramp.**
>
> **In Lean:**
>
> ```lean
> def Burgers.initialRamp (x : ℝ) : ℝ := -x
> ```

> **Theorem 7. Evolution along the characteristic line.**
>
> Along the line \(t\mapsto x_0(1-t)\), the quantity
>
> $$
> Y(t)=u(t,x_0(1-t))+x_0
> $$
>
> satisfies a linear ODE.
>
> **In Lean:**
>
> ```lean
> lemma Burgers.hasDerivAt_along_line
>     {u₀ : ℝ → ℝ} {T : ℝ} {u : ℝ → ℝ → ℝ}
>     (hsol : IsRegularSolution u₀ T u) (x₀ : ℝ) :
>     ∀ s ∈ Set.Ico 0 T,
>       HasDerivAt (fun t => u t (x₀ * (1 - t)) + x₀)
>         (- (u s (x₀ * (1 - s)) + x₀) *
>           deriv (u s) (x₀ * (1 - s)))
>         s
> ```

> **Theorem 8. Constancy along characteristics.**
>
> For the ramp datum, the solution is constant along each characteristic:
>
> $$
> u(t,x_0(1-t))=-x_0.
> $$
>
> **In Lean:**
>
> ```lean
> lemma Burgers.constant_along_characteristic
>     {T : ℝ} {u : ℝ → ℝ → ℝ}
>     (hsol : IsRegularSolution initialRamp T u)
>     (x₀ : ℝ) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
>     u t (x₀ * (1 - t)) = -x₀
> ```

> **Theorem 9. Spatially differentiated Burgers equation.**
>
> Differentiating
>
> $$
> u_t+u u_x=0
> $$
>
> in \(x\) gives
>
> $$
> \partial_t u_x+(u_x)^2+u\,\partial_x u_x=0.
> $$
>
> **In Lean:**
>
> ```lean
> lemma Burgers.pde_spatial_deriv
>     {u₀ : ℝ → ℝ} {T : ℝ} {u : ℝ → ℝ → ℝ}
>     (hsol : IsRegularSolution u₀ T u)
>     (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : ℝ) :
>     deriv (fun x' => deriv (fun s => u s x') t) x +
>       (deriv (u t) x) ^ 2 +
>       u t x * deriv (fun x' => deriv (u t) x') x = 0
> ```

---

## V. Riccati Evolution of the Gradient

The blow-up mechanism is now forced.  Define the gradient along a characteristic
by

$$
V(t)=u_x(t,x_0(1-t)).
$$

Using the spatially differentiated PDE, the Schwarz condition, and the
constancy of \(u\) along the characteristic, one obtains the Riccati equation.

> **Theorem 10. Riccati evolution of the gradient.**
>
> **In Lean:**
>
> ```lean
> lemma Burgers.gradient_riccati_evolution
>     {T : ℝ} {u : ℝ → ℝ → ℝ}
>     (hsol : IsRegularSolution initialRamp T u) (x₀ : ℝ) :
>     ∀ s ∈ Set.Ico 0 T,
>       HasDerivAt (fun t => deriv (u t) (x₀ * (1 - t)))
>         (- (deriv (u s) (x₀ * (1 - s))) ^ 2)
>         s
> ```

> **Theorem 11. Exact gradient formula.**
>
> Therefore
>
> $$
> u_x(t,x_0(1-t))=-\frac{1}{1-t}
> $$
>
> for every \(t<T\) with \(t<1\).
>
> **In Lean:**
>
> ```lean
> lemma Burgers.gradient_eq_neg_one_div
>     {T : ℝ} {u : ℝ → ℝ → ℝ}
>     (hsol : IsRegularSolution initialRamp T u)
>     (x₀ : ℝ) (t : ℝ) (ht : t ∈ Set.Ico 0 T) (ht_lt : t < 1) :
>     deriv (u t) (x₀ * (1 - t)) = -1 / (1 - t)
> ```

---

## VI. The Blow-Up Theorem

The theorem is stated negatively: once \(T\geq 1\), there is no regular solution
on \([0,T)\) with initial datum \(u_0(x)=-x\).

The contradiction is finite and algebraic.  If a regular solution existed, its
definition would provide

$$
|u_x(t,x)|\leq M
$$

on the whole cylinder.  Evaluating the exact formula at

$$
t=1-\frac{1}{|M|+1},
\qquad
x_0=0,
$$

gives

$$
|u_x(t,0)|=|M|+1,
$$

which is strictly larger than any possible bound \(M\).

> **Theorem 12. Finite-time gradient blow-up.**
>
> **In Lean:**
>
> ```lean
> theorem Burgers.not_isRegularSolution_initialRamp
>     {T : ℝ} (hT : 1 ≤ T) (u : ℝ → ℝ → ℝ) :
>     ¬ IsRegularSolution initialRamp T u
> ```

> **Corollary. No regular solution exists on \([0,2)\).**
>
> **In Lean:**
>
> ```lean
> example : ¬ ∃ u : ℝ → ℝ → ℝ, IsRegularSolution initialRamp 2 u
> ```

---

## VII. Scholium

The package follows the classical characteristic proof, but it is arranged so
that each analytic ingredient is independently checkable.

The role of the calculus file is structural: it supplies the two-variable chain
rule needed to evaluate \(u\) and \(u_x\) along characteristic curves.

The role of the ODE file is dynamical: the Lyapunov-energy uniqueness lemma
turns a first-order linear ODE with zero initial value into an exact vanishing
statement, and the Riccati lemma converts \(V'=-V^2\) into the explicit
formula \(-1/(1-t)\).

The role of the characteristics file is geometric: it identifies the straight
characteristics of the ramp datum and proves that the solution remains constant
along them.

The role of the blow-up file is algebraic: rather than proving divergence by a
limit, it evaluates the exact gradient formula at a carefully chosen time and
contradicts the global gradient bound contained in the regular-solution
structure.

---

## VIII. Logical Certificate

This development contains no package-local axioms and no `sorry`.

The intended certificate commands are:

```lean
import BurgersBlowUp

#print axioms Burgers.linear_ode_uniqueness
#print axioms Burgers.riccati_ode_solution
#print axioms Burgers.gradient_eq_neg_one_div
#print axioms Burgers.not_isRegularSolution_initialRamp
```

The expected terminal output contains only the standard foundational axioms used
by Mathlib:

```text
'Burgers.linear_ode_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Burgers.riccati_ode_solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'Burgers.gradient_eq_neg_one_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'Burgers.not_isRegularSolution_initialRamp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Any additional package-local axiom would be a defect.

---

## IX. Live File

For web inspection and study, use:

```text
BurgersBlowUp.live.lean
```

That file is the fused single-file edition of the package in dependency order:

```text
Calculus
ODE
Characteristics
BlowUp
```

The manual explains the mathematical route.  The `.live.lean` file is the
machine-checkable certificate.


Reference paths:

- Live source: `BurgersBlowUp.live.lean`
- Package root: `BurgersBlowUp.lean`
- Source directory: `BurgersBlowUp/`

---

## X. Verification

The live file and the modular package are checked with:

```text
lake env lean BurgersBlowUp/BurgersBlowUpLive/BurgersBlowUp.live.lean
lake build BurgersBlowUp
```
