# ConservationLaws.live

**A single-file live presentation of weak solutions, travelling shocks, and
entropy admissibility for one-dimensional scalar conservation laws, formalised
in Lean 4 over Mathlib.**

\*\*Author:\*\* Bezalel Izquierdo Pérez
\*\*License:\*\* Apache 2.0
\*\*Live file:\*\* `ConservationLaws.live.lean`

This manual is designed for Zulip, web reading, and mathematical study alongside
`ConservationLaws.live.lean`.  It presents the mathematical content in a
classical theorem-style format: first the analytic idea, then the corresponding
Lean statement.  Proof scripts are intentionally omitted here; the live Lean
file is the certificate.

---

## I. The Mathematical Problem

A one-dimensional scalar conservation law has the form

$$
\partial_t u + \partial_x f(u) = 0
$$

on a space-time cylinder

$$
(0,T)\times\mathbb{R}.
$$

Classical differentiability is too restrictive for discontinuous phenomena such
as shocks.  The physically relevant solutions are often only locally integrable,
and the equation is interpreted distributionally: the solution is tested against
smooth compactly supported functions.

The weak formulation is

$$
\int_0^T\int_{\mathbb{R}}
\left(u\,\partial_t\varphi + f(u)\,\partial_x\varphi\right)\,dx\,dt = 0
$$

for every test function \(\varphi\) supported inside the open cylinder.

The central object of the package is the travelling shock profile

$$
u(t,x)=
\begin{cases}
u_L & \text{if } x < st,\\
u_R & \text{if } x \geq st.
\end{cases}
$$

and the Rankine--Hugoniot jump condition

$$
s(u_L-u_R)=f(u_L)-f(u_R).
$$

For the Burgers flux

$$
f(u)=\frac{u^2}{2},
$$

the Rankine--Hugoniot speed is the arithmetic mean

$$
s=\frac{u_L+u_R}{2}.
$$

The package formalises the weak-solution infrastructure, proves the exact shock
residual reduction, and then separates admissible compression shocks from
inadmissible expansion shocks through the Lax and entropy criteria.


The basic geometry is:

```text
            x
            ^
            |
      u_L   |    x < st
            |
------------+---------------------> t
             \
              \
               \  x = st
                \
      u_R        \    x >= st
```

---

## II. Test Functions and the Weak Formulation

> **Definition 1. The space-time cylinder.**
>
> The domain of the problem is the open cylinder
>
> $$
> (0,T)\times\mathbb{R}.
> $$
>
> **In Lean:**
>
> ```lean
> def ConservationLaw.spacetimeDomain (T : ℝ) : Set (ℝ × ℝ) :=
>   Ioo 0 T ×ˢ (univ : Set ℝ)
> ```

> **Definition 2. Test functions.**
>
> A test function is jointly smooth, compactly supported, and has topological
> support contained in the open cylinder.  This support condition removes all
> boundary terms at \(t=0\), \(t=T\), and spatial infinity.
>
> **In Lean:**
>
> ```lean
> structure ConservationLaw.TestFunction (T : ℝ) where
>   toFun : ℝ → ℝ → ℝ
>   smooth : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => toFun p.1 p.2)
>   compactSupport : HasCompactSupport (fun p : ℝ × ℝ => toFun p.1 p.2)
>   support_subset :
>     tsupport (fun p : ℝ × ℝ => toFun p.1 p.2) ⊆ spacetimeDomain T
> ```

> **Definition 3. Partial derivatives of a test function.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ConservationLaw.TestFunction.dt
>     {T : ℝ} (φ : TestFunction T) (t x : ℝ) : ℝ :=
>   deriv (fun s => φ s x) t
> ```
>
> ```lean
> noncomputable def ConservationLaw.TestFunction.dx
>     {T : ℝ} (φ : TestFunction T) (t x : ℝ) : ℝ :=
>   deriv (φ t) x
> ```

> **Theorem 1. Spatial integration by parts on half-lines.**
>
> Compact support lets the improper boundary term at infinity vanish:
>
> $$
> \int_{-\infty}^{b}\partial_x\varphi(t,x)\,dx=\varphi(t,b),
> $$
>
> and
>
> $$
> \int_{b}^{\infty}\partial_x\varphi(t,x)\,dx=-\varphi(t,b).
> $$
>
> **In Lean:**
>
> ```lean
> lemma ConservationLaw.TestFunction.integral_Iic_dx
>     {T : ℝ} (φ : TestFunction T) (t b : ℝ) :
>     (∫ x in Iic b, φ.dx t x) = φ t b
> ```
>
> ```lean
> lemma ConservationLaw.TestFunction.integral_Ioi_dx
>     {T : ℝ} (φ : TestFunction T) (t b : ℝ) :
>     (∫ x in Ioi b, φ.dx t x) = -φ t b
> ```

> **Definition 4. The weak integrand and residual.**
>
> The weak residual is the distributional left-hand side of the conservation
> law tested against \(\varphi\).
>
> **In Lean:**
>
> ```lean
> noncomputable def ConservationLaw.weakIntegrand
>     (f : ℝ → ℝ) {T : ℝ} (u : ℝ → ℝ → ℝ)
>     (φ : TestFunction T) (t x : ℝ) : ℝ :=
>   u t x * φ.dt t x + f (u t x) * φ.dx t x
> ```
>
> ```lean
> noncomputable def ConservationLaw.weakResidual
>     (f : ℝ → ℝ) {T : ℝ} (u : ℝ → ℝ → ℝ)
>     (φ : TestFunction T) : ℝ :=
>   ∫ t in Ioo 0 T, ∫ x : ℝ, weakIntegrand f u φ t x
> ```

> **Definition 5. Weak solutions.**
>
> A weak solution has the minimal local integrability required for the flux and
> satisfies the weak residual identity for every test function.
>
> **In Lean:**
>
> ```lean
> structure ConservationLaw.IsWeakSolution
>     (f : ℝ → ℝ) (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop where
>   locallyIntegrable :
>     LocallyIntegrableOn (fun p : ℝ × ℝ => u p.1 p.2) (spacetimeDomain T)
>   fluxLocallyIntegrable :
>     LocallyIntegrableOn (fun p : ℝ × ℝ => f (u p.1 p.2)) (spacetimeDomain T)
>   weak_identity : ∀ φ : TestFunction T, weakResidual f u φ = 0
> ```

> **Theorem 2. The zero solution.**
>
> If the flux vanishes at the origin, the identically zero function is a weak
> solution.
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.isWeakSolution_zero
>     {f : ℝ → ℝ} (hf0 : f 0 = 0) (T : ℝ) :
>     IsWeakSolution f T (fun _ _ => 0)
> ```

---

## III. Galilean Reduction

The moving shock interface is \(x=st\).  To analyse the weak residual on each
side of that interface, the package uses the Galilean coordinate change

$$
x=\xi+st.
$$

Along this moving frame, the time derivative of a test function satisfies the
chain-rule identity

$$
\frac{d}{dt}\varphi(t,\xi+st)
=
\partial_t\varphi(t,\xi+st)+s\,\partial_x\varphi(t,\xi+st).
$$

> **Definition 6. Galilean transform of a test function.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ConservationLaw.TestFunction.galilean
>     {T : ℝ} (φ : TestFunction T) (s : ℝ) (t ξ : ℝ) : ℝ :=
>   φ t (ξ + s * t)
> ```

> **Theorem 3. Chain rule in the moving frame.**
>
> **In Lean:**
>
> ```lean
> lemma ConservationLaw.TestFunction.deriv_galilean_time
>     {T : ℝ} (φ : TestFunction T) (s t ξ : ℝ) :
>     deriv (fun τ => φ.galilean s τ ξ) t =
>       φ.dt t (ξ + s * t) + s * φ.dx t (ξ + s * t)
> ```

> **Theorem 4. Total time derivatives vanish on the cylinder.**
>
> Since test functions vanish at \(t=0\) and \(t=T\), the time integral of the
> Galilean total derivative over \((0,T)\) is zero.
>
> **In Lean:**
>
> ```lean
> lemma ConservationLaw.TestFunction.integral_Ioo_deriv_galilean_time
>     {T : ℝ} (φ : TestFunction T) (s ξ : ℝ) :
>     (∫ t in Ioo 0 T, deriv (fun τ => φ.galilean s τ ξ) t) = 0
> ```

These Galilean lemmas are the analytic engine used later to reduce the shock
residual to a single interface integral.

---

## IV. Travelling Shocks and Rankine--Hugoniot

> **Definition 7. Travelling shock profile.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ConservationLaw.shockProfile
>     (uL uR s : ℝ) (t x : ℝ) : ℝ :=
>   if x < s * t then uL else uR
> ```

> **Definition 8. Rankine--Hugoniot condition.**
>
> **In Lean:**
>
> ```lean
> def ConservationLaw.RankineHugoniot
>     (f : ℝ → ℝ) (uL uR s : ℝ) : Prop :=
>   s * (uL - uR) = f uL - f uR
> ```

> **Theorem 5. Local integrability of the shock.**
>
> The moving step profile is locally integrable, and so is its flux.
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.locallyIntegrableOn_shockProfile
>     (T uL uR s : ℝ) :
>     LocallyIntegrableOn
>       (fun p : ℝ × ℝ => shockProfile uL uR s p.1 p.2)
>       (spacetimeDomain T)
> ```
>
> ```lean
> theorem ConservationLaw.locallyIntegrableOn_comp_shockProfile
>     (f : ℝ → ℝ) (T uL uR s : ℝ) :
>     LocallyIntegrableOn
>       (fun p : ℝ × ℝ => f (shockProfile uL uR s p.1 p.2))
>       (spacetimeDomain T)
> ```

> **Definition 9. Exact shock residual reduction.**
>
> The analytic reduction states that the weak residual of a travelling step
> collapses to an integral over the moving interface:
>
> $$
> \int_0^T
> \left((f(u_L)-f(u_R))-s(u_L-u_R)\right)\varphi(t,st)\,dt.
> $$
>
> **In Lean:**
>
> ```lean
> def ConservationLaw.HasShockIntegralReduction
>     (f : ℝ → ℝ) (T uL uR s : ℝ) : Prop :=
>   ∀ φ : TestFunction T,
>     weakResidual f (shockProfile uL uR s) φ =
>       ∫ t in Ioo 0 T,
>         ((f uL - f uR) - s * (uL - uR)) * φ t (s * t)
> ```

> **Theorem 6. The reduction is proved.**
>
> The package proves the analytic reduction as a theorem, not as an axiom.
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.hasShockIntegralReduction
>     (f : ℝ → ℝ) (T uL uR s : ℝ) :
>     HasShockIntegralReduction f T uL uR s
> ```

> **Theorem 7. Rankine--Hugoniot makes the shock a weak solution.**
>
> If the Rankine--Hugoniot jump condition holds, the interface coefficient is
> zero, hence the travelling shock is a weak solution.
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.isWeakSolution_shockProfile_of_rankineHugoniot
>     {f : ℝ → ℝ} (T uL uR s : ℝ)
>     (hRH : RankineHugoniot f uL uR s) :
>     IsWeakSolution f T (shockProfile uL uR s)
> ```

---

## V. Compression, Expansion, and Physical Shocks

The weak formulation alone does not distinguish physically admissible shocks
from inadmissible ones.  The package therefore records the elementary
classification:

> **Definition 10. Compression and expansion shocks.**
>
> **In Lean:**
>
> ```lean
> def ConservationLaw.IsCompressionShock (uL uR : ℝ) : Prop :=
>   uL > uR
> ```
>
> ```lean
> def ConservationLaw.IsExpansionShock (uL uR : ℝ) : Prop :=
>   uL < uR
> ```

> **Definition 11. Physical shock.**
>
> A physical shock is a compression shock whose speed satisfies
> Rankine--Hugoniot.
>
> **In Lean:**
>
> ```lean
> structure ConservationLaw.PhysicalShock
>     (f : ℝ → ℝ) (uL uR s : ℝ) : Prop where
>   compression : IsCompressionShock uL uR
>   rankine : RankineHugoniot f uL uR s
> ```

> **Theorem 8. Physical shocks are weak solutions.**
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.isWeakSolution_of_physicalShock
>     {f : ℝ → ℝ} (T uL uR s : ℝ)
>     (hphys : PhysicalShock f uL uR s)
>     (hreduction : HasShockIntegralReduction f T uL uR s) :
>     IsWeakSolution f T (shockProfile uL uR s)
> ```

---

## VI. The Burgers Equation

The final part specialises the general conservation-law infrastructure to the
Burgers flux.

> **Definition 12. Burgers flux.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ConservationLaw.burgersFlux (u : ℝ) : ℝ :=
>   u ^ 2 / 2
> ```

> **Theorem 9. Rankine--Hugoniot speed for Burgers.**
>
> For the Burgers flux, the Rankine--Hugoniot speed is the midpoint of the left
> and right states.
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.rankineHugoniot_midpoint (uL uR : ℝ) :
>     RankineHugoniot burgersFlux uL uR ((uL + uR) / 2)
> ```

> **Theorem 10. Uniqueness of the Burgers shock speed.**
>
> If the left and right states differ, any Rankine--Hugoniot speed is the
> midpoint.
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.rankineHugoniot_speed_unique
>     {uL uR s : ℝ} (hne : uL ≠ uR)
>     (h : RankineHugoniot burgersFlux uL uR s) :
>     s = (uL + uR) / 2
> ```

> **Theorem 11. The midpoint shock is a weak solution.**
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.isWeakSolution_shockProfile_midpoint
>     (T uL uR : ℝ) :
>     IsWeakSolution burgersFlux T
>       (shockProfile uL uR ((uL + uR) / 2))
> ```

---

## VII. Lax and Oleinik Entropy Criteria

For Burgers, the characteristic speed is \(f'(u)=u\).  The Lax entropy condition
for a shock of speed \(s\) is therefore

$$
u_L > s > u_R.
$$

> **Definition 13. Lax entropy condition.**
>
> **In Lean:**
>
> ```lean
> def ConservationLaw.LaxEntropyCondition (uL uR s : ℝ) : Prop :=
>   uL > s ∧ s > uR
> ```

> **Theorem 12. Lax is equivalent to compression for Burgers shocks.**
>
> At Rankine--Hugoniot speed and with distinct states, the Lax condition is
> exactly the compression condition.
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.laxEntropy_iff_compression
>     {uL uR s : ℝ}
>     (hRH : RankineHugoniot burgersFlux uL uR s) (hne : uL ≠ uR) :
>     LaxEntropyCondition uL uR s ↔ IsCompressionShock uL uR
> ```

> **Theorem 13. Expansion shocks violate Lax.**
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.expansion_violates_lax
>     {uL uR : ℝ} (hexp : IsExpansionShock uL uR)
>     (_hRH : RankineHugoniot burgersFlux uL uR ((uL + uR) / 2)) :
>     ¬ LaxEntropyCondition uL uR ((uL + uR) / 2)
> ```

To isolate the physically admissible shocks, we introduce the classical Oleinik
entropy pair for the Burgers equation, consisting of the quadratic entropy and
its associated flux:

$$
\eta(u)=\frac{u^2}{2},
\qquad
q(u)=\frac{u^3}{6}.
$$

> **Definition 14. Entropy, entropy flux, and entropy dissipation.**
>
> **In Lean:**
>
> ```lean
> noncomputable def ConservationLaw.entropy (u : ℝ) : ℝ :=
>   u ^ 2 / 2
> ```
>
> ```lean
> noncomputable def ConservationLaw.entropyFlux (u : ℝ) : ℝ :=
>   u ^ 3 / 6
> ```
>
> ```lean
> noncomputable def ConservationLaw.entropyDissipation (uL uR s : ℝ) : ℝ :=
>   s * (entropy uR - entropy uL) + entropyFlux uL - entropyFlux uR
> ```

> **Theorem 14. Compression has the admissible entropy sign.**
>
> For nonnegative states, compression gives nonpositive entropy dissipation.
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.compression_entropy_dissipation_nonpos
>     {uL uR : ℝ}
>     (h0 : 0 ≤ uR) (hcomp : IsCompressionShock uL uR) :
>     entropyDissipation uL uR ((uL + uR) / 2) ≤ 0
> ```

> **Theorem 15. Expansion has the wrong entropy sign.**
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.expansion_entropy_dissipation_pos
>     {uL uR : ℝ}
>     (h0 : 0 ≤ uL) (hexp : IsExpansionShock uL uR) :
>     0 < entropyDissipation uL uR ((uL + uR) / 2)
> ```

---

## VIII. Main Packaged Statements

> **Theorem 16. Compression midpoint shocks are physical weak solutions.**
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.compression_midpoint_is_physical_weak_solution
>     (T uL uR : ℝ) (hcomp : IsCompressionShock uL uR) :
>     IsWeakSolution burgersFlux T
>       (shockProfile uL uR ((uL + uR) / 2))
> ```

> **Theorem 17. Compression midpoint shocks satisfy Lax.**
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.compression_midpoint_satisfies_lax
>     {uL uR : ℝ} (hcomp : IsCompressionShock uL uR) :
>     LaxEntropyCondition uL uR ((uL + uR) / 2)
> ```

> **Theorem 18. Expansion shocks exhibit weak non-uniqueness.**
>
> The expansion midpoint shock is a weak solution, but it violates Lax and has
> positive entropy dissipation.
>
> **In Lean:**
>
> ```lean
> theorem ConservationLaw.expansion_midpoint_is_weak_but_not_entropic
>     (T uL uR : ℝ)
>     (hexp : IsExpansionShock uL uR) (h0 : 0 ≤ uL) :
>     IsWeakSolution burgersFlux T
>       (shockProfile uL uR ((uL + uR) / 2)) ∧
>       ¬ LaxEntropyCondition uL uR ((uL + uR) / 2) ∧
>       0 < entropyDissipation uL uR ((uL + uR) / 2)
> ```

---

## IX. Scholium

The package isolates a precise route through the classical theory.

The role of `TestFunction` is functional-analytic: it gives enough smoothness
and compact support to justify integration by parts while keeping the solution
itself merely locally integrable.

The role of the Galilean section is geometric: the moving boundary \(x=st\) is
converted into a static boundary in the coordinate \(\xi=x-st\).  This is what
turns the shock residual into a pure interface term.

The role of `HasShockIntegralReduction` is structural: it records the exact
boundary reduction, and the package then proves it.  Once this reduction is
available, the Rankine--Hugoniot condition cancels the entire weak residual.

The Burgers section shows the limitation of weak solutions alone.  Both
compression and expansion midpoint shocks satisfy the weak equation, but only
compression satisfies Lax and has the admissible entropy sign.

---

## X. Axiom Certificate

This development contains no package-local axioms and no `sorry`.

The intended certificate commands are:

```lean
import ConservationLaws

#print axioms ConservationLaw.hasShockIntegralReduction
#print axioms ConservationLaw.isWeakSolution_shockProfile_of_rankineHugoniot
#print axioms ConservationLaw.laxEntropy_iff_compression
#print axioms ConservationLaw.expansion_midpoint_is_weak_but_not_entropic
```

The expected terminal output contains only the standard foundational axioms used
by Mathlib:

```text
'ConservationLaw.hasShockIntegralReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConservationLaw.isWeakSolution_shockProfile_of_rankineHugoniot' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConservationLaw.laxEntropy_iff_compression' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConservationLaw.expansion_midpoint_is_weak_but_not_entropic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Any additional package-local axiom would be a defect.

---

## XI. Live File

For web inspection and study, use:

```text
ConservationLaws.live.lean
```

That file is the fused single-file edition of the package in dependency order:

```text
TestFunction
WeakSolution
Galilean
ShockProfile
ShockReduction
Burgers
```

The manual explains the mathematical route.  The `.live.lean` file is the
machine-checkable certificate.


Reference paths:

- Live source: `ConservationLaws.live.lean`
- Package root: `ConservationLaws.lean`
- Source directory: `ConservationLaws/`

---

## XII. Verification

The live file and the modular package are checked with:

```text
lake env lean ConservationLaws/ConservationLawsLive/ConservationLaws.live.lean
lake build ConservationLaws
```
