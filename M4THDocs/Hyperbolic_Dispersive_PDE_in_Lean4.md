# Hyperbolic and Dispersive 1D PDE in Lean 4

## Weak Solutions, Shock Waves, the Lax Entropy Condition, Gradient Blow-up and Solitons

**Author.** Bezalel Izquierdo Pérez — ORCID [0009-0001-5993-4057](https://orcid.org/0009-0001-5993-4057)
**Code.** <https://github.com/Alektronnik/M4TH> — packages `ConservationLaws`, `BurgersBlowUp`, `KdV`
**License.** Apache 2.0 (software), CC-BY 4.0 (text)
**Verification.** Lean 4 over Mathlib. Zero `axiom`, zero `sorry`. Every displayed theorem carries a clean axiom certificate (`[propext, Classical.choice, Quot.sound]`).

---

## Abstract

We report a self-contained formalisation, in the Lean 4 proof assistant on top of
Mathlib, of the elementary theory of one-dimensional evolutionary partial
differential equations of hyperbolic and dispersive type. Three results anchor
the development. First, for the scalar conservation law `∂ₜu + ∂ₓ(f(u)) = 0`
with an *arbitrary* flux, we prove that the distributional residual of a
travelling step against any smooth compactly supported test function reduces
*exactly* to the boundary integral of the Rankine–Hugoniot deficit along the
moving interface; as a corollary the step is a weak solution if and only if its
speed satisfies Rankine–Hugoniot. For the Burgers flux we formalise the Lax
entropy pair, the entropy-dissipation identity, and the classical
non-uniqueness pathology (a genuine weak solution that violates the entropy
condition). Second, for the inviscid Burgers equation we prove finite-time
gradient blow-up for a compressive datum, by an exact solution of the Riccati
equation governing the gradient along characteristics, with a purely algebraic
final contradiction. Third, for the Korteweg–de Vries equation we verify that the
classical squared-hyperbolic-secant profile is an exact travelling-wave solution
and that mass and quadratic energy are conserved for compactly supported
solutions. To our knowledge this is the first formalisation of weak solutions of
conservation laws, of the Rankine–Hugoniot and Lax entropy conditions, of
gradient blow-up for a nonlinear PDE, and of the KdV soliton, in any major proof
assistant. The material is organised as three independent packages, each split
into a linear series of self-contained modules designed for incremental
contribution to Mathlib.

---

## 1. Introduction

The formal verification of analysis has advanced rapidly, but the theory of
partial differential equations has remained almost entirely outside the reach of
proof assistants. The recent formalisation of the De Giorgi–Nash–Moser theorem
(2026) is, to our knowledge, the first non-trivial regularity result for PDE in
Lean; its own authors note the prior view that non-trivial statements about
solutions of PDE were not formalisable. That result concerns *elliptic*
regularity. The complementary world — *evolutionary* equations, and in
particular the hyperbolic and dispersive phenomena of shock formation, entropy
selection, finite-time singularities, and solitary waves — has, as far as we have
been able to determine, no counterpart in any major library.

This paper occupies that territory with elementary but foundational material. We
deliberately restrict to one spatial dimension and to the most classical model
problems, because our aim is not maximal generality but the establishment of a
*verified vocabulary*: the definitions of weak solution, Rankine–Hugoniot speed,
entropy pair, characteristic, and travelling wave, together with the theorems that
make these definitions non-vacuous. Each definition is chosen to be the one a
subsequent Mathlib development would want to build on, and each is accompanied by
at least one concrete instance in which the corresponding phenomenon is exhibited
in full.

Three theorems organise the development.

1. **Exact shock reduction** (Section 3). For the scalar conservation law with
   arbitrary flux `f`, the distributional residual of the travelling step
   `shockProfile uL uR s` collapses exactly to the Rankine–Hugoniot deficit
   integrated along the interface. This is an equality, not an estimate, and it
   holds for every admissible test function; the Rankine–Hugoniot condition is
   recovered as the precise vanishing criterion.

2. **Gradient blow-up** (Section 5). For the inviscid Burgers equation with the
   compressive ramp datum `u₀(x) = -x`, no `C²` solution survives to time `1`.
   The proof tracks the spatial gradient along characteristics, where it solves
   the Riccati equation `V' = -V²` with `V(0) = -1`, whose exact solution
   `V(t) = -1/(1 - t)` diverges at `t = 1`; the contradiction with any putative
   gradient bound is algebraic and uses no limiting argument.

3. **The KdV soliton** (Section 6). The profile `3c·sech²((√c/2)·ξ)` is an exact
   travelling-wave solution of `uₜ + u uₓ + uₓₓₓ = 0` for every wave speed
   `c > 0`, and mass and quadratic energy are conserved for compactly supported
   solutions.

All three are verified with no axioms beyond the foundations of Lean and Mathlib
and with no incomplete proofs. The development is partitioned into three packages
that share no code and depend only on Mathlib, so that each can be reviewed,
built, and upstreamed independently.

### 1.1 Contributions

- The first formalisation of weak (distributional) solutions of scalar
  conservation laws, for arbitrary flux, with a measure-theoretic residual over
  the open space–time cylinder.
- An *exact* reduction of the weak residual of a travelling discontinuity to the
  Rankine–Hugoniot deficit, and the equivalence "weak solution ⇔ Rankine–Hugoniot".
- The Lax entropy pair for the Burgers flux, the closed-form entropy-dissipation
  identity, and a formal witness of non-uniqueness: an expansion step that is a
  weak solution but is not entropy-admissible.
- The first formalisation of finite-time gradient blow-up for a nonlinear PDE,
  via an exact Riccati solution and a Lyapunov-energy uniqueness lemma for the
  characteristic ODE.
- The first formalisation of the KdV one-soliton and of its mass and energy
  conservation laws.

### 1.2 Non-goals

We do not construct global weak solutions, prove existence via vanishing
viscosity or front tracking, treat systems or several space dimensions, or
establish uniqueness in an entropy class. These are the natural next steps; the
present work supplies the definitions and the first theorems on which they would
rest. Where a result is special to the Burgers flux (the entropy pair, the ramp
blow-up) we mark it as such, and we keep the general-flux theory strictly
separate from the Burgers instance.

---

## 2. Setting and Mathlib background

All three packages are stated over the reals and use only core Mathlib analysis:
`ContDiff` and `HasCompactSupport` for smoothness and support, `deriv` and
`fderiv` for differentiation, `MeasureTheory` for the space–time integral, and
the ODE uniqueness and Grönwall infrastructure of `Mathlib/Analysis/ODE`. No
differential-geometric machinery is required: in one space dimension the objects
are ordinary functions `ℝ → ℝ → ℝ` of time and space, and the analytical content
is carried by elementary calculus, the fundamental theorem of calculus in its
improper form, and Fubini's theorem.

The space–time domain is the open cylinder

```lean
def spacetimeDomain (T : ℝ) : Set (ℝ × ℝ) := Set.Ioo 0 T ×ˢ Set.univ
```

and test functions are smooth, compactly supported, and supported inside it.

---

## 3. Weak solutions of scalar conservation laws

### 3.1 Test functions and the weak residual

A test function on the cylinder `(0,T) × ℝ` is packaged as a structure carrying
its own smoothness and support proofs.

```lean
structure TestFunction (T : ℝ) where
  toFun : ℝ → ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => toFun p.1 p.2)
  compactSupport : HasCompactSupport (fun p : ℝ × ℝ => toFun p.1 p.2)
  support_subset : tsupport (fun p : ℝ × ℝ => toFun p.1 p.2) ⊆ spacetimeDomain T
```

Writing `φ.dt` and `φ.dx` for the partial derivatives of the test function, the
weak formulation of `∂ₜu + ∂ₓ(f(u)) = 0` transfers all derivatives onto `φ`:

```lean
noncomputable def weakIntegrand (f : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (φ : TestFunction T) (t x : ℝ) : ℝ :=
  u t x * φ.dt t x + f (u t x) * φ.dx t x

noncomputable def weakResidual (f : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (φ : TestFunction T) : ℝ :=
  ∫ t in Ioo 0 T, ∫ x : ℝ, weakIntegrand f u φ t x
```

A function is a weak solution when it is locally integrable together with its
flux and its residual vanishes against every test function (`IsWeakSolution`).
Because the support of `φ` is compact and interior to the cylinder, the inner
spatial integral is over a bounded interval and all integrals are finite.

### 3.2 The travelling step and Rankine–Hugoniot

The elementary discontinuous profile is the travelling step, together with the
Rankine–Hugoniot speed condition.

```lean
noncomputable def shockProfile (uL uR s : ℝ) (t x : ℝ) : ℝ :=
  if x < s * t then uL else uR

def RankineHugoniot (f : ℝ → ℝ) (uL uR s : ℝ) : Prop :=
  s * (uL - uR) = f uL - f uR
```

### 3.3 The exact shock reduction

The central theorem of the package evaluates the weak residual of the step in
closed form. After a Galilean change of frame that straightens the interface and
an application of Fubini and the improper fundamental theorem of calculus, every
contribution away from the interface cancels and only the jump survives.

```lean
theorem ConservationLaw.hasShockIntegralReduction (f : ℝ → ℝ) (T uL uR s : ℝ) :
    ∀ φ : TestFunction T,
      weakResidual f (shockProfile uL uR s) φ =
        ∫ t in Ioo 0 T, ((f uL - f uR) - s * (uL - uR)) * φ t (s * t)
```

The integrand is the Rankine–Hugoniot deficit `(f uL - f uR) - s(uL - uR)`
weighted by the trace of the test function along the interface `x = s t`. Two
corollaries follow immediately: if the speed satisfies Rankine–Hugoniot the
deficit is zero and the residual vanishes, so the step is a weak solution; and,
conversely, a step that is a weak solution must satisfy Rankine–Hugoniot.

```lean
theorem ConservationLaw.isWeakSolution_shockProfile_of_rankineHugoniot
    {f : ℝ → ℝ} (h : RankineHugoniot f uL uR s) :
    IsWeakSolution f T (shockProfile uL uR s)
```

We emphasise that these statements hold for an *arbitrary* flux `f : ℝ → ℝ`; no
convexity or smoothness of `f` is used for the reduction itself.

---

## 4. Entropy theory for the Burgers flux

Rankine–Hugoniot alone does not select physical shocks: the step admits weak
solutions in both compressive and expansive configurations. The entropy
condition removes the non-physical ones. We formalise the Lax theory for the
Burgers flux `f(u) = u²/2` with the standard convex entropy pair.

```lean
noncomputable def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2
noncomputable def entropy     (u : ℝ) : ℝ := u ^ 2 / 2
noncomputable def entropyFlux (u : ℝ) : ℝ := u ^ 3 / 6

noncomputable def entropyDissipation (uL uR s : ℝ) : ℝ :=
  s * (entropy uR - entropy uL) + entropyFlux uL - entropyFlux uR
```

At the Rankine–Hugoniot speed the dissipation has a closed form whose sign is
governed by the ordering of the states, which is exactly the Lax condition. The
package makes the resulting non-uniqueness explicit: the midpoint expansion step
is a genuine weak solution of the Burgers equation that nonetheless violates the
Lax condition and dissipates entropy of the wrong sign.

```lean
theorem ConservationLaw.expansion_midpoint_is_weak_but_not_entropic
    (T uL uR : ℝ) (h : uL < uR) : ...
```

This is the formal counterpart of the standard textbook observation that weak
solutions of conservation laws are not unique and that an admissibility criterion
is indispensable. Keeping this pathology inside the verified corpus — rather than
in prose — fixes precisely what the entropy condition is needed for.

---

## 5. Gradient blow-up for the inviscid Burgers equation

### 5.1 Regular solutions and the compressive datum

A regular solution is a `C²` function satisfying `∂ₜu + u ∂ₓu = 0` pointwise; the
initial datum is the compressive ramp.

```lean
def initialRamp : ℝ → ℝ := fun x => -x
```

### 5.2 Characteristics, the Riccati gradient, and blow-up

Along each characteristic `t ↦ x₀(1 - t)` the solution is constant, proved
through a Lyapunov-energy uniqueness lemma for the underlying linear ODE
(`constant_along_characteristic`). Differentiating the equation in space, the
gradient `V(t) = uₓ(t, x₀(1 - t))` satisfies a Riccati equation with a compressive
initial value, whose exact solution is explicit.

```lean
-- V' = -V^2 with V 0 = -1
theorem Burgers.gradient_riccati_evolution ...
-- V t = -1 / (1 - t)
theorem Burgers.gradient_eq_neg_one_div ...
```

The exact formula diverges as `t → 1⁻`, but the final argument avoids limits
entirely: given any putative gradient bound `M`, at the critical time
`t = 1 - 1/(|M| + 1)` the formula yields a gradient of magnitude `|M| + 1 > M`, a
direct algebraic contradiction. Hence no regular solution reaches time `1`.

```lean
theorem Burgers.not_isRegularSolution_initialRamp {T : ℝ} (hT : 1 ≤ T)
    (u : ℝ → ℝ → ℝ) : ¬ IsRegularSolution initialRamp T u
```

This is, to our knowledge, the first machine-checked theorem of finite-time
singularity formation for a nonlinear evolution equation. It is the exact
counterpoint to elliptic regularity: where De Giorgi–Nash–Moser produces
smoothness, the method of characteristics here produces its destruction, and the
mechanism — a Riccati blow-up of the gradient — is displayed in closed form.

---

## 6. The KdV soliton and conservation laws

For the normalisation `uₜ + u uₓ + uₓₓₓ = 0`, the travelling-wave ansatz
`u(t,x) = f(x - c t)` reduces the PDE to the stationary soliton ODE
`-c f' + f f' + f''' = 0` (`travellingWave_reduction`). The package develops the
hyperbolic-secant calculus (`sech`, the identity `sech² = 1 - tanh²`, and the
derivatives of the relevant composites) and verifies the exact profile.

```lean
theorem KdV.soliton_satisfies_kdv (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    -c * deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) ξ +
      (3 * c * sech (Real.sqrt c / 2 * ξ) ^ 2) *
        deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) ξ +
      deriv (fun y => deriv (fun z =>
        deriv (fun x => 3 * c * sech (Real.sqrt c / 2 * x) ^ 2) z) y) ξ = 0
```

For compactly supported smooth solutions the package proves the rate forms of the
first two conservation laws — mass and quadratic energy —

```lean
theorem KdV.ConservedSolution.massRate_conserved   -- ∫ uₜ = 0
theorem KdV.ConservedSolution.energyRate_conserved -- ∫ u uₜ = 0
```

obtained from the integral identities `∫ uᵏ uₓ = 0` and the double integration by
parts `∫ u uₓₓₓ = 0` for compactly supported integrands. The soliton and the
conservation laws together give the smallest non-trivial verified fragment of
integrable-systems theory.

---

## 7. Formalisation notes

**Generality of the flux.** The weak-solution API and the shock reduction are
stated for an arbitrary `f : ℝ → ℝ`. Convexity enters only in Section 4, and only
to obtain the sign of the entropy dissipation; the Burgers-specific results live
in a single module (`Burgers.lean`) and never contaminate the general theory.

**Measure-theoretic choices.** The residual integrates over the open cylinder
with the ambient volume on `ℝ × ℝ`; test functions have compact support interior
to the cylinder, so no boundary terms arise and all integrals are over bounded
sets after restricting to the support. Local integrability of the solution and of
its flux is part of the definition of a weak solution.

**No axioms, no `sorry`, no `native_decide`.** Every result is kernel-checked.
The numerical witnesses in the Burgers and KdV packages are proved by `norm_num`
and explicit finite reductions rather than by trusted compiled evaluation, so the
axiom certificate of each headline theorem is exactly
`[propext, Classical.choice, Quot.sound]`.

**Independence and PR partition.** The three packages share no code and depend
only on Mathlib; the four calculus helpers common to `ConservationLaws` and
`BurgersBlowUp` are duplicated deliberately so that each package is
self-contained, and would be contributed once, in their most general form, at PR
time. Within each package the modules form a linear chain, and the intended
Mathlib PR series follows that chain, each PR self-contained and useful on its own
(definitions and the null solution; test-function calculus; the Galilean frame
and Fubini cancellations; the shock profile and Rankine–Hugoniot; the exact
reduction; the entropy theory). The KdV special-function lemmas (`sech` and its
derivatives) are split off first, as they belong in
`Analysis/SpecialFunctions` independently of the PDE.

---

## 8. Related work

The formalisation of De Giorgi–Nash–Moser (2026) established elliptic regularity
in Lean and is the closest precedent for non-trivial PDE in a proof assistant;
the present work is complementary, addressing evolutionary hyperbolic and
dispersive equations. Mathlib already provides the ODE uniqueness and Grönwall
inequalities used in Section 5, the smoothness and compact-support API used
throughout, and the measure theory underlying the residual. Classical references
for the mathematics formalised here are Lax's theory of hyperbolic conservation
laws and the shock admissibility conditions [2], the method of characteristics for
Burgers' equation, and the inverse-scattering theory of KdV [4]; we formalise only
the elementary, self-contained fragments of each.

---

## 9. Availability

The three packages are available at <https://github.com/Alektronnik/M4TH> under
the Apache 2.0 license, each with its own `lakefile.toml` (pinned to Mathlib `fabf563a`, Lean 4 v4.31.0) and a native Lean-generated SVG cover figure.
Each package also includes a `Live` single-file study version. After a successful build the axiom certificate
of each headline theorem may be reproduced with

```
#print axioms ConservationLaw.hasShockIntegralReduction
#print axioms Burgers.not_isRegularSolution_initialRamp
#print axioms KdV.soliton_satisfies_kdv
```

each returning `[propext, Classical.choice, Quot.sound]`.

---

## References

1. S. Armstrong et al., *A formalisation of the De Giorgi–Nash–Moser theorem in
   Lean* (2026).
2. P. D. Lax, *Hyperbolic Systems of Conservation Laws II*, Comm. Pure Appl.
   Math. 10 (1957), 537–566.
3. C. M. Dafermos, *Hyperbolic Conservation Laws in Continuum Physics*, Springer,
   4th ed., 2016.
4. G. B. Whitham, *Linear and Nonlinear Waves*, Wiley, 1974.
5. The mathlib Community, *The Lean Mathematical Library*, CPP 2020;
   <https://github.com/leanprover-community/mathlib4>.
