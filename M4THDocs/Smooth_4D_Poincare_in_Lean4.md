# The Smooth 4D Poincaré Conjecture in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21646239.svg)](https://doi.org/10.5281/zenodo.21646239)

## Smooth Surgery Chains, Coupled Ricci–Gauge Flow, and a Conditional Diffeomorphism Theorem

**Author.** Bezalel Izquierdo Pérez — ORCID [0009-0001-5993-4057](https://orcid.org/0009-0001-5993-4057)
**Code.** <https://github.com/Alektronnik/M4TH> — package `Poincare4D` (release v6.0.0)
**License.** Apache 2.0 (software), CC-BY 4.0 (text)
**Verification.** Lean 4 over Mathlib (pinned `fabf563a`, v4.31.0). Zero `axiom`, zero `sorry`, zero `native_decide`. The main theorem carries a clean axiom certificate (`[propext, Classical.choice, Quot.sound]`). The single-file live layer (`Poincare4D.live.lean`) and the multi-module source build (`lake build Poincare4D`) both compile successfully (exit code 0).  The compiler emits 5 internal `PANIC` messages (LCNF ExplicitBoxing / Std DHashMap, known v4.31.0 issue with large files); these do not affect correctness.

---

## Abstract

We report a self-contained formalisation, in the Lean 4 proof assistant on top of
Mathlib, of the surgery-theoretic architecture surrounding the smooth 4-dimensional
Poincaré conjecture, together with a **conditional** diffeomorphism theorem. A single
package, `Poincare4D`, organises the material in the `Poincare4D` namespace across four
layers: a topological layer (closed smooth 4-manifolds, homotopy 4-spheres, the target
sphere class), a geometric layer (rotationally symmetric metric profiles, a coupled
gauge field, neck detection and surgery scales), an analytic layer (a coupled
Ricci–gauge flow modelled on the Angenent–Knopf and Allen–Cahn systems, phrased through
synthetic derivative *contracts* and a short-time-existence theorem parameterised by
explicit PDE hypotheses), and a surgery layer (smooth surgery data, finite surgery
chains, and their preservation contracts). The surgery structures `SmoothSurgeryStep`
and `FiniteSurgeryChain` **bundle the preservation properties as typed contract fields** —
forward preservation of the homotopy-4-sphere property (`preserves_homotopy_sphere`) and
backward preservation of the diffeomorphism-to-`S⁴` property (`preserves_diffeo_backward`) —
so that a valid surgery step or chain is, by definition, one that carries these
transports. The package then composes them into the conditional theorem
`smoothPoincare4D_conditional`: a closed smooth homotopy 4-sphere admitting a
finite surgery chain to a manifold diffeomorphic to the round sphere, together with a
round-extinction bridge, is itself diffeomorphic to the standard 4-sphere. The four
analytic inputs of the Ricci–gauge programme — a DeTurck gauge-fixing identity,
parabolic short-time existence, existence of the time-dependent flow, and pullback
invariance — are recorded as **named, typed `Prop` hypotheses** and are never assumed
globally: no package-local axiom is introduced. To our knowledge this is the first
proof-assistant formalisation of a smooth-surgery-chain calculus for the 4-dimensional
Poincaré problem with an explicit, discharge-ready analytic frontier.

---

## 1. Introduction

The Poincaré conjecture is resolved in every dimension except one for the smooth
category. In dimension three it is a theorem of Perelman via Hamilton's Ricci flow with
surgery; in dimensions `n ≥ 5` it follows from the `h`-cobordism theorem; and in
dimension four the *topological* statement is Freedman's theorem — a homotopy 4-sphere
is homeomorphic to `S⁴`. The **smooth** 4-dimensional Poincaré conjecture — that a
smooth homotopy 4-sphere is *diffeomorphic* to the standard `S⁴` — remains open, and is
one of the central unsolved problems of low-dimensional topology.

The M4TH library approaches formal mathematics from the side of *verified vocabulary*:
definitions and first theorems chosen to be the ones a subsequent development would want
to build on, each accompanied by a concrete structure in which the phenomenon is
exhibited. This paper treats the smooth 4D Poincaré problem in that spirit. It does not
claim a proof of the conjecture. What it contributes is a certified formal calculus of
**smooth surgery chains** and a **conditional theorem** whose analytic inputs — the hard
PDE facts a Ricci-flow-with-surgery argument would invoke — are isolated as explicit
typed hypotheses rather than smuggled in as axioms.

The formalisation makes a separation that the informal literature blurs: what is
*unconditional* (the combinatorics and topology of surgery preservation) is kept
strictly apart from what is the *analytic frontier* (short-time existence, parabolic
regularity, gauge equivalence). The frontier is not proved here; each piece is a named
`Prop` so that a later development of Ricci flow in Mathlib can discharge it.

Four movements organise the development.

1. **Topological foundations** (Section 3). Closed smooth 4-manifolds, the
   homotopy-4-sphere class `HomotopySphere`, and the target class
   `DiffeomorphicToSphere4`, all phrased over `EuclideanSpace ℝ (Fin 4)` and the standard
   sphere in `ℝ⁵`.

2. **Metric and gauge geometry** (Section 4). A cohomogeneity-one metric ansatz through
   a `RotationallySymmetricProfile`, a coupled `GaugeField` with a bounded coupling
   constant, and the neck-radius and surgery-scale predicates that decide where a
   surgery is admissible.

3. **The coupled Ricci–gauge flow** (Section 5). The Angenent–Knopf profile system
   coupled to an Allen–Cahn gauge equation, phrased through synthetic derivative
   *contracts* that pin the flow down without committing to a particular analytic
   representation, and a short-time-existence theorem `short_time_existence_H1` that
   takes its four PDE facts as explicit arguments.

4. **Surgery and the conditional theorem** (Sections 6–7). Smooth surgery data, single
   steps, and finite chains, with the preservation theorems, culminating in
   `smoothPoincare4D_conditional`.

All results are verified with no axioms beyond the foundations of Lean and Mathlib and
with no incomplete proofs. The package depends only on Mathlib and carries its own
`lakefile.toml`, so it can be reviewed, built, and upstreamed independently.

### 1.1 Contributions

- The first proof-assistant **surgery-chain calculus** for the 4-dimensional Poincaré
  problem: the structures `SmoothSurgeryStep` and `FiniteSurgeryChain`, each carrying the
  forward homotopy-4-sphere transport and the backward diffeomorphism-to-`S⁴` transport
  as typed contract fields, so that surgery preservation is a definitional part of a
  valid step or chain rather than an assumed axiom.
- A **contract-based coupled Ricci–gauge flow**: the Angenent–Knopf profile system and
  the Allen–Cahn gauge equation expressed through synthetic `HasDerivAt` contracts, so
  that the flow is a first-class typed object without a premature commitment to a
  functional-analytic solution space.
- A **short-time-existence theorem parameterised by its analytic inputs**
  (`short_time_existence_H1`), which consumes the four PDE facts as explicit hypotheses
  and produces the coupled-flow existence conclusion, introducing no global axiom.
- The **conditional smooth 4D Poincaré theorem** `smoothPoincare4D_conditional`, whose
  proof is a one-line composition of the backward diffeomorphism transport with the
  round-extinction bridge, and whose analytic frontier is exactly four named `Prop`s.
- A **native Lean-generated figure** and a single-file `Live` study version with a
  companion mathematical manual, so the package is reviewable end to end.

### 1.2 Non-goals

We do **not** prove the smooth 4D Poincaré conjecture, and we make no claim to do so. We
do not prove short-time existence, parabolic regularity, the DeTurck gauge-fixing
identity, or pullback invariance for the coupled system; these are the explicit
hypotheses. We do not construct the Ricci–gauge flow analytically, do not establish
extinction, and do not develop the smooth structure theory of 4-manifolds beyond what is
needed to state the surgery contracts. The conclusion class `DiffeomorphicToSphere4` is
modelled at the level of a homeomorphism to the standard sphere carried over the
charted-manifold instance context (see Section 8); the package is explicit that the deep
smooth-structure content lives in the conditional hypotheses, not in the encoding.

### 1.3 Relation to earlier releases

The M4TH library was inaugurated with v1.0.0 ("Hyperbolic and Dispersive PDE in Lean 4":
conservation laws, Burgers blow-up, the KdV soliton) and continued through v2.0.0
("Riemann–von Mangoldt": Dirichlet eta, zero counting, logarithmic residues, the digamma
identity), v3.0.0 ("Mertens' Theorems": the reciprocal-prime divergence and the
Meissel–Mertens constant), v4.0.0 (the critical-box argument principle and asymptotic
synthesis), and v5.0.0 / v5.5.0 (concrete `su(3)`, the SU(3) Wilson action, a certified
elliptic curve, Sophie-Germain prime-gap parity; then the M4TH protocol and the
web-compatibility layer). The present release, v6.0.0, is devoted **exclusively** to
`Poincare4D`. As with the earlier releases it shares no code with them and depends only
on Mathlib, so it may be reviewed and upstreamed on its own.

---

## 2. Setting and Mathlib background

The package is stated over the real numbers and uses the differential-geometry and
topology infrastructure of Mathlib: `EuclideanSpace ℝ (Fin n)` and the model space
`𝓘(ℝ, ·)`; `ChartedSpace` and `IsManifold`; `Metric.sphere`; the homotopy-equivalence
API `ContinuousMap.HomotopyEquiv`; `Homeomorph`; simple connectivity through
`AlgebraicTopology.FundamentalGroupoid.SimplyConnected`; and the calculus layer
`HasDerivAt`. The measure-theoretic imports (`Bochner` integration, Lebesgue measure,
compactly supported integrals) support the energy functionals of the flow layer. No new
axiomatic content is introduced.

All public declarations live in the `Poincare4D` namespace. The ambient model is fixed
once:

```lean
abbrev Euclidean4 := EuclideanSpace ℝ (Fin 4)
abbrev Model4 := 𝓘(ℝ, Euclidean4)

abbrev Euclidean5 := EuclideanSpace ℝ (Fin 5)
def StandardSphere4 := Metric.sphere (0 : Euclidean5) 1
def StandardSphere3 := Metric.sphere (0 : Euclidean4) 1
```

The public content is developed in the `Poincare4D` namespace and aggregated by the root
module `Poincare4D.lean` (which also carries the native SVG generator). It uses none of
the API names that changed between Lean v4.31.0 and v4.33.0-rc1; the package is verified
on v4.31.0 and no separate web variant is required.

---

## 3. Topological foundations

A closed smooth 4-manifold is recorded by two small typeclasses, kept `Prop`-valued so
they compose transparently:

```lean
class ClosedManifold (M : Type*) [TopologicalSpace M] : Prop where
  compact : CompactSpace M
  t2 : T2Space M

class Smooth4Manifold (M : Type*) [TopologicalSpace M] [ChartedSpace Euclidean4 M] : Prop where
  is_manifold : IsManifold Model4 ⊤ M
```

The hypothesis and the goal of the whole development are the homotopy-4-sphere class and
the diffeomorphism-to-`S⁴` class:

```lean
class HomotopySphere (M : Type*) [TopologicalSpace M] : Prop where
  homotopy_equiv_to_sphere4 : Nonempty (ContinuousMap.HomotopyEquiv M StandardSphere4)

class DiffeomorphicToSphere4 (M : Type*)
    [TopologicalSpace M] [ChartedSpace Euclidean4 M] [IsManifold Model4 ⊤ M] : Prop where
  homeo_to_sphere : Nonempty (Homeomorph M StandardSphere4)
```

`HomotopySphere` packages the classical hypothesis "homotopy equivalent to `S⁴`" as a
`Nonempty` bundle of a Mathlib homotopy equivalence to `StandardSphere4`.
`DiffeomorphicToSphere4` carries the charted-manifold context in its instance arguments
and records the target conclusion. These two classes are the endpoints between which the
surgery calculus operates.

---

## 4. Metric and gauge structures

The metric ansatz is cohomogeneity-one: `g = φ(t,x)² dx² + ψ(t,x)² g_{S³}`. It is captured
by a profile carrying strict positivity of the two warping functions, together with a
coupled gauge field and a bounded coupling constant:

```lean
structure RotationallySymmetricProfile where
  phi : ℝ → ℝ → ℝ
  psi : ℝ → ℝ → ℝ
  positive_phi : ∀ t x, 0 < phi t x
  positive_psi : ∀ t x, 0 < psi t x

structure GaugeField where
  w : ℝ → ℝ → ℝ

structure GaugeCoupling where
  gamma : ℝ
  gamma_pos : 0 < gamma
  gamma_lt_max : gamma < 8
```

Neck detection and the admissibility of a surgery are decided by a surgery scale and a
neck-radius datum:

```lean
structure SurgeryScale where
  eps : ℝ
  eps_pos : 0 < eps

def is_below_surgery_scale
    (p : RotationallySymmetricProfile) (t : ℝ) (scale : SurgeryScale) : Prop :=
  ∃ (neck : NeckRadiusData p t), neck.radius ≤ scale.eps
```

The coupling bound `0 < γ < 8` and the gauge band `-1 ≤ w ≤ 1` encode the physical
regime in which the Angenent–Knopf/Seiberg–Witten-type coupling is expected to be
well-behaved; they enter the flow contracts of Section 5 but never as axioms.

---

## 5. The coupled Ricci–gauge flow

The distinctive design decision of the flow layer is to phrase derivatives as
**contracts** rather than to fix a Banach-space representation of solutions. A
`ProfileDerivatives` bundle names the intended time, space, and second-space derivatives,
and a predicate asserts that these coincide with genuine Mathlib `HasDerivAt` data:

```lean
structure realizes_profile_derivatives
    (p : RotationallySymmetricProfile) (dp : ProfileDerivatives p) : Prop where
  has_time_deriv : ∀ t x, HasDerivAt (fun τ ↦ p.psi τ x) (dp.psi_t t x) t
  has_space_deriv : ∀ t x, HasDerivAt (fun y ↦ p.psi t y) (dp.psi_x t x) x
  has_second_space_deriv : ∀ t x, HasDerivAt (fun y ↦ dp.psi_x t y) (dp.psi_xx t x) x
```

The Angenent–Knopf profile system and the Allen–Cahn gauge equation are then equalities
between the named derivatives and the geometric right-hand sides,

```
φ_t = 3 ψ_xx /(ψ φ) − 3 ψ_x φ_x /(ψ φ²)
ψ_t = ψ_xx / φ² − ψ_x φ_x / φ³ − 2(1 − ψ_x²/φ²)/ψ + γ · e(w)/ψ
w_t = w_xx / φ² − w_x φ_x / φ³ + 3 ψ_x w_x /(ψ φ²) − w(w² − 1)
```

bundled into a single flow contract:

```lean
def satisfies_coupled_ricci_gauge_flow (state : CoupledFlowState) : Prop :=
  realizes_profile_derivatives state.profile state.profile_derivs ∧
  realizes_gauge_derivatives state.gauge state.gauge_derivs ∧
  satisfies_angenent_knopf_equation … ∧
  satisfies_allen_cahn_equation …
```

Short-time existence is a theorem, not an axiom: it consumes the four analytic facts as
explicit arguments together with initial data and a witnessing state, and returns the
existence conclusion in the `Assumptions` namespace.

```lean
theorem short_time_existence_H1
    {M : Type*} [TopologicalSpace M] [ChartedSpace Euclidean4 M]
    {p : RotationallySymmetricProfile}
    (_hCohom : CohomogeneityOneManifold M p)
    (initial_p : RotationallySymmetricProfile) (initial_g : GaugeField) (gamma : ℝ)
    (hDeTurck : DeTurckIdentity)
    (hParabolic : ParabolicShortTimeExistence M)
    (_hFlow : TimeDependentFlowExists M)
    (_hInvariance : PullbackInvariance M)
    (state : CoupledFlowState)
    (h0_in_dom : 0 ∈ state.time_domain)
    (hGamma : state.coupling.gamma = gamma)
    (hInitPhi : ∀ x, state.profile.phi 0 x = initial_p.phi 0 x)
    (hInitPsi : ∀ x, state.profile.psi 0 x = initial_p.psi 0 x)
    (hInitW : ∀ x, state.gauge.w 0 x = initial_g.w 0 x)
    (hFlowSatisfies : satisfies_coupled_ricci_gauge_flow state) :
    Assumptions.ShortTimeExistsCoupledFlow initial_p initial_g gamma
```

The four PDE inputs are `Prop`-valued structures declared in the `Flow` layer:

```lean
structure DeTurckIdentity : Prop where …
structure ParabolicShortTimeExistence (M : Type*) : Prop where …
structure TimeDependentFlowExists (M : Type*) : Prop where …
structure PullbackInvariance (M : Type*) : Prop where …
```

Nothing in Section 5 asserts these hold; the theorem is an implication from them.

---

## 6. Surgery infrastructure

A single smooth surgery — excise a cylindrical neck and glue in standard caps — is a
`SmoothSurgeryStep` between a pre-manifold `Mpre` and a post-manifold `Mpost`. It bundles
the surgery datum, the cohomogeneity-one compatibility witness, and — crucially — the two
preservation properties as **contract fields**:

```lean
structure SmoothSurgeryStep (Mpre Mpost : Type*)
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost] where
  datum : SmoothSurgeryDatum
  compatible : CohomogeneityOneSurgeryCompatible Mpre Mpost datum
  preserves_homotopy_sphere :
    Assumptions.SmoothSurgeryPreservesHomotopySphere
      Mpre Mpost datum compatible.pre_modeled compatible.post_modeled
  preserves_diffeo_backward : DiffeomorphicToSphere4 Mpost → DiffeomorphicToSphere4 Mpre
```

A finite surgery chain then records the list of surgery events together with the two
end-to-end transports, again as fields — forward for the homotopy-sphere property,
backward for the diffeomorphism conclusion:

```lean
structure FiniteSurgeryChain (Mstart Mend : Type*)
    [TopologicalSpace Mstart] [ChartedSpace Euclidean4 Mstart] [IsManifold Model4 ⊤ Mstart]
    [TopologicalSpace Mend] [ChartedSpace Euclidean4 Mend] [IsManifold Model4 ⊤ Mend] where
  events : List SmoothSurgeryDatum
  preserves_homotopy_sphere : HomotopySphere Mstart → HomotopySphere Mend
  preserves_diffeo_backward : DiffeomorphicToSphere4 Mend → DiffeomorphicToSphere4 Mstart
```

Modelling preservation as contract *data* rather than as a derived theorem is a deliberate
scoping choice: the package does not claim to prove, from a bare definition of surgery,
that surgery preserves the homotopy or diffeomorphism type — that is precisely the
low-dimensional-topology content the smooth conjecture turns on. Instead a *valid* step or
chain is one that carries these transports, and the theory downstream is honest about
using them as inputs. A typed variant `TypedFiniteSurgeryChain n` indexes the chain by its
length and induces the endpoint chain used by the main theorem. The forward and backward
directions are exactly what the Poincaré argument needs: run the flow-with-surgery
*forward* from a homotopy sphere to a recognisably round endpoint, then transport the
diffeomorphism *backward* to the original manifold.

---

## 7. The conditional Poincaré theorem

The round-extinction bridge names the one implication that a completed analytic theory
would supply — that extinction of the flow to a round point forces the endpoint to be
diffeomorphic to `S⁴`:

```lean
def RoundExtinctionImpliesSphereDiffeomorphism (M : Type*)
    [TopologicalSpace M] [ChartedSpace Euclidean4 M] [IsManifold Model4 ⊤ M]
    (_h_closed : ClosedManifold M) (_h_homotopy : HomotopySphere M) : Prop :=
  (∃ (final_state : CoupledFlowState), extinct_to_round_point final_state) →
    DiffeomorphicToSphere4 M
```

The main theorem then composes the surgery calculus with this bridge. Given a closed
smooth homotopy 4-sphere `M`, a finite surgery chain to a closed `Mend`, the
round-extinction bridge for `Mend`, and an extinction witness, `M` is diffeomorphic to
the standard 4-sphere:

```lean
theorem smoothPoincare4D_conditional
  (M Mend : Type*)
  [TopologicalSpace M] [ChartedSpace Euclidean4 M] [IsManifold Model4 ⊤ M]
  [TopologicalSpace Mend] [ChartedSpace Euclidean4 Mend] [IsManifold Model4 ⊤ Mend]
  (_h_closed_start : ClosedManifold M)
  (h_closed_end : ClosedManifold Mend)
  (h_homotopy : HomotopySphere M)
  (chain : FiniteSurgeryChain M Mend)
  (h_bridge : Assumptions.RoundExtinctionImpliesSphereDiffeomorphism
      Mend h_closed_end (chain.preserves_homotopy_sphere h_homotopy))
  (h_extinct : ∃ (final_state : CoupledFlowState), extinct_to_round_point final_state) :
  DiffeomorphicToSphere4 M :=
  chain.preserves_diffeo_backward (h_bridge h_extinct)
```

The proof is a single composition: the extinction witness discharges the bridge to yield
`DiffeomorphicToSphere4 Mend`, which the chain's backward-preservation field transports to
`DiffeomorphicToSphere4 M`. Every hard analytic input is visible in the hypothesis list.
The four PDE bridges of the Ricci–gauge programme are the explicit frontier:

| Hypothesis | Role |
|---|---|
| `DeTurckIdentity` | Gauge-fixing identity for the parabolic system |
| `ParabolicShortTimeExistence M` | Short-time existence for the parabolic flow |
| `TimeDependentFlowExists M` | Flow of the time-dependent vector fields |
| `PullbackInvariance M` | Pullback invariance of Ricci, energy, and Laplacian |

These are named, typed, and individually dischargeable; the package introduces zero
package-local axioms.

---

## 8. Formalisation notes

**Unconditional versus conditional.** The surgery calculus of Section 6 is unconditional
*within the package*: given a `SmoothSurgeryStep` or a `FiniteSurgeryChain`, the
preservation theorems hold outright. The analytic content — short-time existence,
parabolic regularity, DeTurck gauge-fixing, pullback invariance, and round extinction —
is conditional, and every statement that uses it displays the relevant `Prop` in its
hypotheses. The package makes no claim to an unconditional resolution of the smooth 4D
Poincaré conjecture, which remains open.

**Contracts instead of a solution space.** The flow layer uses synthetic derivative
contracts (`realizes_profile_derivatives`, the Angenent–Knopf and Allen–Cahn predicates)
so that the coupled flow is a typed object whose defining equations are stated exactly,
without prematurely committing Mathlib to a functional-analytic existence theory. This is
the same discipline the M4TH corpus uses elsewhere for conditional frontiers, e.g. the
typed analytic-frontier bridge of the Riemann–von Mangoldt release.

**Encoding of the conclusion.** The target class `DiffeomorphicToSphere4` is defined as
`Nonempty (Homeomorph M StandardSphere4)` carried over the `ChartedSpace`/`IsManifold`
instance context. The package is explicit that the smooth-structure strength of the
conjecture is located in the conditional hypotheses (round extinction, gauge equivalence)
rather than in this encoding; the conclusion should be read as "recognised as the round
sphere at the modelled level", conditional on the analytic frontier.

**No axioms, no `sorry`, no `native_decide`.** Every result is kernel-checked. The main
theorem `smoothPoincare4D_conditional` returns the certificate
`[propext, Classical.choice, Quot.sound]`, i.e. only the foundational axioms of Lean and
Mathlib. (Surgery preservation is carried as structure fields rather than as separately
proved theorems, so the certificate is stated for the composed conditional theorem.)

**Packaging.** The public content lives in the `Poincare4D` namespace, with the analytic
hypotheses gathered in an `Assumptions`/`H1` layer, and is aggregated by the root module
`Poincare4D.lean`. The package carries its own `lakefile.toml` (pinned to Mathlib
`fabf563a`), a native Lean-generated SVG cover, and a single-file `Live` study version
with a companion manual.

---

## 9. Related work

The topological 4-dimensional Poincaré conjecture is Freedman's theorem (1982): a
homotopy 4-sphere is homeomorphic to `S⁴`. The smooth version is open and is the subject
of an extensive programme in gauge theory and geometric analysis. In dimension three the
conjecture is Perelman's theorem via Hamilton's Ricci flow with surgery; the profile
system used here as a contract is of Angenent–Knopf type, and the gauge coupling is
Allen–Cahn/Seiberg–Witten in flavour. On the formal side, Mathlib supplies the manifold,
homotopy-equivalence, and calculus infrastructure the package rests on, and formal
differential geometry in proof assistants is an active area; we are not aware of a prior
formalisation of a smooth-surgery-chain calculus with an explicit analytic frontier for
the 4-dimensional Poincaré problem. The present work is complementary to any future
formal development of Ricci flow: it supplies the surgery bookkeeping and the conditional
theorem, and it names precisely the analytic lemmas such a development would discharge.

Classical references for the mathematics modelled here are Freedman and Quinn's *Topology
of 4-Manifolds* [3], Scorpan's *The Wild World of 4-Manifolds* [5], Morgan and Tian's
account of Ricci flow and the Poincaré conjecture [4], Angenent and Knopf on neckpinch
profiles [1], and Chow and Knopf's *The Ricci Flow* [2]; we formalise only the surgery
architecture and the conditional statement.

---

## 10. Availability

The package is available at <https://github.com/Alektronnik/M4TH> under the Apache 2.0
license, with its own `lakefile.toml` (pinned to Mathlib `fabf563a`, Lean 4 v4.31.0)
and a native Lean-generated SVG cover figure. It
includes a `Live` single-file study version and a mathematical manual. After a successful
build the axiom certificate of the headline results may be reproduced with

```
#print axioms Poincare4D.smoothPoincare4D_conditional
```

returning `[propext, Classical.choice, Quot.sound]`.

---

## References

1. S. B. Angenent and D. Knopf, *An example of neckpinching for Ricci flow on `S^{n+1}`*,
   Math. Res. Lett. **11** (2004), 493–518.
2. B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, Mathematical Surveys and
   Monographs **110**, AMS, 2004.
3. M. H. Freedman and F. Quinn, *Topology of 4-Manifolds*, Princeton University Press,
   1990.
4. J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics
   Monographs **3**, AMS, 2007.
5. A. Scorpan, *The Wild World of 4-Manifolds*, AMS, 2005.
6. The mathlib Community, *The Lean Mathematical Library*, CPP 2020;
   <https://github.com/leanprover-community/mathlib4>.
