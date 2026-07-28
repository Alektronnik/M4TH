# XiLogResidue.live

**Author:** Bezalel Izquierdo Pérez  
**License:** Apache 2.0  
**Live file:** `XiLogResidue.live.lean`

---

## I. Purpose

This live file is the single-file study version of the `XiLogResidue` package.

It formalizes the local residue of the logarithmic derivative of the entire Xi
variant and relates it to two multiplicity languages:

- analytic multiplicity, through `analyticOrderNatAt`;
- meromorphic divisor multiplicity, through `MeromorphicOn.divisor`.

The file is a reading copy of the public package.  It does not import local
package modules and does not contain graph-generation code.

---

## II. Source Order

The live file is fused in dependency order:

```text
XiLogResidue/Basic.lean
XiLogResidue/LocalResidue.lean
XiLogResidue/Divisor.lean
```

The only imports are Mathlib imports:

```lean
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Tactic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.DiscreteSubset
```

---

## III. Critical Box and Zero Set

The first layer defines the nontrivial zeros of the Riemann zeta function:

```lean
def nontrivialZeros : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}
```

It then restricts them by positive imaginary part and height:

```lean
def zerosUpToIm (T : ℝ) : Set ℂ :=
  {s : ℂ | s ∈ nontrivialZeros ∧ 0 < s.im ∧ s.im ≤ T}
```

The geometric region is the closed critical box:

```lean
def criticalBox (T : ℝ) : Set ℂ :=
  {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}
```

Its boundary is split into four edges:

```lean
criticalBoxTopEdge
criticalBoxBottomEdge
criticalBoxLeftEdge
criticalBoxRightEdge
criticalBoxBoundary
```

The safe-height condition is:

```lean
def IsSafeHeight (T : ℝ) : Prop :=
  ∀ s ∈ criticalBoxTopEdge T, ¬ s ∈ nontrivialZeros
```

This prevents zeros from lying on the top edge of the box.

---

## IV. The Entire Xi Variant

The package uses the entire Xi variant:

```lean
noncomputable def entireXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1
```

The basic analytic API is:

```lean
differentiable_entireXi
continuous_entireXi
analyticAt_entireXi
entireXi_ne_zero_at_zero
```

The zero set is:

```lean
def entireXiZeros : Set ℂ :=
  {z : ℂ | entireXi z = 0}
```

Inside the open critical strip, zeros of `riemannZeta` and zeros of `entireXi`
are connected by:

```lean
completedRiemannZeta_zero_iff
nontrivial_zero_implies_entireXi_zero
entireXi_zero_implies_nontrivial
```

This is the bridge that lets the package count zeta zeros through the analytic
behavior of `entireXi`.

---

## V. Finiteness and Multiplicity

The package proves discreteness and finiteness of the relevant zero set:

```lean
isDiscrete_entireXi_zeros
zeros_discrete_entireXi
finite_zeros_in_box
zerosUpToIm_finite
```

The finite zero set is:

```lean
noncomputable def zerosUpToImFinset (T : ℝ) : Finset ℂ :=
  (zerosUpToIm_finite T).toFinset
```

Analytic multiplicity is recorded as:

```lean
noncomputable def entireXiZeroMultiplicity (s : ℂ) : ℕ :=
  analyticOrderNatAt entireXi s
```

The logarithmic derivative is:

```lean
noncomputable def entireXiLogDeriv (s : ℂ) : ℂ :=
  logDeriv entireXi s
```

The package-local multiplicity count is:

```lean
noncomputable def zeroCountingWithMultiplicity (T : ℝ) : ℝ :=
  Nat.cast ((zerosUpToImFinset T).sum entireXiZeroMultiplicity)
```

---

## VI. Local Logarithmic Residue

The simple-zero case is:

```lean
theorem entireXi_logDeriv_residue_simple_zero {s : ℂ}
    (hs : entireXi s = 0) (hs' : deriv entireXi s ≠ 0) :
    Tendsto (fun w => (w - s) * entireXiLogDeriv w) (𝓝[≠] s) (𝓝 1)
```

The general theorem is:

```lean
theorem entireXi_logDeriv_residue_eq_multiplicity {s : ℂ}
    (hs : entireXi s = 0) :
    Tendsto (fun w => (w - s) * entireXiLogDeriv w) (𝓝[≠] s)
      (𝓝 (entireXiZeroMultiplicity s : ℂ))
```

The proof uses the local analytic factorization supplied by Mathlib's analytic
order API:

```text
f(z) = (z - p)^n g(z),     g(p) ≠ 0
```

and rewrites the logarithmic derivative as:

```text
logDeriv f = n / (z - p) + bounded term.
```

Multiplying by `z - p` and taking the punctured-neighborhood limit gives the
analytic multiplicity.

The package-level proposition is:

```lean
def EntireXiLogResidueEqualsMultiplicity : Prop :=
  ∀ {s : ℂ}, entireXi s = 0 →
    Tendsto (fun w => (w - s) * entireXiLogDeriv w) (𝓝[≠] s)
      (𝓝 (entireXiZeroMultiplicity s : ℂ))
```

and the exported theorem is:

```lean
theorem entireXi_logResidue_equals_multiplicity :
    EntireXiLogResidueEqualsMultiplicity
```

---

## VII. Divisor Dictionary

The divisor layer works on the compact critical box.

The boundary condition is:

```lean
def entireXi_ne_zero_on_box_boundary (T : ℝ) : Prop :=
  ∀ s ∈ criticalBoxBoundary T, entireXi s ≠ 0
```

This condition is explicit.  The package does not claim an unconditional
zero-free boundary theorem.

The meromorphic API is:

```lean
entireXi_meromorphicOn_criticalBox
entireXiLogDeriv_meromorphicOn_criticalBox
divisor_support_criticalBox_finite
entireXi_meromorphicOrder_ne_top_on_criticalBox
```

The local dictionary between the divisor value and analytic multiplicity is:

```lean
lemma entireXi_divisor_eq_multiplicity {T : ℝ} {s : ℂ}
    (hs : s ∈ criticalBox T) (hzero : entireXi s = 0) :
    (MeromorphicOn.divisor entireXi (criticalBox T) s : ℂ) =
      (entireXiZeroMultiplicity s : ℂ)
```

The support dictionary is proved in both directions:

```lean
mem_divisor_finset_zerosUpToIm
mem_zerosUpToIm_finset_divisor_support
```

The final finite-support theorem is:

```lean
lemma entireXi_divisor_finset_eq_zerosUpToImFinset
    (T : ℝ) (hSafe : IsSafeHeight T)
    (hne : entireXi_ne_zero_on_box_boundary T) :
    (divisor_support_criticalBox_finite T).toFinset = zerosUpToImFinset T
```

This identifies the support of the meromorphic divisor in the box with the
finite set of zeros counted by height, under the safe-height and boundary
nonvanishing hypotheses.

---

## VIII. Verification

Compile the live file directly:

```text
lake env lean XiLogResidue/XiLogResidueLive/XiLogResidue.live.lean
```

A clean run produces no output.

Check for forbidden local dependencies or unfinished proof markers:

```text
rg -n "public import XiLogResidue|import XiLogResidue|RiemannSynthesis|NavierStokesWeb|BirchSwinnertonDyerWeb|ErdosWeb|source corpus|mother formalization|unpublished formalization|formalizacion madre|formalización madre|\bsorry\b|\baxiom\b|admit|native_decide" XiLogResidue/XiLogResidueLive/XiLogResidue.live.lean
```

A clean run produces no output.

---

## IX. Axiom Certificate

The following command records the trusted kernel base used by the main package
theorems:

```text
printf 'import XiLogResidue
#print axioms RiemannLogResidue.entireXi_logDeriv_residue_eq_multiplicity
#print axioms RiemannLogResidue.entireXi_logResidue_equals_multiplicity
#print axioms RiemannLogResidue.entireXi_divisor_eq_multiplicity
#print axioms RiemannLogResidue.entireXi_divisor_finset_eq_zerosUpToImFinset
' | lake env lean --stdin
```

Expected output:

```text
'RiemannLogResidue.entireXi_logDeriv_residue_eq_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannLogResidue.entireXi_logResidue_equals_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannLogResidue.entireXi_divisor_eq_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannLogResidue.entireXi_divisor_finset_eq_zerosUpToImFinset' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is the standard Lean/Mathlib kernel base for this classical development.
