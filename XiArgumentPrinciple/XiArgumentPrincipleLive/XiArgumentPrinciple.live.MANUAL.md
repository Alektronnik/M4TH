# XiArgumentPrinciple.live

**Author:** Bezalel Izquierdo Pérez  
**License:** Apache 2.0  
**Live file:** `XiArgumentPrinciple.live.lean`

---

## I. Purpose

This live file is the single-file study version of the `XiArgumentPrinciple`
package.

It formalizes the critical-box contour framework for the entire Xi variant and
packages the argument-principle step which turns a contour integral of
`ξ'/ξ` into a multiplicity count of zeros.

The central theorem is conditional on an explicit bridge:

```lean
RiemannArgumentPrinciple.ArgumentPrincipleBridge T
```

This bridge represents the rectangular argument-principle input.  It is a
typed hypothesis, not a local trusted declaration.

---

## II. Source Order

The live file is fused in dependency order:

```text
XiArgumentPrinciple/Basic.lean
XiArgumentPrinciple/Contour.lean
XiArgumentPrinciple/Counting.lean
```

The live file imports only Mathlib dependencies and does not import the local
package modules.

---

## III. Basic Infrastructure

The first layer defines the open critical-strip zero set:

```lean
def nontrivialZeros : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}
```

Zeros up to height `T` are:

```lean
def zerosUpToIm (T : ℝ) : Set ℂ :=
  {s : ℂ | s ∈ nontrivialZeros ∧ 0 < s.im ∧ s.im ≤ T}
```

The critical box is:

```lean
def criticalBox (T : ℝ) : Set ℂ :=
  {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}
```

The safe-height condition excludes zeros from the top edge:

```lean
def IsSafeHeight (T : ℝ) : Prop :=
  ∀ s ∈ criticalBoxTopEdge T, ¬ s ∈ nontrivialZeros
```

The package proves that zeros counted by `zerosUpToIm T` lie in the interior of
the critical box when `T` is safe:

```lean
zerosUpToIm_subset_criticalBoxInterior
```

---

## IV. Entire Xi and Multiplicity

The entire Xi variant is:

```lean
noncomputable def entireXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1
```

The basic analytic API is:

```lean
differentiable_entireXi
continuous_entireXi
analyticAt_entireXi
```

Inside the open critical strip, zeta zeros and `entireXi` zeros are related by:

```lean
completedRiemannZeta_zero_iff
nontrivial_zero_implies_entireXi_zero
entireXi_zero_implies_nontrivial
```

The finite zero set and multiplicity count are:

```lean
noncomputable def zerosUpToImFinset (T : ℝ) : Finset ℂ :=
  (zerosUpToIm_finite T).toFinset

noncomputable def entireXiZeroMultiplicity (s : ℂ) : ℕ :=
  analyticOrderNatAt entireXi s

noncomputable def zeroCountingWithMultiplicity (T : ℝ) : ℝ :=
  Nat.cast ((zerosUpToImFinset T).sum entireXiZeroMultiplicity)
```

---

## V. Contour Parametrization

The contour layer defines the four oriented edges of the critical box:

```lean
criticalBoxBottomParam
criticalBoxRightParam
criticalBoxTopParam
criticalBoxLeftParam
```

The edge integrals use the logarithmic derivative of `entireXi`:

```lean
entireXiBottomEdgeIntegral
entireXiRightEdgeIntegral
entireXiTopEdgeIntegral
entireXiLeftEdgeIntegral
```

The full boundary integral is:

```lean
noncomputable def entireXiContourIntegral (T : ℝ) : ℂ :=
  entireXiBottomEdgeIntegral + entireXiRightEdgeIntegral T +
    entireXiTopEdgeIntegral T + entireXiLeftEdgeIntegral T
```

The rectangular integral convention is:

```lean
noncomputable def criticalBoxRectangleIntegral (f : ℂ → ℂ) (T : ℝ) : ℂ :=
  (∫ x in (0 : ℝ)..1, f (x : ℂ)) -
    (∫ x in (0 : ℝ)..1, f ((x : ℂ) + (T : ℂ) * I)) +
  (Complex.I • ∫ y in (0 : ℝ)..T, f (1 + (y : ℂ) * I)) -
    (Complex.I • ∫ y in (0 : ℝ)..T, f ((y : ℂ) * I))
```

The package proves the equality between the edge-by-edge contour and the
rectangular convention:

```lean
theorem entireXiContourIntegral_eq_rectangleIntegral (T : ℝ) :
    entireXiContourIntegral T =
      criticalBoxRectangleIntegral entireXiLogDeriv T
```

---

## VI. Cauchy Index and Bridge

The counting layer defines the Cauchy kernel:

```lean
noncomputable def contourCauchyKernel (w : ℂ) (z : ℂ) : ℂ :=
  1 / (z - w)
```

and its contour index integral:

```lean
noncomputable def contourCauchyIndexIntegral (w : ℂ) (T : ℝ) : ℂ :=
  criticalBoxRectangleIntegral (contourCauchyKernel w) T
```

The typed winding statement is:

```lean
def ContourWindingIndexEq (T : ℝ) (w : ℂ) (k : ℤ) : Prop :=
  contourCauchyIndexIntegral w T = (k : ℂ) * (2 * Real.pi * I)
```

The external analytic interface is:

```lean
structure ArgumentPrincipleBridge (T : ℝ) : Prop where
  index_one :
    ∀ {w : ℂ}, w ∈ criticalBoxInterior T →
      contourCauchyIndexIntegral w T = 2 * Real.pi * I
  index_zero :
    ∀ {w : ℂ}, w ∉ criticalBox T →
      contourCauchyIndexIntegral w T = 0
  residue_sum :
    entireXiContourIntegral T / (2 * Real.pi * I) =
      entireXiCriticalBoxResidueSum T
```

This structure is the exact frontier of the package.  The live file does not
claim to prove the rectangular residue theorem internally.

---

## VII. Counting Theorems

The package first packages the winding-index statement:

```lean
theorem contour_winding_index_one_of_safe {T : ℝ}
    (hT : 0 < T) (hSafe : IsSafeHeight T)
    (hBridge : ArgumentPrincipleBridge T) :
    ContourWindingIndexOne T
```

Every zero counted by `zerosUpToIm T` has winding index `+1`:

```lean
theorem contour_winding_index_one_on_zerosUpToIm {T : ℝ}
    (hSafe : IsSafeHeight T) (hBridge : ArgumentPrincipleBridge T) :
    ∀ {s : ℂ}, s ∈ zerosUpToIm T → ContourWindingIndexEq T s 1
```

The residue sum equals the multiplicity count under the bridge:

```lean
theorem contour_residue_sum_equals_N_of_safe {T : ℝ}
    (hT : 0 < T) (hSafe : IsSafeHeight T)
    (hBridge : ArgumentPrincipleBridge T) :
    ContourResidueSumEqualsN T
```

The main contour-counting theorem is:

```lean
theorem contour_winding_equals_count_of_safe {T : ℝ}
    (hT : 0 < T) (hSafe : IsSafeHeight T)
    (hBridge : ArgumentPrincipleBridge T) :
    ContourWindingEqualsCount T
```

It proves:

```text
∮ ξ'/ξ = 2πi · zeroCountingWithMultiplicity(T)
```

in the typed form used by the package.

The eventual global form is:

```lean
theorem contour_winding_equals_count_forall
    (h : ∀ T > 0, ∃ T' ≥ T,
      IsSafeHeight T' ∧ ArgumentPrincipleBridge T') :
    ContourWindingEqualsCountEventually
```

---

## VIII. Verification

Compile the live file directly:

```text
lake env lean XiArgumentPrinciple/XiArgumentPrincipleLive/XiArgumentPrinciple.live.lean
```

A clean run produces no output.

Check for forbidden local dependencies or unfinished proof markers:

```text
rg -n "public import XiArgumentPrinciple|import XiArgumentPrinciple|RiemannSynthesis|NavierStokesWeb|BirchSwinnertonDyerWeb|ErdosWeb|source corpus|mother formalization|unpublished formalization|formalizacion madre|formalización madre|\bsorry\b|\baxiom\b|admit|native_decide" XiArgumentPrinciple/XiArgumentPrincipleLive/XiArgumentPrinciple.live.lean
```

A clean run produces no output.

---

## IX. Axiom Certificate

The following command records the trusted kernel base used by representative
theorems:

```text
printf 'import XiArgumentPrinciple
#print axioms RiemannArgumentPrinciple.entireXiContourIntegral_eq_rectangleIntegral
#print axioms RiemannArgumentPrinciple.contour_winding_index_one_of_safe
#print axioms RiemannArgumentPrinciple.contour_residue_sum_equals_N_of_safe
#print axioms RiemannArgumentPrinciple.contour_winding_equals_count_of_safe
#print axioms RiemannArgumentPrinciple.contour_winding_equals_count_forall
' | lake env lean --stdin
```

Expected output:

```text
'RiemannArgumentPrinciple.entireXiContourIntegral_eq_rectangleIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannArgumentPrinciple.contour_winding_index_one_of_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannArgumentPrinciple.contour_residue_sum_equals_N_of_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannArgumentPrinciple.contour_winding_equals_count_of_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannArgumentPrinciple.contour_winding_equals_count_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is the standard Lean/Mathlib kernel base for this classical development.
