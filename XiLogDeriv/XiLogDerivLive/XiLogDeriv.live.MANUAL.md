# XiLogDeriv.live

**Author:** Bezalel Izquierdo Pérez  
**License:** Apache 2.0  
**Live file:** `XiLogDeriv.live.lean`

---

## I. Mathematical Aim

`XiLogDeriv.live.lean` is the single-file reading version of the
`XiLogDeriv` package.

The package isolates the logarithmic-derivative expansion of the entire
Riemann Xi variant used in contour arguments.  The formal target is the
decomposition

```lean
entireXiLogDeriv s =
  1 / s + 1 / (s - 1) +
    (-(1 / 2) * log (Real.pi : ℂ) + (1 / 2) * digamma (s / 2)) +
      riemannZetaLogDeriv s
```

under the explicit regularity and nonvanishing hypotheses required by
Mathlib's `logDeriv` API.

The file also packages the analytic support layer around `Complex.Gammaℝ` and
`digamma`: nonvanishing away from real poles, differentiability of the Gamma
factor, the Gamma-real digamma identity, and continuity wrappers on the contour
edges needed by later Riemann-von Mangoldt developments.

No Riemann Hypothesis statement is assumed or proved here.  Zeta and Xi
nonvanishing hypotheses remain visible in the statements that require them.

---

## II. Source Architecture

The live file is a faithful fusion of the public package modules:

```text
XiLogDeriv/Basic.lean
XiLogDeriv/GammaR.lean
XiLogDeriv/DigammaContinuity.lean
XiLogDeriv/Expansion.lean
```

The namespace is:

```lean
namespace RiemannLogDeriv
```

This name keeps the standalone package separate from other Riemann packages in
the same workspace.  A later Mathlib contribution may choose a final namespace
with reviewers.

The live file imports only Mathlib modules.  It does not import the local
package modules, because the source content is present directly in the file.

---

## III. Basic Xi and Log-Derivative Infrastructure

The first source block defines the package-local Xi variant:

```lean
noncomputable def entireXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1
```

It also defines the polynomial factor and the logarithmic derivatives used in
the expansion:

```lean
noncomputable def entireXiPolynomialFactor (s : ℂ) : ℂ :=
  s * (s - 1)

noncomputable def entireXiLogDeriv (s : ℂ) : ℂ :=
  logDeriv entireXi s

noncomputable def entireXiPolynomialLogDeriv (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1)

noncomputable def completedRiemannZetaLogDeriv (s : ℂ) : ℂ :=
  logDeriv completedRiemannZeta s

noncomputable def gammaRFactorLogDeriv (s : ℂ) : ℂ :=
  logDeriv Complex.Gammaℝ s

noncomputable def riemannZetaLogDeriv (s : ℂ) : ℂ :=
  logDeriv riemannZeta s
```

The basic regularity layer proves that `entireXi` is differentiable,
continuous, and analytic at every complex point:

```lean
lemma differentiable_entireXi : Differentiable ℂ entireXi
lemma continuous_entireXi : Continuous entireXi
lemma analyticAt_entireXi (s : ℂ) : AnalyticAt ℂ entireXi s
```

The bridge to Mathlib's completed zeta is explicitly restricted away from
`0` and `1`:

```lean
lemma entireXi_eq_polynomial_times_completedZeta_of_ne_zero_ne_one {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireXi s = s * (s - 1) * completedRiemannZeta s
```

The polynomial logarithmic derivative is separated as a reusable lemma:

```lean
lemma logDeriv_entireXiPolynomialFactor_eq {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv entireXiPolynomialFactor s = 1 / s + 1 / (s - 1)
```

The first-stage expansion is:

```lean
theorem entireXiLogDeriv_expansion_of_ne_zero_ne_one {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (_hξ : entireXi s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) :
    entireXiLogDeriv s =
      1 / s + 1 / (s - 1) + completedRiemannZetaLogDeriv s
```

The hypothesis `_hξ` is present because this is a logarithmic-derivative
statement.  It is intentionally not hidden.

---

## IV. Gamma-Real and Digamma Identity

The second source block proves the API for the archimedean factor.

The nonvanishing lemma says that `Complex.Gammaℝ` cannot vanish off the real
axis:

```lean
lemma Complex_Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (him : s.im ≠ 0) :
    Complex.Gammaℝ s ≠ 0
```

The differentiability wrapper allows `logDeriv` to be applied to
`Complex.Gammaℝ` under a nonvanishing hypothesis:

```lean
lemma differentiableAt_Complex_Gammaℝ_of_ne_zero {s : ℂ}
    (hγ : Complex.Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ s
```

The completed zeta factor is decomposed as:

```lean
lemma completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hγ : Complex.Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s
```

This yields the second-stage logarithmic derivative expansion:

```lean
theorem completedRiemannZetaLogDeriv_expansion_of_factors_ne_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hγ : Complex.Gammaℝ s ≠ 0)
    (hzeta : riemannZeta s ≠ 0) (_hΛ : completedRiemannZeta s ≠ 0) :
    completedRiemannZetaLogDeriv s =
      gammaRFactorLogDeriv s + riemannZetaLogDeriv s
```

The Gamma-real digamma identity is the central archimedean theorem:

```lean
theorem gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma {s : ℂ}
    (hγ : Complex.Gammaℝ s ≠ 0) :
    gammaRFactorLogDeriv s =
      -(1 / 2) * log (Real.pi : ℂ) + (1 / 2) * digamma (s / 2)
```

The proof is split through:

```lean
lemma gammaRPiCpow_logDeriv (s : ℂ)
lemma gamma_half_digamma_logDeriv {s : ℂ} (hγ : Gamma (s / 2) ≠ 0)
```

The first lemma handles the `π^{-s/2}` factor.  The second lemma handles the
Gamma term through Mathlib's `digamma` API.

---

## V. Digamma Continuity Wrappers

The third source block packages continuity facts for later contour work.

The basic pointwise wrappers are:

```lean
lemma digamma_continuousAt_of_ne_neg_nat {z : ℂ}
    (hz : ∀ m : ℕ, z ≠ -↑m) :
    ContinuousAt digamma z

lemma digamma_continuousAt_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    ContinuousAt digamma z
```

For positive real half-lines:

```lean
lemma digamma_ne_neg_nat_of_real_half_pos {t : ℝ} (ht : 0 < t) :
    ∀ m : ℕ, ((t : ℂ) / 2) ≠ -↑m

lemma digamma_continuousAt_real_half_pos {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun x : ℝ => digamma ((x : ℂ) / 2)) t

lemma digamma_comp_real_half_continuousOn_Ioo :
    ContinuousOn (fun x : ℝ => digamma ((x : ℂ) / 2)) (Set.Ioi 0)
```

For contour edges and parametrized complex paths:

```lean
lemma digamma_continuousOn_of_forall_im_ne_zero {S : Set ℂ}
    (hS : ∀ z ∈ S, z.im ≠ 0) :
    ContinuousOn digamma S

lemma continuousOn_topEdgeParam {T : ℝ} :
    ContinuousOn (fun x : ℝ => (x : ℂ) + T * Complex.I) (Set.Icc 0 1)

lemma digamma_comp_half_continuousOn_Icc {g : ℝ → ℂ} {S : Set ℝ}
    (hg : ContinuousOn g S) (him : ∀ x ∈ S, (g x / 2).im ≠ 0) :
    ContinuousOn (fun x => digamma (g x / 2)) S
```

The named edge wrappers are:

```lean
lemma digamma_top_edge_continuousOn_Icc {T : ℝ} (hT : 0 < T)
lemma digamma_right_tail_continuousOn_Icc (T : ℝ)
lemma digamma_left_tail_continuousOn_Icc (T : ℝ)
```

They are deliberately modest API lemmas.  Their purpose is to remove
repetitive pole-avoidance work from later contour packages.

---

## VI. Full Expansion

The final source block combines the previous layers.

The factor-only expansion is:

```lean
theorem entireXiLogDeriv_full_expansion_of_factors_ne_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hξ : entireXi s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) (hγ : Complex.Gammaℝ s ≠ 0)
    (hzeta : riemannZeta s ≠ 0) :
    entireXiLogDeriv s =
      1 / s + 1 / (s - 1) + gammaRFactorLogDeriv s + riemannZetaLogDeriv s
```

The regular-boundary version exposes exactly the hypotheses later supplied by
critical-box and safe-height arguments:

```lean
theorem entireXiLogDeriv_full_expansion_on_regular_boundary {T : ℝ} {s : ℂ}
    (hT : 0 < T) (hs_re : 0 ≤ s.re ∧ s.re ≤ 1) (hs_im : s.im = T)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hξ : entireXi s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) (hzeta : riemannZeta s ≠ 0) :
    entireXiLogDeriv s =
      1 / s + 1 / (s - 1) + gammaRFactorLogDeriv s + riemannZetaLogDeriv s
```

The digamma-substituted final form is:

```lean
theorem entireXiLogDeriv_full_expansion_with_digamma {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hξ : entireXi s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0) (hγ : Complex.Gammaℝ s ≠ 0)
    (hzeta : riemannZeta s ≠ 0) :
    entireXiLogDeriv s =
      1 / s + 1 / (s - 1) +
        (-(1 / 2) * log (Real.pi : ℂ) + (1 / 2) * digamma (s / 2)) +
          riemannZetaLogDeriv s
```

This is the main public theorem of the live file.

---

## VII. Conditional Frontiers

The package proves a glue layer, not a zero-free region.

The following hypotheses are mathematical frontiers intentionally left explicit:

- `hξ : entireXi s ≠ 0`
- `hΛ : completedRiemannZeta s ≠ 0`
- `hγ : Complex.Gammaℝ s ≠ 0`
- `hzeta : riemannZeta s ≠ 0`
- `hs0 : s ≠ 0`
- `hs1 : s ≠ 1`

This is the correct shape for a Mathlib-oriented API.  Later packages may
discharge these assumptions from contour conditions, safe heights, or
domain-specific zero-avoidance lemmas.  This package does not conceal those
responsibilities.

---

## VIII. Certificate

Command:

```text
printf 'import XiLogDeriv
#print axioms RiemannLogDeriv.logDeriv_entireXiPolynomialFactor_eq
#print axioms RiemannLogDeriv.Complex_Gammaℝ_ne_zero_of_im_ne_zero
#print axioms RiemannLogDeriv.gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma
#print axioms RiemannLogDeriv.digamma_top_edge_continuousOn_Icc
#print axioms RiemannLogDeriv.entireXiLogDeriv_full_expansion_with_digamma
' | lake env lean --stdin
```

Observed output:

```text
'RiemannLogDeriv.logDeriv_entireXiPolynomialFactor_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannLogDeriv.Complex_Gammaℝ_ne_zero_of_im_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannLogDeriv.gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RiemannLogDeriv.digamma_top_edge_continuousOn_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannLogDeriv.entireXiLogDeriv_full_expansion_with_digamma' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

No additional foundational dependency appears in these reported theorems.

---

## IX. Reading Guide

Read the live file in the same order as the source blocks.

First, `Basic.lean` establishes the local Xi object and proves the polynomial
part of the logarithmic derivative.

Second, `GammaR.lean` splits the completed zeta factor into `Gammaℝ` and
`riemannZeta`, then rewrites the Gamma-real logarithmic derivative with
`digamma`.

Third, `DigammaContinuity.lean` supplies the continuity API needed for
horizontal and vertical contour edges.

Fourth, `Expansion.lean` assembles the final theorem and the regular-boundary
variant.

The important discipline is that every analytic singularity is either avoided
by a named hypothesis or packaged in a lemma whose assumptions state the
avoidance condition directly.

---

## X. Verification

Compile the live file:

```text
lake env lean XiLogDerivLive/XiLogDeriv.live.lean
```

Build the package:

```text
lake build XiLogDeriv
```

Audit the live layer:

```text
rg -n "sor""ry|adm""it|native_dec""ide|^import Xi""LogDeriv|^public import Xi""LogDeriv" XiLogDerivLive/XiLogDeriv.live.lean
```

Expected live-layer files:

```text
XiLogDerivLive/XiLogDeriv.live.MANUAL.md
XiLogDerivLive/XiLogDeriv.live.lean
```
