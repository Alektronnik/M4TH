# DirichletEta.live

**Author:** Bezalel Izquierdo Pérez  
**License:** Apache 2.0  
**Live file:** `DirichletEta.live.lean`

---

## I. Purpose

This live file presents the complete `DirichletEta` package as a single Lean 4 source file.

The package isolates the Dirichlet eta function, its elementary relation with the Riemann zeta function in the half-plane `1 < re s`, the analytic API of the zeta-product normalization, and a conditional non-vanishing statement for `ζ(x)` on the real interval `0 < x < 1`.

The final non-vanishing theorem is deliberately conditional.  The bridge between the real alternating limit and the zeta-product identity is exposed as the named proposition

```lean
DirichletEta.RiemannZetaAlternatingLimitIdentity
```

Thus the package records the exact frontier required for the real interval argument instead of hiding it behind an unpublished dependency.

---

## II. Source Order

The live file is fused in the same dependency order as the library package.

```text
DirichletEta/Basic.lean
DirichletEta/Analytic.lean
DirichletEta/Nonvanishing.lean
```

The live version imports only Mathlib:

```lean
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic
```

It does not import the local package modules.

---

## III. Basic Eta API

The first layer defines the alternating term, the eta series, the zeta-product normalization, and finite eta partial sums.

```lean
noncomputable def etaTerm (n : ℕ) (s : ℂ) : ℂ :=
  (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s

noncomputable def dirichletEtaSeries (s : ℂ) : ℂ :=
  ∑' n, etaTerm n s

noncomputable def dirichletEta (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

noncomputable def etaPartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, etaTerm n s
```

The basic convergence and splitting lemmas are:

```lean
eta_summable_one_div_nat_add_one_cpow
eta_summable_odd_term
eta_summable_even_term
eta_zeta_odd_even_split
eta_even_zeta_term
eta_eq_zeta_of_re_gt_one
etaTerm_ofReal
```

The theorem

```lean
eta_eq_zeta_of_re_gt_one
```

proves the eta-zeta identity in the absolutely convergent half-plane:

```lean
dirichletEtaSeries s =
  (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s
```

under the hypothesis `1 < s.re`.

---

## IV. Analytic Layer

The second layer packages differentiability of finite eta components and analyticity of the zeta-product normalization away from the zeta pole.

```lean
etaTerm_differentiable
etaPartialSum_differentiable
etaTerm_norm_eq
analyticOn_etaZetaProduct
analyticOn_dirichletEta
dirichletEta_eq_zeta_of_re_pos
```

The main analytic statement is:

```lean
lemma analyticOn_dirichletEta :
    AnalyticOn ℂ dirichletEta {s | 0 < s.re ∧ s ≠ 1}
```

This is an API theorem for the product

```lean
(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s
```

on the punctured right half-plane.

---

## V. Positivity of the Alternating Real Series

The real eta-side positivity is proved directly from the alternating-series machinery.

```lean
lemma alternating_zeta_real_pos (x : ℝ) (hx0 : 0 < x) :
    ∃ l,
      Tendsto
        (fun n => ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i / (i + 1 : ℝ) ^ x)
        atTop (𝓝 l) ∧
        0 < l
```

This theorem supplies a positive limit for the alternating real series for every `x > 0`.

---

## VI. Conditional Non-Vanishing on `(0, 1)`

The continuation bridge is isolated as a proposition.

```lean
def RiemannZetaAlternatingLimitIdentity : Prop :=
  ∀ (x : ℝ), 0 < x → x ≠ 1 → ∀ l : ℝ,
    Tendsto
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i / (i + 1 : ℝ) ^ x)
      atTop (𝓝 l) →
    riemannZeta x * (1 - (2 : ℂ) ^ (1 - (x : ℂ))) = l
```

The non-vanishing result is then conditional on this bridge:

```lean
theorem riemannZeta_ne_zero_on_real_open_interval
    (hη : RiemannZetaAlternatingLimitIdentity)
    (x : ℝ) (hx0 : 0 < x) (hx1lt : x < 1) :
    riemannZeta x ≠ 0
```

The package-level form is:

```lean
theorem zeta_real_open_interval_nonvanishing_from_eta
    (hη : RiemannZetaAlternatingLimitIdentity) :
    ∀ x : ℝ, 0 < x → x < 1 → riemannZeta x ≠ 0
```

No unconditional non-vanishing theorem is claimed here.

---

## VII. Verification

Compile the live file directly:

```text
lake env lean DirichletEta/DirichletEtaLive/DirichletEta.live.lean
```

A clean run produces no output.

Check for forbidden local dependencies or unfinished proof markers:

```text
rg -n "public import DirichletEta|import DirichletEta|RiemannSynthesis|NavierStokesWeb|BirchSwinnertonDyerWeb|ErdosWeb|source corpus|mother formalization|unpublished formalization|formalizacion madre|formalización madre|\bsorry\b|\baxiom\b|admit|native_decide" DirichletEta/DirichletEtaLive/DirichletEta.live.lean
```

A clean run produces no output.

---

## VIII. Axiom Certificate

The following command records the trusted kernel base used by representative theorems:

```text
printf 'import DirichletEta
#print axioms DirichletEta.eta_eq_zeta_of_re_gt_one
#print axioms DirichletEta.analyticOn_dirichletEta
#print axioms DirichletEta.alternating_zeta_real_pos
#print axioms DirichletEta.zeta_real_open_interval_nonvanishing_from_eta
' | lake env lean --stdin
```

Expected output:

```text
'DirichletEta.eta_eq_zeta_of_re_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirichletEta.analyticOn_dirichletEta' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirichletEta.alternating_zeta_real_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirichletEta.zeta_real_open_interval_nonvanishing_from_eta' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is the standard Lean/Mathlib kernel base for the present classical development.
