/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import MertensPNT.MertensBridge

set_option linter.style.setOption false
set_option maxHeartbeats 800000

/-!
# Certified computational tables

This file preserves the kernel-checked TTAO, wheel-sieve and segmented-sieve
numerical certificates shipped with this package.
-/

/-! ### Certified finite tables -/

/-!
The constants in this section are stored directly in Lean.  This package ships
only the kernel-checkable layer:
exact finite identities and numerical brackets proved with `norm_num`.

# Empirical TTAO bridge in Lean

These finite certificates do not replace Mertens' theorem or PNT.  They are
published here as audited computational data points.
-/

set_option maxRecDepth 200000

@[expose] public section

namespace ErdosReciprocals

open Real

/-- Empirical proxy for `Δ(x) = (S - log log) - M` using `mertensConstantApprox`. -/
noncomputable def taoResidualProxy (sumMinusLogLog : ℝ) : ℝ :=
  sumMinusLogLog - mertensConstantApprox


/-! ## Exact Euler products at primorials -/
theorem primorial_survival_2 :
    (1 : ℝ) / 2 = (1 : ℝ) / 2 := by
  norm_num

theorem primorial_survival_6 :
    (2 : ℝ) / 6 = (1 : ℝ) / 3 := by
  norm_num

theorem primorial_euler_product_6 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3)
      = (1 : ℝ) / 3 := by
  norm_num

theorem primorial_survival_30 :
    (8 : ℝ) / 30 = (4 : ℝ) / 15 := by
  norm_num

theorem primorial_euler_product_30 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5)
      = (4 : ℝ) / 15 := by
  norm_num

theorem primorial_survival_210 :
    (48 : ℝ) / 210 = (8 : ℝ) / 35 := by
  norm_num

theorem primorial_euler_product_210 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7)
      = (8 : ℝ) / 35 := by
  norm_num

theorem primorial_survival_2310 :
    (480 : ℝ) / 2310 = (16 : ℝ) / 77 := by
  norm_num

theorem primorial_euler_product_2310 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7) *
      (1 - (1 : ℝ) / 11)
      = (16 : ℝ) / 77 := by
  norm_num

theorem primorial_survival_30030 :
    (5760 : ℝ) / 30030 = (192 : ℝ) / 1001 := by
  norm_num

theorem primorial_euler_product_30030 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7) *
      (1 - (1 : ℝ) / 11) * (1 - (1 : ℝ) / 13)
      = (192 : ℝ) / 1001 := by
  norm_num

theorem primorial_survival_510510 :
    (92160 : ℝ) / 510510 = (3072 : ℝ) / 17017 := by
  norm_num

theorem primorial_euler_product_510510 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7) *
      (1 - (1 : ℝ) / 11) * (1 - (1 : ℝ) / 13) * (1 - (1 : ℝ) / 17)
      = (3072 : ℝ) / 17017 := by
  norm_num

theorem primorial_survival_9699690 :
    (1658880 : ℝ) / 9699690 = (55296 : ℝ) / 323323 := by
  norm_num

theorem primorial_euler_product_9699690 :
    (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7) *
      (1 - (1 : ℝ) / 11) * (1 - (1 : ℝ) / 13) * (1 - (1 : ℝ) / 17) * (1 - (1 : ℝ) / 19)
      = (55296 : ℝ) / 323323 := by
  norm_num

/-! ## Wheel sieves (residuos coprimos y saltos C++) -/

/-! ### Wheel sieve mod 6 (`PATRONES/factorizador.cpp`) -/

def taoWheel6_modulus : ℕ := 6
def taoWheel6_phi : ℕ := 2
def taoWheel6_coprimeResidues : List ℕ :=
  [1, 5]

theorem taoWheel6_residue_count_eq_phi :
    taoWheel6_coprimeResidues.length = taoWheel6_phi := by
  rfl

theorem taoWheel6_survival_fraction :
    (taoWheel6_phi : ℝ) / taoWheel6_modulus =
      (2 : ℝ) / 6 := by
  unfold taoWheel6_phi taoWheel6_modulus
  norm_num

/-! ### Wheel sieve mod 30 (`PATRONES/factorizador.cpp`) -/

def taoWheel30_modulus : ℕ := 30
def taoWheel30_phi : ℕ := 8
def taoWheel30_coprimeResidues : List ℕ :=
  [1, 7, 11, 13, 17, 19, 23, 29]

theorem taoWheel30_residue_count_eq_phi :
    taoWheel30_coprimeResidues.length = taoWheel30_phi := by
  rfl

theorem taoWheel30_survival_fraction :
    (taoWheel30_phi : ℝ) / taoWheel30_modulus =
      (8 : ℝ) / 30 := by
  unfold taoWheel30_phi taoWheel30_modulus
  norm_num

def taoWheel30_jumpsDocumented : List ℕ :=
  [3, 2, 1, 2, 1, 2, 3, 1]

theorem taoWheel30_documented_jump_count_eq_phi :
    taoWheel30_jumpsDocumented.length = taoWheel30_phi := by
  rfl

theorem taoWheel30_documented_jumps_sum_eq_half_modulus :
    taoWheel30_jumpsDocumented.sum = taoWheel30_modulus / 2 := by
  unfold taoWheel30_jumpsDocumented taoWheel30_modulus
  decide

def taoWheel30_residueGaps : List ℕ :=
  [6, 4, 2, 4, 2, 4, 6, 2]

theorem taoWheel30_residue_gap_count_eq_phi :
    taoWheel30_residueGaps.length = taoWheel30_phi := by
  rfl

theorem taoWheel30_residue_gaps_sum_eq_modulus :
    taoWheel30_residueGaps.sum = taoWheel30_modulus := by
  unfold taoWheel30_residueGaps taoWheel30_modulus
  decide

/-! ### Wheel sieve mod 210 (`PATRONES/factorizador.cpp`) -/

def taoWheel210_modulus : ℕ := 210
def taoWheel210_phi : ℕ := 48
def taoWheel210_coprimeResidues : List ℕ :=
  [1, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103,
    107, 109, 113, 121, 127, 131, 137, 139, 143, 149, 151, 157,
    163, 167, 169, 173, 179, 181, 187, 191, 193, 197, 199, 209]

theorem taoWheel210_residue_count_eq_phi :
    taoWheel210_coprimeResidues.length = taoWheel210_phi := by
  rfl

theorem taoWheel210_survival_fraction :
    (taoWheel210_phi : ℝ) / taoWheel210_modulus =
      (48 : ℝ) / 210 := by
  unfold taoWheel210_phi taoWheel210_modulus
  norm_num

def taoWheel210_jumpsDocumented : List ℕ :=
  [5, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 3,
    3, 1, 3, 2, 1, 3, 2, 3, 4, 2, 1, 2,
    1, 2, 4, 3, 2, 3, 1, 2, 3, 1, 3, 3,
    2, 1, 2, 3, 1, 3, 2, 1, 2, 1, 5, 1]

theorem taoWheel210_documented_jump_count_eq_phi :
    taoWheel210_jumpsDocumented.length = taoWheel210_phi := by
  rfl

theorem taoWheel210_documented_jumps_sum_eq_half_modulus :
    taoWheel210_jumpsDocumented.sum = taoWheel210_modulus / 2 := by
  unfold taoWheel210_jumpsDocumented taoWheel210_modulus
  decide

def taoWheel210_residueGaps : List ℕ :=
  [10, 2, 4, 2, 4, 6, 2, 6, 4, 2, 4, 6,
    6, 2, 6, 4, 2, 6, 4, 6, 8, 4, 2, 4,
    2, 4, 8, 6, 4, 6, 2, 4, 6, 2, 6, 6,
    4, 2, 4, 6, 2, 6, 4, 2, 4, 2, 10, 2]

theorem taoWheel210_residue_gap_count_eq_phi :
    taoWheel210_residueGaps.length = taoWheel210_phi := by
  rfl

theorem taoWheel210_residue_gaps_sum_eq_modulus :
    taoWheel210_residueGaps.sum = taoWheel210_modulus := by
  unfold taoWheel210_residueGaps taoWheel210_modulus
  decide

/-! ## Tabla criba `CONJETURA-009-ERDOS/data/mertens_table.json` -/

/-- Límite de la criba segmentada (potencias de 10 hasta `10^11`). -/
def cribaTableLimit : ℕ := 100000000000
noncomputable def cribaTableFinalS : ℝ := 3.4934250719082645

/-- Criba segmentada: checkpoint `n = 1000`. -/
def cribaCp1000_n : ℕ := 1000
def cribaCp1000_pi : ℕ := 169
noncomputable def cribaCp1000_S : ℝ := 2.19907120745259
noncomputable def cribaCp1000_delta : ℝ := 0.004929260691740822
noncomputable def cribaCp1000_prod : ℝ := 0.08088502043101808
noncomputable def cribaCp1000_logLog : ℝ := 1.9326447339160655

theorem cribaCp1000_S_bracket :
    (2199071207451 : ℝ) / 1000000000000 < cribaCp1000_S ∧
      cribaCp1000_S < (1099535603727 : ℝ) / 500000000000 := by
  constructor <;> unfold cribaCp1000_S <;> norm_num

theorem cribaCp1000_delta_bracket :
    (492926069 : ℝ) / 100000000000 < cribaCp1000_delta ∧
      cribaCp1000_delta < (4929260693 : ℝ) / 1000000000000 := by
  constructor <;> unfold cribaCp1000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 10000`. -/
def cribaCp10000_n : ℕ := 10000
def cribaCp10000_pi : ℕ := 1230
noncomputable def cribaCp10000_S : ℝ := 2.4831598772825303
noncomputable def cribaCp10000_delta : ℝ := 0.0013358580699001088
noncomputable def cribaCp10000_prod : ℝ := 0.06087860824553999
noncomputable def cribaCp10000_logLog : ℝ := 2.2203268063678463

theorem cribaCp10000_S_bracket :
    (2483159877281 : ℝ) / 1000000000000 < cribaCp10000_S ∧
      cribaCp10000_S < (620789969321 : ℝ) / 250000000000 := by
  constructor <;> unfold cribaCp10000_S <;> norm_num

theorem cribaCp10000_delta_bracket :
    (333964517 : ℝ) / 250000000000 < cribaCp10000_delta ∧
      cribaCp10000_delta < (1335858071 : ℝ) / 1000000000000 := by
  constructor <;> unfold cribaCp10000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 100000`. -/
def cribaCp100000_n : ℕ := 100000
def cribaCp100000_pi : ℕ := 9593
noncomputable def cribaCp100000_S : ℝ := 2.70528217874729
noncomputable def cribaCp100000_delta : ℝ := 0.0003146082204499301
noncomputable def cribaCp100000_prod : ℝ := 0.04875243033646201
noncomputable def cribaCp100000_logLog : ℝ := 2.443470357682056

theorem cribaCp100000_S_bracket :
    (1352641089373 : ℝ) / 500000000000 < cribaCp100000_S ∧
      cribaCp100000_S < (2705282178749 : ℝ) / 1000000000000 := by
  constructor <;> unfold cribaCp100000_S <;> norm_num

theorem cribaCp100000_delta_bracket :
    (314608219 : ℝ) / 1000000000000 < cribaCp100000_delta ∧
      cribaCp100000_delta < (157304111 : ℝ) / 500000000000 := by
  constructor <;> unfold cribaCp100000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 1000000`. -/
def cribaCp1000000_n : ℕ := 1000000
def cribaCp1000000_pi : ℕ := 78499
noncomputable def cribaCp1000000_S : ℝ := 2.8873290995646936
noncomputable def cribaCp1000000_delta : ℝ := 3.9972243898844795e-05
noncomputable def cribaCp1000000_prod : ℝ := 0.04063816953356033
noncomputable def cribaCp1000000_logLog : ℝ := 2.625791914476011

theorem cribaCp1000000_S_bracket :
    (2887329099563 : ℝ) / 1000000000000 < cribaCp1000000_S ∧
      cribaCp1000000_S < (1443664549783 : ℝ) / 500000000000 := by
  constructor <;> unfold cribaCp1000000_S <;> norm_num

theorem cribaCp1000000_delta_bracket :
    (399721 : ℝ) / 10000000000 < cribaCp1000000_delta ∧
      cribaCp1000000_delta < (99931 : ℝ) / 2500000000 := by
  constructor <;> unfold cribaCp1000000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 10000000`. -/
def cribaCp10000000_n : ℕ := 10000000
def cribaCp10000000_pi : ℕ := 664580
noncomputable def cribaCp10000000_S : ℝ := 3.0414494812793724
noncomputable def cribaCp10000000_delta : ℝ := 9.674131319581392e-06
noncomputable def cribaCp10000000_prod : ℝ := 0.03483377104624719
noncomputable def cribaCp10000000_logLog : ℝ := 2.779942594303269

theorem cribaCp10000000_S_bracket :
    (1520724740639 : ℝ) / 500000000000 < cribaCp10000000_S ∧
      cribaCp10000000_S < (3041449481281 : ℝ) / 1000000000000 := by
  constructor <;> unfold cribaCp10000000_S <;> norm_num

theorem cribaCp10000000_delta_bracket :
    (4837 : ℝ) / 500000000 < cribaCp10000000_delta ∧
      cribaCp10000000_delta < (96743 : ℝ) / 10000000000 := by
  constructor <;> unfold cribaCp10000000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 100000000`. -/
def cribaCp100000000_n : ℕ := 100000000
def cribaCp100000000_pi : ℕ := 5761456
noncomputable def cribaCp100000000_S : ℝ := 3.1749752399205624
noncomputable def cribaCp100000000_delta : ℝ := 4.040147986827947e-06
noncomputable def cribaCp100000000_prod : ℝ := 0.030479721305794072
noncomputable def cribaCp100000000_logLog : ℝ := 2.9134739869277917

theorem cribaCp100000000_S_bracket :
    (3174975239919 : ℝ) / 1000000000000 < cribaCp100000000_S ∧
      cribaCp100000000_S < (1587487619961 : ℝ) / 500000000000 := by
  constructor <;> unfold cribaCp100000000_S <;> norm_num

theorem cribaCp100000000_delta_bracket :
    (101 : ℝ) / 25000000 < cribaCp100000000_delta ∧
      cribaCp100000000_delta < (40403 : ℝ) / 10000000000 := by
  constructor <;> unfold cribaCp100000000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 1000000000`. -/
def cribaCp1000000000_n : ℕ := 1000000000
def cribaCp1000000000_pi : ℕ := 50847535
noncomputable def cribaCp1000000000_S : ℝ := 3.292755719800315
noncomputable def cribaCp1000000000_delta : ℝ := 1.4843713560530603e-06
noncomputable def cribaCp1000000000_prod : ℝ := 0.027093154842787338
noncomputable def cribaCp1000000000_logLog : ℝ := 3.031257022584175

theorem cribaCp1000000000_S_bracket :
    (3292755719799 : ℝ) / 1000000000000 < cribaCp1000000000_S ∧
      cribaCp1000000000_S < (1646377859901 : ℝ) / 500000000000 := by
  constructor <;> unfold cribaCp1000000000_S <;> norm_num

theorem cribaCp1000000000_delta_bracket :
    (7421 : ℝ) / 5000000000 < cribaCp1000000000_delta ∧
      cribaCp1000000000_delta < (2969 : ℝ) / 2000000000 := by
  constructor <;> unfold cribaCp1000000000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 10000000000`. -/
def cribaCp10000000000_n : ℕ := 10000000000
def cribaCp10000000000_pi : ℕ := 455052512
noncomputable def cribaCp10000000000_S : ℝ := 3.3981153423420314
noncomputable def cribaCp10000000000_delta : ℝ := 5.912552460962672e-07
noncomputable def cribaCp10000000000_prod : ℝ := 0.024383861135675634
noncomputable def cribaCp10000000000_logLog : ℝ := 3.1366175382420014

theorem cribaCp10000000000_S_bracket :
    (3398115342341 : ℝ) / 1000000000000 < cribaCp10000000000_S ∧
      cribaCp10000000000_S < (424764417793 : ℝ) / 125000000000 := by
  constructor <;> unfold cribaCp10000000000_S <;> norm_num

theorem cribaCp10000000000_delta_bracket :
    (5911 : ℝ) / 10000000000 < cribaCp10000000000_delta ∧
      cribaCp10000000000_delta < (2957 : ℝ) / 5000000000 := by
  constructor <;> unfold cribaCp10000000000_delta <;> norm_num

/-- Criba segmentada: checkpoint `n = 100000000000`. -/
def cribaCp100000000000_n : ℕ := 100000000000
def cribaCp100000000000_pi : ℕ := 4118054813
noncomputable def cribaCp100000000000_S : ℝ := 3.4934250719082645
noncomputable def cribaCp100000000000_delta : ℝ := 1.4101715395398173e-07
noncomputable def cribaCp100000000000_prod : ℝ := 0.022167156466509352
noncomputable def cribaCp100000000000_logLog : ℝ := 3.2319277180463266

theorem cribaCp100000000000_S_bracket :
    (3493425071907 : ℝ) / 1000000000000 < cribaCp100000000000_S ∧
      cribaCp100000000000_S < (349342507191 : ℝ) / 100000000000 := by
  constructor <;> unfold cribaCp100000000000_S <;> norm_num

theorem cribaCp100000000000_delta_bracket :
    (1409 : ℝ) / 10000000000 < cribaCp100000000000_delta ∧
      cribaCp100000000000_delta < (353 : ℝ) / 2500000000 := by
  constructor <;> unfold cribaCp100000000000_delta <;> norm_num

/-! ## Tendencia criba: `S(n)` ↑ y `Δ` ↓ en potencias de 10 -/

theorem criba_delta_tightens_1e3_to_1e11 :
    cribaCp100000000000_delta < cribaCp1000_delta := by
  unfold cribaCp100000000000_delta cribaCp1000_delta
  norm_num

theorem cribaCp100000000000_delta_lt_micro :
    cribaCp100000000000_delta < (1 / 1000000 : ℝ) := by
  unfold cribaCp100000000000_delta
  norm_num

theorem cribaCp100000000000_S_gt_cribaCp1000_S :
    cribaCp1000_S < cribaCp100000000000_S := by
  unfold cribaCp1000_S cribaCp100000000000_S
  norm_num

theorem cribaCp10000_S_gt_cribaCp1000_S :
    cribaCp1000_S < cribaCp10000_S := by
  unfold cribaCp1000_S cribaCp10000_S
  norm_num

theorem cribaCp10000_delta_lt_cribaCp1000_delta :
    cribaCp10000_delta < cribaCp1000_delta := by
  unfold cribaCp1000_delta cribaCp10000_delta
  norm_num

theorem cribaCp100000_S_gt_cribaCp10000_S :
    cribaCp10000_S < cribaCp100000_S := by
  unfold cribaCp10000_S cribaCp100000_S
  norm_num

theorem cribaCp100000_delta_lt_cribaCp10000_delta :
    cribaCp100000_delta < cribaCp10000_delta := by
  unfold cribaCp10000_delta cribaCp100000_delta
  norm_num

theorem cribaCp1000000_S_gt_cribaCp100000_S :
    cribaCp100000_S < cribaCp1000000_S := by
  unfold cribaCp100000_S cribaCp1000000_S
  norm_num

theorem cribaCp1000000_delta_lt_cribaCp100000_delta :
    cribaCp1000000_delta < cribaCp100000_delta := by
  unfold cribaCp100000_delta cribaCp1000000_delta
  norm_num

theorem cribaCp10000000_S_gt_cribaCp1000000_S :
    cribaCp1000000_S < cribaCp10000000_S := by
  unfold cribaCp1000000_S cribaCp10000000_S
  norm_num

theorem cribaCp10000000_delta_lt_cribaCp1000000_delta :
    cribaCp10000000_delta < cribaCp1000000_delta := by
  unfold cribaCp1000000_delta cribaCp10000000_delta
  norm_num

theorem cribaCp100000000_S_gt_cribaCp10000000_S :
    cribaCp10000000_S < cribaCp100000000_S := by
  unfold cribaCp10000000_S cribaCp100000000_S
  norm_num

theorem cribaCp100000000_delta_lt_cribaCp10000000_delta :
    cribaCp100000000_delta < cribaCp10000000_delta := by
  unfold cribaCp10000000_delta cribaCp100000000_delta
  norm_num

theorem cribaCp1000000000_S_gt_cribaCp100000000_S :
    cribaCp100000000_S < cribaCp1000000000_S := by
  unfold cribaCp100000000_S cribaCp1000000000_S
  norm_num

theorem cribaCp1000000000_delta_lt_cribaCp100000000_delta :
    cribaCp1000000000_delta < cribaCp100000000_delta := by
  unfold cribaCp100000000_delta cribaCp1000000000_delta
  norm_num

theorem cribaCp10000000000_S_gt_cribaCp1000000000_S :
    cribaCp1000000000_S < cribaCp10000000000_S := by
  unfold cribaCp1000000000_S cribaCp10000000000_S
  norm_num

theorem cribaCp10000000000_delta_lt_cribaCp1000000000_delta :
    cribaCp10000000000_delta < cribaCp1000000000_delta := by
  unfold cribaCp1000000000_delta cribaCp10000000000_delta
  norm_num

theorem cribaCp100000000000_S_gt_cribaCp10000000000_S :
    cribaCp10000000000_S < cribaCp100000000000_S := by
  unfold cribaCp10000000000_S cribaCp100000000000_S
  norm_num

theorem cribaCp100000000000_delta_lt_cribaCp10000000000_delta :
    cribaCp100000000000_delta < cribaCp10000000000_delta := by
  unfold cribaCp10000000000_delta cribaCp100000000000_delta
  norm_num

/-! ## Serie acumulativa `low_from_2` (1k … 10k primos desde 2) -/

/-- Checkpoint: x = 7919, 1000 primos en ventana. -/
def taoCheckpointX_7919 : ℕ := 7919

noncomputable def taoCp7919_sumOneOverP : ℝ := 2.457411276711362
noncomputable def taoCp7919_logLogX : ℝ := 2.194668002549939
noncomputable def taoCp7919_sumMinusLogLog : ℝ := 0.26274327416142285
noncomputable def taoCp7919_partialProduct : ℝ := 0.062466592946666254
noncomputable def taoCp7919_prodOverHeuristic : ℝ := 0.9987610575790983
noncomputable def taoCp7919_residualProxy : ℝ := 0.0012460613166390133

theorem taoCp7919_sumMinusLogLog_bracket :
    (3284290927 : ℝ) / 12500000000 < taoCp7919_sumMinusLogLog ∧
      taoCp7919_sumMinusLogLog < (262743274163 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoCp7919_sumMinusLogLog <;> norm_num

theorem taoCp7919_residualProxy_pos : 0 < taoCp7919_residualProxy := by
  unfold taoCp7919_residualProxy
  norm_num

theorem taoCp7919_residualProxy_bracket :
    (3115153 : ℝ) / 2500000000 < taoCp7919_residualProxy ∧
      taoCp7919_residualProxy < (2492123 : ℝ) / 2000000000 := by
  unfold taoCp7919_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 17389, 2000 primos en ventana. -/
def taoCheckpointX_17389 : ℕ := 17389

noncomputable def taoCp17389_sumOneOverP : ℝ := 2.5408915524876656
noncomputable def taoCp17389_logLogX : ℝ := 2.2786604783094333
noncomputable def taoCp17389_sumMinusLogLog : ℝ := 0.2622310741782323
noncomputable def taoCp17389_partialProduct : ℝ := 0.057463384743108595
noncomputable def taoCp17389_prodOverHeuristic : ℝ := 0.9992690893661653
noncomputable def taoCp17389_residualProxy : ℝ := 0.0007338613334484934

theorem taoCp17389_sumMinusLogLog_bracket :
    (262231074177 : ℝ) / 1000000000000 < taoCp17389_sumMinusLogLog ∧
      taoCp17389_sumMinusLogLog < (13111553709 : ℝ) / 50000000000 := by
  constructor <;> unfold taoCp17389_sumMinusLogLog <;> norm_num

theorem taoCp17389_residualProxy_pos : 0 < taoCp17389_residualProxy := by
  unfold taoCp17389_residualProxy
  norm_num

theorem taoCp17389_residualProxy_bracket :
    (1834653 : ℝ) / 2500000000 < taoCp17389_residualProxy ∧
      taoCp17389_residualProxy < (1467723 : ℝ) / 2000000000 := by
  unfold taoCp17389_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 27449, 3000 primos en ventana. -/
def taoCheckpointX_27449 : ℕ := 27449

noncomputable def taoCp27449_sumOneOverP : ℝ := 2.5863620272696917
noncomputable def taoCp27449_logLogX : ℝ := 2.324354903371252
noncomputable def taoCp27449_sumMinusLogLog : ℝ := 0.2620071238984396
noncomputable def taoCp27449_partialProduct : ℝ := 0.05490895397799993
noncomputable def taoCp27449_prodOverHeuristic : ℝ := 0.9994918497979041
noncomputable def taoCp27449_residualProxy : ℝ := 0.000509911053655776

theorem taoCp27449_sumMinusLogLog_bracket :
    (262007123897 : ℝ) / 1000000000000 < taoCp27449_sumMinusLogLog ∧
      taoCp27449_sumMinusLogLog < (2620071239 : ℝ) / 10000000000 := by
  constructor <;> unfold taoCp27449_sumMinusLogLog <;> norm_num

theorem taoCp27449_residualProxy_pos : 0 < taoCp27449_residualProxy := by
  unfold taoCp27449_residualProxy
  norm_num

theorem taoCp27449_residualProxy_bracket :
    (5099109 : ℝ) / 10000000000 < taoCp27449_residualProxy ∧
      taoCp27449_residualProxy < (637389 : ℝ) / 1250000000 := by
  unfold taoCp27449_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 37813, 4000 primos en ventana. -/
def taoCheckpointX_37813 : ℕ := 37813

noncomputable def taoCp37813_sumOneOverP : ℝ := 2.61727832686903
noncomputable def taoCp37813_logLogX : ℝ := 2.355216274604724
noncomputable def taoCp37813_sumMinusLogLog : ℝ := 0.262062052264306
noncomputable def taoCp37813_partialProduct : ℝ := 0.053237319763928294
noncomputable def taoCp37813_prodOverHeuristic : ℝ := 0.9994364691012536
noncomputable def taoCp37813_residualProxy : ℝ := 0.0005648394195221784

theorem taoCp37813_sumMinusLogLog_bracket :
    (262062052263 : ℝ) / 1000000000000 < taoCp37813_sumMinusLogLog ∧
      taoCp37813_sumMinusLogLog < (131031026133 : ℝ) / 500000000000 := by
  constructor <;> unfold taoCp37813_sumMinusLogLog <;> norm_num

theorem taoCp37813_residualProxy_pos : 0 < taoCp37813_residualProxy := by
  unfold taoCp37813_residualProxy
  norm_num

theorem taoCp37813_residualProxy_bracket :
    (5648393 : ℝ) / 10000000000 < taoCp37813_residualProxy ∧
      taoCp37813_residualProxy < (1412099 : ℝ) / 2500000000 := by
  unfold taoCp37813_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 48611, 5000 primos en ventana. -/
def taoCheckpointX_48611 : ℕ := 48611

noncomputable def taoCp48611_sumOneOverP : ℝ := 2.6405528434271104
noncomputable def taoCp48611_logLogX : ℝ := 2.3787685283293087
noncomputable def taoCp48611_sumMinusLogLog : ℝ := 0.26178431509780165
noncomputable def taoCp48611_partialProduct : ℝ := 0.05201254091326835
noncomputable def taoCp48611_prodOverHeuristic : ℝ := 0.9997138161204105
noncomputable def taoCp48611_residualProxy : ℝ := 0.00028710225301781245

theorem taoCp48611_sumMinusLogLog_bracket :
    (32723039387 : ℝ) / 125000000000 < taoCp48611_sumMinusLogLog ∧
      taoCp48611_sumMinusLogLog < (261784315099 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoCp48611_sumMinusLogLog <;> norm_num

theorem taoCp48611_residualProxy_pos : 0 < taoCp48611_residualProxy := by
  unfold taoCp48611_residualProxy
  norm_num

theorem taoCp48611_residualProxy_bracket :
    (2871021 : ℝ) / 10000000000 < taoCp48611_residualProxy ∧
      taoCp48611_residualProxy < (179439 : ℝ) / 625000000 := by
  unfold taoCp48611_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 59359, 6000 primos en ventana. -/
def taoCheckpointX_59359 : ℕ := 59359

noncomputable def taoCp59359_sumOneOverP : ℝ := 2.6591357546549808
noncomputable def taoCp59359_logLogX : ℝ := 2.397109421492482
noncomputable def taoCp59359_sumMinusLogLog : ℝ := 0.26202633316249857
noncomputable def taoCp59359_partialProduct : ℝ := 0.051054912871272944
noncomputable def taoCp59359_prodOverHeuristic : ℝ := 0.9994717234391494
noncomputable def taoCp59359_residualProxy : ℝ := 0.0005291203177147374

theorem taoCp59359_sumMinusLogLog_bracket :
    (262026333161 : ℝ) / 1000000000000 < taoCp59359_sumMinusLogLog ∧
      taoCp59359_sumMinusLogLog < (65506583291 : ℝ) / 250000000000 := by
  constructor <;> unfold taoCp59359_sumMinusLogLog <;> norm_num

theorem taoCp59359_residualProxy_pos : 0 < taoCp59359_residualProxy := by
  unfold taoCp59359_residualProxy
  norm_num

theorem taoCp59359_residualProxy_bracket :
    (2645601 : ℝ) / 5000000000 < taoCp59359_residualProxy ∧
      taoCp59359_residualProxy < (1058241 : ℝ) / 2000000000 := by
  unfold taoCp59359_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 70657, 7000 primos en ventana. -/
def taoCheckpointX_70657 : ℕ := 70657

noncomputable def taoCp70657_sumOneOverP : ℝ := 2.6745562902631397
noncomputable def taoCp70657_logLogX : ℝ := 2.4128369482081533
noncomputable def taoCp70657_sumMinusLogLog : ℝ := 0.26171934205498637
noncomputable def taoCp70657_partialProduct : ℝ := 0.05027365194295217
noncomputable def taoCp70657_prodOverHeuristic : ℝ := 0.99977848030009
noncomputable def taoCp70657_residualProxy : ℝ := 0.0002221292102025374

theorem taoCp70657_sumMinusLogLog_bracket :
    (261719342053 : ℝ) / 1000000000000 < taoCp70657_sumMinusLogLog ∧
      taoCp70657_sumMinusLogLog < (32714917757 : ℝ) / 125000000000 := by
  constructor <;> unfold taoCp70657_sumMinusLogLog <;> norm_num

theorem taoCp70657_residualProxy_pos : 0 < taoCp70657_residualProxy := by
  unfold taoCp70657_residualProxy
  norm_num

theorem taoCp70657_residualProxy_bracket :
    (2221291 : ℝ) / 10000000000 < taoCp70657_residualProxy ∧
      taoCp70657_residualProxy < (1110647 : ℝ) / 5000000000 := by
  unfold taoCp70657_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 81799, 8000 primos en ventana. -/
def taoCheckpointX_81799 : ℕ := 81799

noncomputable def taoCp81799_sumOneOverP : ℝ := 2.687700665463508
noncomputable def taoCp81799_logLogX : ℝ := 2.425865903492886
noncomputable def taoCp81799_sumMinusLogLog : ℝ := 0.2618347619706216
noncomputable def taoCp81799_partialProduct : ℝ := 0.04961715594371256
noncomputable def taoCp81799_prodOverHeuristic : ℝ := 0.9996630060955574
noncomputable def taoCp81799_residualProxy : ℝ := 0.0003375491258377772

theorem taoCp81799_sumMinusLogLog_bracket :
    (261834761969 : ℝ) / 1000000000000 < taoCp81799_sumMinusLogLog ∧
      taoCp81799_sumMinusLogLog < (65458690493 : ℝ) / 250000000000 := by
  constructor <;> unfold taoCp81799_sumMinusLogLog <;> norm_num

theorem taoCp81799_residualProxy_pos : 0 < taoCp81799_residualProxy := by
  unfold taoCp81799_residualProxy
  norm_num

theorem taoCp81799_residualProxy_bracket :
    (337549 : ℝ) / 1000000000 < taoCp81799_residualProxy ∧
      taoCp81799_residualProxy < (3375493 : ℝ) / 10000000000 := by
  unfold taoCp81799_residualProxy
  constructor <;> norm_num

/-- Checkpoint: x = 93179, 9000 primos en ventana. -/
def taoCheckpointX_93179 : ℕ := 93179

noncomputable def taoCp93179_sumOneOverP : ℝ := 2.6991401810819573
noncomputable def taoCp93179_logLogX : ℝ := 2.4373150617113732
noncomputable def taoCp93179_sumMinusLogLog : ℝ := 0.26182511937058406
noncomputable def taoCp93179_partialProduct : ℝ := 0.04905279066790089
noncomputable def taoCp93179_prodOverHeuristic : ℝ := 0.999672579988035
noncomputable def taoCp93179_residualProxy : ℝ := 0.0003279065258002256

theorem taoCp93179_sumMinusLogLog_bracket :
    (261825119369 : ℝ) / 1000000000000 < taoCp93179_sumMinusLogLog ∧
      taoCp93179_sumMinusLogLog < (65456279843 : ℝ) / 250000000000 := by
  constructor <;> unfold taoCp93179_sumMinusLogLog <;> norm_num

theorem taoCp93179_residualProxy_pos : 0 < taoCp93179_residualProxy := by
  unfold taoCp93179_residualProxy
  norm_num

theorem taoCp93179_residualProxy_bracket :
    (409883 : ℝ) / 1250000000 < taoCp93179_residualProxy ∧
      taoCp93179_residualProxy < (3279067 : ℝ) / 10000000000 := by
  unfold taoCp93179_residualProxy
  constructor <;> norm_num

/-- Checkpoint principal: x = 104729. -/
def taoCheckpointX : ℕ := 104729

noncomputable def taoCp104729_sumOneOverP : ℝ := 2.709258248797317
noncomputable def taoCp104729_logLogX : ℝ := 2.4474757168532646
noncomputable def taoCp104729_sumMinusLogLog : ℝ := 0.26178253194405254
noncomputable def taoCp104729_partialProduct : ℝ := 0.048558971171659714
noncomputable def taoCp104729_prodOverHeuristic : ℝ := 0.9997151031452159
noncomputable def taoCp104729_residualProxy : ℝ := 0.00028531909926871046

theorem taoCp104729_sumMinusLogLog_bracket :
    (261782531943 : ℝ) / 1000000000000 < taoCp104729_sumMinusLogLog ∧
      taoCp104729_sumMinusLogLog < (130891265973 : ℝ) / 500000000000 := by
  constructor <;> unfold taoCp104729_sumMinusLogLog <;> norm_num

theorem taoCp104729_residualProxy_pos : 0 < taoCp104729_residualProxy := by
  unfold taoCp104729_residualProxy
  norm_num

theorem taoCp104729_residualProxy_bracket :
    (2853189 : ℝ) / 10000000000 < taoCp104729_residualProxy ∧
      taoCp104729_residualProxy < (356649 : ℝ) / 1250000000 := by
  unfold taoCp104729_residualProxy
  constructor <;> norm_num

theorem taoEmpiricalSumMinusLogLog_near_mertensConstantApprox :
    |taoCp104729_sumMinusLogLog - mertensConstantApprox| < (1 / 1000 : ℝ) := by
  unfold taoCp104729_sumMinusLogLog mertensConstantApprox
  norm_num

/-- Heurística Tao: `∏ / (e^{-γ}/log x) ≈ 1` en x = 104729. -/
theorem taoEmpiricalProdOverHeuristic_near_one :
    (999715103 : ℝ) / 1000000000 < taoCp104729_prodOverHeuristic ∧
      taoCp104729_prodOverHeuristic < (9997151033 : ℝ) / 10000000000 := by
  constructor <;> unfold taoCp104729_prodOverHeuristic <;> norm_num

/-! ## Ventana local `high_from_10M` (10k primos desde 10M) -/

/-- Checkpoint (suma local, no acumulativa): x = 10016051, 1000 primos en ventana. -/
def taoCheckpointX_High10M_10016051 : ℕ := 10016051

noncomputable def taoHigh10M_Cp10016051_sumOneOverP : ℝ := 9.991925549458609e-05
noncomputable def taoHigh10M_Cp10016051_logLogX : ℝ := 2.7800420932422854
noncomputable def taoHigh10M_Cp10016051_sumMinusLogLog : ℝ := -2.779942173986791
noncomputable def taoHigh10M_Cp10016051_partialProduct : ℝ := 0.9999000857312778
noncomputable def taoHigh10M_Cp10016051_prodOverHeuristic : ℝ := 28.707483528075453
noncomputable def taoHigh10M_Cp10016051_residualProxy : ℝ := -3.0414393868315748

theorem taoHigh10M_Cp10016051_sumMinusLogLog_bracket :
    (-2779942173987 : ℝ) / 1000000000000 < taoHigh10M_Cp10016051_sumMinusLogLog ∧
      taoHigh10M_Cp10016051_sumMinusLogLog < (-86873192937 : ℝ) / 31250000000 := by
  constructor <;> unfold taoHigh10M_Cp10016051_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10016051_residualProxy_neg : taoHigh10M_Cp10016051_residualProxy < 0 := by
  unfold taoHigh10M_Cp10016051_residualProxy
  norm_num

theorem taoHigh10M_Cp10016051_residualProxy_bracket :
    (-30414393869 : ℝ) / 10000000000 < taoHigh10M_Cp10016051_residualProxy ∧
      taoHigh10M_Cp10016051_residualProxy < (-15207196933 : ℝ) / 5000000000 := by
  unfold taoHigh10M_Cp10016051_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10032181, 2000 primos en ventana. -/
def taoCheckpointX_High10M_10032181 : ℕ := 10032181

noncomputable def taoHigh10M_Cp10032181_sumOneOverP : ℝ := 0.00019967937720542848
noncomputable def taoHigh10M_Cp10032181_logLogX : ℝ := 2.78014191144857
noncomputable def taoHigh10M_Cp10032181_sumMinusLogLog : ℝ := -2.7799422320713645
noncomputable def taoHigh10M_Cp10032181_partialProduct : ℝ := 0.9998003405474292
noncomputable def taoHigh10M_Cp10032181_prodOverHeuristic : ℝ := 28.707485195394568
noncomputable def taoHigh10M_Cp10032181_residualProxy : ℝ := -3.0414394449161484

theorem taoHigh10M_Cp10032181_sumMinusLogLog_bracket :
    (-347492779009 : ℝ) / 125000000000 < taoHigh10M_Cp10032181_sumMinusLogLog ∧
      taoHigh10M_Cp10032181_sumMinusLogLog < (-2779942232069 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoHigh10M_Cp10032181_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10032181_residualProxy_neg : taoHigh10M_Cp10032181_residualProxy < 0 := by
  unfold taoHigh10M_Cp10032181_residualProxy
  norm_num

theorem taoHigh10M_Cp10032181_residualProxy_bracket :
    (-608287889 : ℝ) / 200000000 < taoHigh10M_Cp10032181_residualProxy ∧
      taoHigh10M_Cp10032181_residualProxy < (-30414394447 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10032181_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10047881, 3000 primos en ventana. -/
def taoCheckpointX_High10M_10047881 : ℕ := 10047881

noncomputable def taoHigh10M_Cp10047881_sumOneOverP : ℝ := 0.00029928090284024004
noncomputable def taoHigh10M_Cp10047881_logLogX : ℝ := 2.7802389051055623
noncomputable def taoHigh10M_Cp10047881_sumMinusLogLog : ℝ := -2.779939624202722
noncomputable def taoHigh10M_Cp10047881_partialProduct : ℝ := 0.9997007638622997
noncomputable def taoHigh10M_Cp10047881_prodOverHeuristic : ℝ := 28.707410329999373
noncomputable def taoHigh10M_Cp10047881_residualProxy : ℝ := -3.041436837047506

theorem taoHigh10M_Cp10047881_sumMinusLogLog_bracket :
    (-2779939624203 : ℝ) / 1000000000000 < taoHigh10M_Cp10047881_sumMinusLogLog ∧
      taoHigh10M_Cp10047881_sumMinusLogLog < (-13899698121 : ℝ) / 5000000000 := by
  constructor <;> unfold taoHigh10M_Cp10047881_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10047881_residualProxy_neg : taoHigh10M_Cp10047881_residualProxy < 0 := by
  unfold taoHigh10M_Cp10047881_residualProxy
  norm_num

theorem taoHigh10M_Cp10047881_residualProxy_bracket :
    (-30414368371 : ℝ) / 10000000000 < taoHigh10M_Cp10047881_residualProxy ∧
      taoHigh10M_Cp10047881_residualProxy < (-1900898023 : ℝ) / 625000000 := by
  unfold taoHigh10M_Cp10047881_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10063771, 4000 primos en ventana. -/
def taoCheckpointX_High10M_10063771 : ℕ := 10063771

noncomputable def taoHigh10M_Cp10063771_sumOneOverP : ℝ := 0.0003987251876420962
noncomputable def taoHigh10M_Cp10063771_logLogX : ℝ := 2.7803369088211594
noncomputable def taoHigh10M_Cp10063771_sumMinusLogLog : ℝ := -2.7799381836335173
noncomputable def taoHigh10M_Cp10063771_partialProduct : ℝ := 0.9996013542728166
noncomputable def taoHigh10M_Cp10063771_prodOverHeuristic : ℝ := 28.707368974875905
noncomputable def taoHigh10M_Cp10063771_residualProxy : ℝ := -3.041435396478301

theorem taoHigh10M_Cp10063771_sumMinusLogLog_bracket :
    (-1389969091817 : ℝ) / 500000000000 < taoHigh10M_Cp10063771_sumMinusLogLog ∧
      taoHigh10M_Cp10063771_sumMinusLogLog < (-2779938183631 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoHigh10M_Cp10063771_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10063771_residualProxy_neg : taoHigh10M_Cp10063771_residualProxy < 0 := by
  unfold taoHigh10M_Cp10063771_residualProxy
  norm_num

theorem taoHigh10M_Cp10063771_residualProxy_bracket :
    (-6082870793 : ℝ) / 2000000000 < taoHigh10M_Cp10063771_residualProxy ∧
      taoHigh10M_Cp10063771_residualProxy < (-15207176981 : ℝ) / 5000000000 := by
  unfold taoHigh10M_Cp10063771_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10080061, 5000 primos en ventana. -/
def taoCheckpointX_High10M_10080061 : ℕ := 10080061

noncomputable def taoHigh10M_Cp10080061_sumOneOverP : ℝ := 0.0004980100294140917
noncomputable def taoHigh10M_Cp10080061_logLogX : ℝ := 2.7804372091429688
noncomputable def taoHigh10M_Cp10080061_sumMinusLogLog : ℝ := -2.7799391991135547
noncomputable def taoHigh10M_Cp10080061_partialProduct : ℝ := 0.9995021139322078
noncomputable def taoHigh10M_Cp10080061_prodOverHeuristic : ℝ := 28.707398126509318
noncomputable def taoHigh10M_Cp10080061_residualProxy : ℝ := -3.0414364119583386

theorem taoHigh10M_Cp10080061_sumMinusLogLog_bracket :
    (-1389969599557 : ℝ) / 500000000000 < taoHigh10M_Cp10080061_sumMinusLogLog ∧
      taoHigh10M_Cp10080061_sumMinusLogLog < (-2779939199111 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoHigh10M_Cp10080061_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10080061_residualProxy_neg : taoHigh10M_Cp10080061_residualProxy < 0 := by
  unfold taoHigh10M_Cp10080061_residualProxy
  norm_num

theorem taoHigh10M_Cp10080061_residualProxy_bracket :
    (-760359103 : ℝ) / 250000000 < taoHigh10M_Cp10080061_residualProxy ∧
      taoHigh10M_Cp10080061_residualProxy < (-30414364117 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10080061_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10096169, 6000 primos en ventana. -/
def taoCheckpointX_High10M_10096169 : ℕ := 10096169

noncomputable def taoHigh10M_Cp10096169_sumOneOverP : ℝ := 0.0005971372015084941
noncomputable def taoHigh10M_Cp10096169_logLogX : ℝ := 2.780536219733681
noncomputable def taoHigh10M_Cp10096169_sumMinusLogLog : ℝ := -2.779939082532173
noncomputable def taoHigh10M_Cp10096169_partialProduct : ℝ := 0.9994030410197341
noncomputable def taoHigh10M_Cp10096169_prodOverHeuristic : ℝ := 28.70739477962042
noncomputable def taoHigh10M_Cp10096169_residualProxy : ℝ := -3.0414362953769567

theorem taoHigh10M_Cp10096169_sumMinusLogLog_bracket :
    (-2779939082533 : ℝ) / 1000000000000 < taoHigh10M_Cp10096169_sumMinusLogLog ∧
      taoHigh10M_Cp10096169_sumMinusLogLog < (-277993908253 : ℝ) / 100000000000 := by
  constructor <;> unfold taoHigh10M_Cp10096169_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10096169_residualProxy_neg : taoHigh10M_Cp10096169_residualProxy < 0 := by
  unfold taoHigh10M_Cp10096169_residualProxy
  norm_num

theorem taoHigh10M_Cp10096169_residualProxy_bracket :
    (-15207181477 : ℝ) / 5000000000 < taoHigh10M_Cp10096169_residualProxy ∧
      taoHigh10M_Cp10096169_residualProxy < (-30414362951 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10096169_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10112299, 7000 primos en ventana. -/
def taoCheckpointX_High10M_10112299 : ℕ := 10112299

noncomputable def taoHigh10M_Cp10112299_sumOneOverP : ℝ := 0.0006961052425863461
noncomputable def taoHigh10M_Cp10112299_logLogX : ℝ := 2.7806351975879138
noncomputable def taoHigh10M_Cp10112299_sumMinusLogLog : ℝ := -2.7799390923453275
noncomputable def taoHigh10M_Cp10112299_partialProduct : ℝ := 0.9993041369478766
noncomputable def taoHigh10M_Cp10112299_prodOverHeuristic : ℝ := 28.707395061189985
noncomputable def taoHigh10M_Cp10112299_residualProxy : ℝ := -3.0414363051901114

theorem taoHigh10M_Cp10112299_sumMinusLogLog_bracket :
    (-1389969546173 : ℝ) / 500000000000 < taoHigh10M_Cp10112299_sumMinusLogLog ∧
      taoHigh10M_Cp10112299_sumMinusLogLog < (-2779939092343 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoHigh10M_Cp10112299_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10112299_residualProxy_neg : taoHigh10M_Cp10112299_residualProxy < 0 := by
  unfold taoHigh10M_Cp10112299_residualProxy
  norm_num

theorem taoHigh10M_Cp10112299_residualProxy_bracket :
    (-7603590763 : ℝ) / 2500000000 < taoHigh10M_Cp10112299_residualProxy ∧
      taoHigh10M_Cp10112299_residualProxy < (-30414363049 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10112299_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10128439, 8000 primos en ventana. -/
def taoCheckpointX_High10M_10128439 : ℕ := 10128439

noncomputable def taoHigh10M_Cp10128439_sumOneOverP : ℝ := 0.0007949156195997105
noncomputable def taoHigh10M_Cp10128439_logLogX : ℝ := 2.780734069124213
noncomputable def taoHigh10M_Cp10128439_sumMinusLogLog : ℝ := -2.779939153504613
noncomputable def taoHigh10M_Cp10128439_partialProduct : ℝ := 0.9992054002026638
noncomputable def taoHigh10M_Cp10128439_prodOverHeuristic : ℝ := 28.707396816773677
noncomputable def taoHigh10M_Cp10128439_residualProxy : ℝ := -3.041436366349397

theorem taoHigh10M_Cp10128439_sumMinusLogLog_bracket :
    (-555987830701 : ℝ) / 200000000000 < taoHigh10M_Cp10128439_sumMinusLogLog ∧
      taoHigh10M_Cp10128439_sumMinusLogLog < (-1389969576751 : ℝ) / 500000000000 := by
  constructor <;> unfold taoHigh10M_Cp10128439_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10128439_residualProxy_neg : taoHigh10M_Cp10128439_residualProxy < 0 := by
  unfold taoHigh10M_Cp10128439_residualProxy
  norm_num

theorem taoHigh10M_Cp10128439_residualProxy_bracket :
    (-1900897729 : ℝ) / 625000000 < taoHigh10M_Cp10128439_residualProxy ∧
      taoHigh10M_Cp10128439_residualProxy < (-30414363661 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10128439_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 10144187, 9000 primos en ventana. -/
def taoCheckpointX_High10M_10144187 : ℕ := 10144187

noncomputable def taoHigh10M_Cp10144187_sumOneOverP : ℝ := 0.0008935687840663146
noncomputable def taoHigh10M_Cp10144187_logLogX : ℝ := 2.7808303781756627
noncomputable def taoHigh10M_Cp10144187_sumMinusLogLog : ℝ := -2.7799368093915966
noncomputable def taoHigh10M_Cp10144187_partialProduct : ℝ := 0.9991068302853175
noncomputable def taoHigh10M_Cp10144187_prodOverHeuristic : ℝ := 28.707329523330326
noncomputable def taoHigh10M_Cp10144187_residualProxy : ℝ := -3.0414340222363805

theorem taoHigh10M_Cp10144187_sumMinusLogLog_bracket :
    (-173746050587 : ℝ) / 62500000000 < taoHigh10M_Cp10144187_sumMinusLogLog ∧
      taoHigh10M_Cp10144187_sumMinusLogLog < (-2779936809389 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoHigh10M_Cp10144187_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10144187_residualProxy_neg : taoHigh10M_Cp10144187_residualProxy < 0 := by
  unfold taoHigh10M_Cp10144187_residualProxy
  norm_num

theorem taoHigh10M_Cp10144187_residualProxy_bracket :
    (-30414340223 : ℝ) / 10000000000 < taoHigh10M_Cp10144187_residualProxy ∧
      taoHigh10M_Cp10144187_residualProxy < (-1520717011 : ℝ) / 500000000 := by
  unfold taoHigh10M_Cp10144187_residualProxy
  constructor <;> norm_num

/-- Checkpoint principal (suma local, no acumulativa): x = 10160539. -/
def taoHigh10M_CheckpointX : ℕ := 10160539

noncomputable def taoHigh10M_Cp10160539_sumOneOverP : ℝ := 0.0009920674957481137
noncomputable def taoHigh10M_Cp10160539_logLogX : ℝ := 2.7809302131860036
noncomputable def taoHigh10M_Cp10160539_sumMinusLogLog : ℝ := -2.7799381456902554
noncomputable def taoHigh10M_Cp10160539_partialProduct : ℝ := 0.9990084243913625
noncomputable def taoHigh10M_Cp10160539_prodOverHeuristic : ℝ := 28.707367884782663
noncomputable def taoHigh10M_Cp10160539_residualProxy : ℝ := -3.0414353585350393

theorem taoHigh10M_Cp10160539_sumMinusLogLog_bracket :
    (-2779938145691 : ℝ) / 1000000000000 < taoHigh10M_Cp10160539_sumMinusLogLog ∧
      taoHigh10M_Cp10160539_sumMinusLogLog < (-347492268211 : ℝ) / 125000000000 := by
  constructor <;> unfold taoHigh10M_Cp10160539_sumMinusLogLog <;> norm_num

theorem taoHigh10M_Cp10160539_residualProxy_neg : taoHigh10M_Cp10160539_residualProxy < 0 := by
  unfold taoHigh10M_Cp10160539_residualProxy
  norm_num

theorem taoHigh10M_Cp10160539_residualProxy_bracket :
    (-15207176793 : ℝ) / 5000000000 < taoHigh10M_Cp10160539_residualProxy ∧
      taoHigh10M_Cp10160539_residualProxy < (-30414353583 : ℝ) / 10000000000 := by
  unfold taoHigh10M_Cp10160539_residualProxy
  constructor <;> norm_num

/-! ## Ventana local `millions_1M_10M` (~586k primos en [1M, 10M)) -/

/-- Checkpoint (suma local, no acumulativa): x = 1069363, 5000 primos en ventana. -/
def taoCheckpointX_Millions_1069363 : ℕ := 1069363

noncomputable def taoMillions_Cp1069363_sumOneOverP : ℝ := 0.004835758923991824
noncomputable def taoMillions_Cp1069363_logLogX : ℝ := 2.6306343631098255
noncomputable def taoMillions_Cp1069363_sumMinusLogLog : ℝ := -2.6257986041858334
noncomputable def taoMillions_Cp1069363_partialProduct : ℝ := 0.9951759122058744
noncomputable def taoMillions_Cp1069363_prodOverHeuristic : ℝ := 24.606589348071424
noncomputable def taoMillions_Cp1069363_residualProxy : ℝ := -2.8872958170306173

theorem taoMillions_Cp1069363_sumMinusLogLog_bracket :
    (-1312899302093 : ℝ) / 500000000000 < taoMillions_Cp1069363_sumMinusLogLog ∧
      taoMillions_Cp1069363_sumMinusLogLog < (-2625798604183 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoMillions_Cp1069363_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp1069363_residualProxy_neg : taoMillions_Cp1069363_residualProxy < 0 := by
  unfold taoMillions_Cp1069363_residualProxy
  norm_num

theorem taoMillions_Cp1069363_residualProxy_bracket :
    (-28872958171 : ℝ) / 10000000000 < taoMillions_Cp1069363_residualProxy ∧
      taoMillions_Cp1069363_residualProxy < (-3609119771 : ℝ) / 1250000000 := by
  unfold taoMillions_Cp1069363_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 2432587, 100000 primos en ventana. -/
def taoCheckpointX_Millions_2432587 : ℕ := 2432587

noncomputable def taoMillions_Cp2432587_sumOneOverP : ℝ := 0.06235128945765767
noncomputable def taoMillions_Cp2432587_logLogX : ℝ := 2.6881512475159632
noncomputable def taoMillions_Cp2432587_sumMinusLogLog : ℝ := -2.6257999580583054
noncomputable def taoMillions_Cp2432587_partialProduct : ℝ := 0.9395527543289707
noncomputable def taoMillions_Cp2432587_prodOverHeuristic : ℝ := 24.60662220917977
noncomputable def taoMillions_Cp2432587_residualProxy : ℝ := -2.8872971709030892

theorem taoMillions_Cp2432587_sumMinusLogLog_bracket :
    (-2625799958059 : ℝ) / 1000000000000 < taoMillions_Cp2432587_sumMinusLogLog ∧
      taoMillions_Cp2432587_sumMinusLogLog < (-328224994757 : ℝ) / 125000000000 := by
  constructor <;> unfold taoMillions_Cp2432587_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp2432587_residualProxy_neg : taoMillions_Cp2432587_residualProxy < 0 := by
  unfold taoMillions_Cp2432587_residualProxy
  norm_num

theorem taoMillions_Cp2432587_residualProxy_bracket :
    (-2887297171 : ℝ) / 1000000000 < taoMillions_Cp2432587_residualProxy ∧
      taoMillions_Cp2432587_residualProxy < (-28872971707 : ℝ) / 10000000000 := by
  unfold taoMillions_Cp2432587_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 3928667, 200000 primos en ventana. -/
def taoCheckpointX_Millions_3928667 : ℕ := 3928667

noncomputable def taoMillions_Cp3928667_sumOneOverP : ℝ := 0.09443317011207081
noncomputable def taoMillions_Cp3928667_logLogX : ℝ := 2.720229777390412
noncomputable def taoMillions_Cp3928667_sumMinusLogLog : ℝ := -2.625796607278341
noncomputable def taoMillions_Cp3928667_partialProduct : ℝ := 0.9098885166875568
noncomputable def taoMillions_Cp3928667_prodOverHeuristic : ℝ := 24.606539628865995
noncomputable def taoMillions_Cp3928667_residualProxy : ℝ := -2.887293820123125

theorem taoMillions_Cp3928667_sumMinusLogLog_bracket :
    (-2625796607279 : ℝ) / 1000000000000 < taoMillions_Cp3928667_sumMinusLogLog ∧
      taoMillions_Cp3928667_sumMinusLogLog < (-656449151819 : ℝ) / 250000000000 := by
  constructor <;> unfold taoMillions_Cp3928667_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp3928667_residualProxy_neg : taoMillions_Cp3928667_residualProxy < 0 := by
  unfold taoMillions_Cp3928667_residualProxy
  norm_num

theorem taoMillions_Cp3928667_residualProxy_bracket :
    (-14436469101 : ℝ) / 5000000000 < taoMillions_Cp3928667_residualProxy ∧
      taoMillions_Cp3928667_residualProxy < (-28872938199 : ℝ) / 10000000000 := by
  unfold taoMillions_Cp3928667_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 5464031, 300000 primos en ventana. -/
def taoCheckpointX_Millions_5464031 : ℕ := 5464031

noncomputable def taoMillions_Cp5464031_sumOneOverP : ℝ := 0.11592961607639489
noncomputable def taoMillions_Cp5464031_logLogX : ℝ := 2.7417233339317644
noncomputable def taoMillions_Cp5464031_sumMinusLogLog : ℝ := -2.6257937178553696
noncomputable def taoMillions_Cp5464031_partialProduct : ℝ := 0.8905378754142584
noncomputable def taoMillions_Cp5464031_prodOverHeuristic : ℝ := 24.60646847289772
noncomputable def taoMillions_Cp5464031_residualProxy : ℝ := -2.8872909307001535

theorem taoMillions_Cp5464031_sumMinusLogLog_bracket :
    (-82056053683 : ℝ) / 31250000000 < taoMillions_Cp5464031_sumMinusLogLog ∧
      taoMillions_Cp5464031_sumMinusLogLog < (-2625793717853 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoMillions_Cp5464031_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp5464031_residualProxy_neg : taoMillions_Cp5464031_residualProxy < 0 := by
  unfold taoMillions_Cp5464031_residualProxy
  norm_num

theorem taoMillions_Cp5464031_residualProxy_bracket :
    (-7218227327 : ℝ) / 2500000000 < taoMillions_Cp5464031_residualProxy ∧
      taoMillions_Cp5464031_residualProxy < (-5774581861 : ℝ) / 2000000000 := by
  unfold taoMillions_Cp5464031_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 7028963, 400000 primos en ventana. -/
def taoCheckpointX_Millions_7028963 : ℕ := 7028963

noncomputable def taoMillions_Cp7028963_sumOneOverP : ℝ := 0.13202551167141097
noncomputable def taoMillions_Cp7028963_logLogX : ℝ := 2.7578271634475597
noncomputable def taoMillions_Cp7028963_sumMinusLogLog : ℝ := -2.6258016517761487
noncomputable def taoMillions_Cp7028963_partialProduct : ℝ := 0.8763186124736502
noncomputable def taoMillions_Cp7028963_prodOverHeuristic : ℝ := 24.60666366739903
noncomputable def taoMillions_Cp7028963_residualProxy : ℝ := -2.8872988646209325

theorem taoMillions_Cp7028963_sumMinusLogLog_bracket :
    (-2625801651777 : ℝ) / 1000000000000 < taoMillions_Cp7028963_sumMinusLogLog ∧
      taoMillions_Cp7028963_sumMinusLogLog < (-1312900825887 : ℝ) / 500000000000 := by
  constructor <;> unfold taoMillions_Cp7028963_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp7028963_residualProxy_neg : taoMillions_Cp7028963_residualProxy < 0 := by
  unfold taoMillions_Cp7028963_residualProxy
  norm_num

theorem taoMillions_Cp7028963_residualProxy_bracket :
    (-28872988647 : ℝ) / 10000000000 < taoMillions_Cp7028963_residualProxy ∧
      taoMillions_Cp7028963_residualProxy < (-7218247161 : ℝ) / 2500000000 := by
  unfold taoMillions_Cp7028963_residualProxy
  constructor <;> norm_num

/-- Checkpoint (suma local, no acumulativa): x = 8616547, 500000 primos en ventana. -/
def taoCheckpointX_Millions_8616547 : ℕ := 8616547

noncomputable def taoMillions_Cp8616547_sumOneOverP : ℝ := 0.14485477819817347
noncomputable def taoMillions_Cp8616547_logLogX : ℝ := 2.770661552837407
noncomputable def taoMillions_Cp8616547_sumMinusLogLog : ℝ := -2.6258067746392335
noncomputable def taoMillions_Cp8616547_partialProduct : ℝ := 0.8651478959777597
noncomputable def taoMillions_Cp8616547_prodOverHeuristic : ℝ := 24.60678970396996
noncomputable def taoMillions_Cp8616547_residualProxy : ℝ := -2.8873039874840174

theorem taoMillions_Cp8616547_sumMinusLogLog_bracket :
    (-32822584683 : ℝ) / 12500000000 < taoMillions_Cp8616547_sumMinusLogLog ∧
      taoMillions_Cp8616547_sumMinusLogLog < (-2625806774637 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoMillions_Cp8616547_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp8616547_residualProxy_neg : taoMillions_Cp8616547_residualProxy < 0 := by
  unfold taoMillions_Cp8616547_residualProxy
  norm_num

theorem taoMillions_Cp8616547_residualProxy_bracket :
    (-230984319 : ℝ) / 80000000 < taoMillions_Cp8616547_residualProxy ∧
      taoMillions_Cp8616547_residualProxy < (-28196328 : ℝ) / 9765625 := by
  unfold taoMillions_Cp8616547_residualProxy
  constructor <;> norm_num

/-- Checkpoint principal (suma local, no acumulativa): x = 9999991. -/
def taoMillions_CheckpointX : ℕ := 9999991

noncomputable def taoMillions_Cp9999991_sumOneOverP : ℝ := 0.15412128171203857
noncomputable def taoMillions_Cp9999991_logLogX : ℝ := 2.7799425384653804
noncomputable def taoMillions_Cp9999991_sumMinusLogLog : ℝ := -2.625821256753342
noncomputable def taoMillions_Cp9999991_partialProduct : ℝ := 0.8571680293616284
noncomputable def taoMillions_Cp9999991_prodOverHeuristic : ℝ := 24.6071460525909
noncomputable def taoMillions_Cp9999991_residualProxy : ℝ := -2.8873184695981258

theorem taoMillions_Cp9999991_sumMinusLogLog_bracket :
    (-1312910628377 : ℝ) / 500000000000 < taoMillions_Cp9999991_sumMinusLogLog ∧
      taoMillions_Cp9999991_sumMinusLogLog < (-2625821256751 : ℝ) / 1000000000000 := by
  constructor <;> unfold taoMillions_Cp9999991_sumMinusLogLog <;> norm_num

theorem taoMillions_Cp9999991_residualProxy_neg : taoMillions_Cp9999991_residualProxy < 0 := by
  unfold taoMillions_Cp9999991_residualProxy
  norm_num

theorem taoMillions_Cp9999991_residualProxy_bracket :
    (-3609148087 : ℝ) / 1250000000 < taoMillions_Cp9999991_residualProxy ∧
      taoMillions_Cp9999991_residualProxy < (-28873184693 : ℝ) / 10000000000 := by
  unfold taoMillions_Cp9999991_residualProxy
  constructor <;> norm_num

/-! ## Tendencia empírica `Δ_proxy` en escala baja (hacia PNT+ `Δ → 0`) -/

theorem taoResidualProxy_tightens_Cp7919_to_Cp104729 :
    taoCp104729_residualProxy < taoCp7919_residualProxy := by
  unfold taoCp7919_residualProxy taoCp104729_residualProxy
  norm_num

theorem taoCp104729_residualProxy_lt_thousandth :
    taoCp104729_residualProxy < (1 / 1000 : ℝ) := by
  unfold taoCp104729_residualProxy
  norm_num


/-! ## Contraste entre escalas (acumulativa vs ventana local) -/

/-- Escala baja acumulativa: `∏ / (e^{-γ}/log x) ≈ 1`. -/
theorem taoLow_prodOverHeuristic_near_one :
    taoCp104729_prodOverHeuristic < (2 : ℝ) := by
  unfold taoCp104729_prodOverHeuristic
  norm_num

/-- Ventana local 10M: la heurística Mertens-3 no aplica (producto ≈ 1 en ventana). -/
theorem taoHigh10M_prodOverHeuristic_gt_twenty :
    (20 : ℝ) < taoHigh10M_Cp10160539_prodOverHeuristic := by
  unfold taoHigh10M_Cp10160539_prodOverHeuristic
  norm_num

/-- Ventana local [1M,10M): mismo fenómeno en x ≈ 10⁷. -/
theorem taoMillions_prodOverHeuristic_gt_twenty :
    (20 : ℝ) < taoMillions_Cp9999991_prodOverHeuristic := by
  unfold taoMillions_Cp9999991_prodOverHeuristic
  norm_num

/-- Escala baja: `S - log log` cerca de `M`. Ventana 10M: suma local ≪ log log. -/
theorem taoLow_sumMinusLogLog_near_M :
    (1 / 4 : ℝ) < taoCp104729_sumMinusLogLog ∧
      taoCp104729_sumMinusLogLog < (1 / 2 : ℝ) := by
  constructor <;> unfold taoCp104729_sumMinusLogLog <;> norm_num

theorem taoHigh10M_sumMinusLogLog_far_below_loglog :
    taoHigh10M_Cp10160539_sumMinusLogLog < (-2 : ℝ) := by
  unfold taoHigh10M_Cp10160539_sumMinusLogLog
  norm_num


/-! ## Normalización de gaps `g_n / log p_n` -/
noncomputable def taoGapMean_low_from_2 : ℝ := 1.0041835788042288
theorem taoGapMean_low_from_2_near_one :
    (10041835787 : ℝ) / 10000000000 < taoGapMean_low_from_2 ∧
      taoGapMean_low_from_2 < (1004183579 : ℝ) / 1000000000 := by
  constructor <;> unfold taoGapMean_low_from_2 <;> norm_num

noncomputable def taoGapMean_high_from_10M : ℝ := 0.9955058562947525
theorem taoGapMean_high_from_10M_near_one :
    (9955058561 : ℝ) / 10000000000 < taoGapMean_high_from_10M ∧
      taoGapMean_high_from_10M < (2488764641 : ℝ) / 2500000000 := by
  constructor <;> unfold taoGapMean_high_from_10M <;> norm_num

noncomputable def taoGapMean_millions_1M_10M : ℝ := 1.000358672216777
theorem taoGapMean_millions_1M_10M_near_one :
    (10003586721 : ℝ) / 10000000000 < taoGapMean_millions_1M_10M ∧
      taoGapMean_millions_1M_10M < (2500896681 : ℝ) / 2500000000 := by
  constructor <;> unfold taoGapMean_millions_1M_10M <;> norm_num

end ErdosReciprocals

/-! ### From `ErdosReciprocals/WheelSieve.lean` -/

/-!
# Wheel sieves — puente formal al mensaje Tao §1

Datos generados en `TTAOData` desde `TTAO/data/wheel_sieve_mod_*.json`.

* Residuos coprimos mod `W`: `φ(W)` clases, fracción de supervivencia `φ(W)/W`.
* Saltos **documentados** (`factorizador.cpp`): una vuelta tiene `φ(W)` saltos;
  su suma es `W/2` (recorrido de índices `u` en la rama Sundaram).
* **Gaps entre residuos** (rueda aritmética cíclica): también `φ(W)` saltos,
  pero suman `W` (periodo completo).

Los saltos C++ no coinciden con los gaps de residuos; ambas listas están verificadas.
-/

namespace ErdosReciprocals

/-!
### Mod 30 — 8 saltos (mensaje Tao)
-/

theorem tao_message_wheel30_eight_jumps :
    taoWheel30_jumpsDocumented.length = 8 :=
  taoWheel30_documented_jump_count_eq_phi

theorem tao_wheel30_survival_matches_primorial :
    (taoWheel30_phi : ℝ) / taoWheel30_modulus = (4 : ℝ) / 15 := by
  rw [taoWheel30_survival_fraction]
  norm_num

theorem tao_wheel30_documented_jumps_half_period :
    taoWheel30_jumpsDocumented.sum = taoWheel30_modulus / 2 :=
  taoWheel30_documented_jumps_sum_eq_half_modulus

theorem tao_wheel30_residue_gaps_full_period :
    taoWheel30_residueGaps.sum = taoWheel30_modulus :=
  taoWheel30_residue_gaps_sum_eq_modulus

/-!
### Mod 210 — 48 saltos (mensaje Tao)
-/

theorem tao_message_wheel210_forty_eight_jumps :
    taoWheel210_jumpsDocumented.length = 48 :=
  taoWheel210_documented_jump_count_eq_phi

theorem tao_wheel210_survival_matches_primorial :
    (taoWheel210_phi : ℝ) / taoWheel210_modulus = (8 : ℝ) / 35 := by
  rw [taoWheel210_survival_fraction]
  norm_num

theorem tao_wheel210_documented_jumps_half_period :
    taoWheel210_jumpsDocumented.sum = taoWheel210_modulus / 2 :=
  taoWheel210_documented_jumps_sum_eq_half_modulus

theorem tao_wheel210_residue_gaps_full_period :
    taoWheel210_residueGaps.sum = taoWheel210_modulus :=
  taoWheel210_residue_gaps_sum_eq_modulus

/-!
### Enlace Mertens: tasa de exclusión = ∏_{p|W}(1 - 1/p)
-/

theorem tao_wheel30_exclusion_rate_eq_euler_product :
    (taoWheel30_phi : ℝ) / taoWheel30_modulus =
      (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) := by
  rw [tao_wheel30_survival_matches_primorial, primorial_euler_product_30]

theorem tao_wheel210_exclusion_rate_eq_euler_product :
    (taoWheel210_phi : ℝ) / taoWheel210_modulus =
      (1 - (1 : ℝ) / 2) * (1 - (1 : ℝ) / 3) * (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 7) := by
  rw [tao_wheel210_survival_matches_primorial, primorial_euler_product_210]

end ErdosReciprocals

/-! ### From `ErdosReciprocals/MertensTableBridge.lean` -/

/-!
# Puente criba `mertens_table` ↔ TTAO

La criba segmentada (`CONJETURA-009-ERDOS/data/mertens_table.json`) registra
`S(n)`, `Δ = S(n) - (log log n + M)` y `∏(1-1/p)` en potencias de 10 hasta `10¹¹`.

Los checkpoints TTAO (`low_from_2`) usan recuentos fijos de primos hasta `x = 104729`.
Ambas fuentes son empíricas; aquí solo enlazamos consistencia de magnitud y tendencia.
-/

namespace ErdosReciprocals

open Real

/-!
### Tendencia hacia PNT+ `Δ → 0` (empírica criba)
-/

theorem criba_empirical_delta_toward_zero :
    cribaCp100000000000_delta < cribaCp1000_delta :=
  criba_delta_tightens_1e3_to_1e11

theorem criba_empirical_delta_micro_at_1e11 :
    cribaCp100000000000_delta < (1 / 1000000 : ℝ) :=
  cribaCp100000000000_delta_lt_micro

theorem criba_empirical_S_monotone_to_1e11 :
    cribaCp1000_S < cribaCp100000000000_S :=
  cribaCp100000000000_S_gt_cribaCp1000_S

/-!
### Cruce criba `n = 10⁵` vs TTAO `x = 104729` (misma escala baja)
-/

/-- `S(10⁵)` de la criba queda por debajo de la suma TTAO hasta el primo 10 000. -/
theorem cribaCp100000_S_lt_taoCp104729_sum :
    cribaCp100000_S < taoCp104729_sumOneOverP := by
  unfold cribaCp100000_S taoCp104729_sumOneOverP
  norm_num

/-- Ambos proxies `S - log log` son positivos y del mismo orden en escala baja. -/
theorem criba_and_tao_residual_proxy_positive_at_low_scale :
    (0 : ℝ) < cribaCp100000_delta ∧
      (0 : ℝ) < taoCp104729_residualProxy := by
  constructor
  · unfold cribaCp100000_delta
    norm_num
  · exact taoCp104729_residualProxy_pos

/-- La criba en `10⁵` ya tiene `Δ` criba < 10⁻³ (TTAO llega ahí en `x = 104729`). -/
theorem cribaCp100000_delta_lt_thousandth :
    cribaCp100000_delta < (1 / 1000 : ℝ) := by
  unfold cribaCp100000_delta
  norm_num

/-!
### Nota metodológica (no teorema PNT+)

`cribaCp*_delta` usa la misma aproximación `M ≈ mertensConstantApprox` que los
proxies TTAO; no identifica `mertensResidual n` con `partialSum n` salvo PNT+.
-/

end ErdosReciprocals

end
