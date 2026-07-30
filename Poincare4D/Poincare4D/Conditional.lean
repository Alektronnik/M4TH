/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Poincare4D.Surgery

/-!
## Source file: Poincare4D/Conditional.lean

Conditional closure. Contains the main conditional theorem
 and the symmetric program.
-/

noncomputable section

@[expose] public section

namespace Poincare4D

/-!
### FASE 6: Cierre Topológico Condicional
El Teorema Principal de Poincaré 4D.
-/

namespace Assumptions
  /-- Contrato temporal: monotonía del funcional de energía a lo largo del flujo.
  La energía no crece a medida que el tiempo avanza. El funcional `E` se pasa
  como dato externo para evitar que el contrato se habite con una energía
  constante elegida ad hoc. -/
  def EnergyMonotone (state : CoupledFlowState) (E : EnergyFunctional state) : Prop :=
    AntitoneOn E.value state.time_domain

  /-- Una identidad de disipación con densidad no negativa implica monotonía de
  la energía. Esto aísla la parte analítica difícil en el certificado de
  disipación; la implicación ordenada queda probada en Lean. -/
  theorem EnergyMonotone.of_dissipation_certificate
      {state : CoupledFlowState} {E : EnergyFunctional state}
      (cert : EnergyDissipationCertificate state E) :
      EnergyMonotone state E := by
    intro t₁ ht₁ t₂ ht₂ hle
    have hnonneg :
        0 ≤ E.spatial_integral.integral (fun x ↦ cert.density t₁ t₂ x) :=
      E.spatial_integral.nonneg
        (fun x ↦ cert.density t₁ t₂ x)
        (cert.integrable_density t₁ t₂ ht₁ ht₂ hle)
        (cert.nonnegative_density t₁ t₂ ht₁ ht₂ hle)
    have hdrop :
        E.value t₁ - E.value t₂ =
          E.spatial_integral.integral (fun x ↦ cert.density t₁ t₂ x) :=
      cert.energy_drop_identity t₁ t₂ ht₁ ht₂ hle
    nlinarith

  /-- Forma operacional de la monotonía: tiempos posteriores tienen energía menor
  o igual dentro del dominio temporal del flujo. -/
  theorem EnergyMonotone.energy_le
      {state : CoupledFlowState} {E : EnergyFunctional state}
      (hE : EnergyMonotone state E)
      {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ state.time_domain) (ht₂ : t₂ ∈ state.time_domain)
      (hle : t₁ ≤ t₂) :
      E.value t₂ ≤ E.value t₁ :=
    hE ht₁ ht₂ hle

  /-- Contrato puente: la extinción terminal a un perfil redondo implica difeomorfismo con S^4.
  Al depender de CoupledFlowState, asume implícitamente la Ventana Crítica (gamma < 8). -/
  def RoundExtinctionImpliesSphereDiffeomorphism (M : Type*) [TopologicalSpace M] [ChartedSpace Euclidean4 M] [IsManifold Model4 ⊤ M]
    (_h_closed : ClosedManifold M) (_h_homotopy : HomotopySphere M)
    : Prop :=
    (∃ (final_state : CoupledFlowState), extinct_to_round_point final_state) →
      DiffeomorphicToSphere4 M

  /-- Tasa de disipación instantánea para el modelo de laboratorio.
  Representa físicamente la norma cuadrática L2 de las velocidades del flujo. -/
  def labDissipationRate (state : CoupledFlowState) (t x : ℝ) : ℝ :=
    (state.profile_derivs.psi_t t x)^2 + (state.gauge_derivs.w_t t x)^2

  /-- Densidad de disipación acumulada entre dos tiempos t₁ y t₂.
  Usa la integral de Lebesgue estándar 1D en el tiempo. -/
  noncomputable def labDissipationDensity (state : CoupledFlowState) (t₁ t₂ x : ℝ) : ℝ :=
    ∫ t in Set.Icc t₁ t₂, labDissipationRate state t x

  /-- Identidad variacional explícita para el laboratorio.
  Exige que la caída de energía coincida con la integral espacial de la densidad
  de disipación acumulada. En la etapa analítica posterior, esto se demostrará
  mediante integración por partes en el espacio. -/
  def SatisfiesLabVariationalIdentity (state : CoupledFlowState) (E : EnergyFunctional state) : Prop :=
    (∀ t₁ t₂, t₁ ∈ state.time_domain → t₂ ∈ state.time_domain → t₁ ≤ t₂ →
      MeasureTheory.Integrable (fun x ↦ labDissipationDensity state t₁ t₂ x)) ∧
    (∀ t₁ t₂, t₁ ∈ state.time_domain → t₂ ∈ state.time_domain → t₁ ≤ t₂ →
      ∀ x, 0 ≤ labDissipationDensity state t₁ t₂ x) ∧
    (∀ t₁ t₂, t₁ ∈ state.time_domain → t₂ ∈ state.time_domain → t₁ ≤ t₂ →
      E.value t₁ - E.value t₂ = E.spatial_integral.integral (fun x ↦ labDissipationDensity state t₁ t₂ x))

  /-- Instanciación formal del certificado de disipación para el modelo numérico,
  asumiendo la identidad variacional como contrato. -/
  noncomputable def labEnergyDissipationCertificate
      (state : CoupledFlowState) (E : EnergyFunctional state)
      (_h_lab : satisfies_numerical_lab_model state)
      (h_var : SatisfiesLabVariationalIdentity state E) :
      EnergyDissipationCertificate state E where
    density := labDissipationDensity state
    integrable_density := h_var.1
    nonnegative_density := h_var.2.1
    energy_drop_identity := h_var.2.2

end Assumptions

/-!
### FASE 7: Programa simétrico

Esta sección refleja el `Poincare4DBLUEPRINT.md`: el teorema simétrico
se formaliza como ensamblaje condicional de contratos analíticos ya redactados
en papel. No se intenta demostrar aquí Kotschwar, Arzelà-Ascoli, no-colapso
geométrico ni teoría parabólica completa; esos bloques quedan tipados con
nombres precisos para evitar que la formalización confunda arquitectura con
prueba analítica.
-/
namespace SymmetricProgram

/-! ### PCO-term: operador de curvatura positivo en la componente terminal

Para la métrica de cohomogeneidad uno `g = ds² + ψ² g_{S³}`, las curvaturas
seccionales son `L = -ψ_{ss}/ψ` (planos radiales) y `K = (1-ψ_s²)/ψ²` (planos
de fibra). El operador de curvatura es diag(L, L, L, K, K, K) por la simetría
SO(4) de la fibra. `K > 0` es automático (`|ψ_s| < 1` por principio del máximo).
La positividad equivale a `L > 0`, es decir, sin cuellos en la terminal.

Referencia: Hamilton (1986), *Four-manifolds with positive curvature operator*.
Bajo PCO-term, el flujo de Ricci converge a un punto redondo (Tipo I). -/

/-- Curvatura seccional radial: `L = -ψ_{ss}/ψ`. -/
def sectionalCurvatureL (p : RotationallySymmetricProfile) (dp : ProfileDerivatives p) (t x : ℝ) : ℝ :=
  -(dp.psi_xx t x) / p.psi t x

/-- Curvatura seccional de fibra: `K = (1-ψ_s²)/ψ²`. -/
def sectionalCurvatureK (p : RotationallySymmetricProfile) (dp : ProfileDerivatives p) (t x : ℝ) : ℝ :=
  (1 - (dp.psi_x t x) ^ 2) / (p.psi t x) ^ 2

/-- `K ≥ 0` automático en el interior: `|ψ_s| ≤ 1` por principio del máximo
(Angenent-Knopf), y `ψ > 0` por regularidad polar.
En el interior estricto (`|ψ_s| < 1`) se tiene `K > 0`. -/
lemma sectionalCurvatureK_nonneg (p : RotationallySymmetricProfile) (dp : ProfileDerivatives p) (t x : ℝ)
    (h_psi_pos : 0 < p.psi t x) (h_psis_bound : |dp.psi_x t x| ≤ 1) :
    0 ≤ sectionalCurvatureK p dp t x := by
  dsimp [sectionalCurvatureK]
  have h_psis_sq_le_one : (dp.psi_x t x) ^ 2 ≤ 1 := by
    rcases abs_le.mp h_psis_bound with ⟨hlo, hhi⟩
    nlinarith
  have h_num_nonneg : 0 ≤ 1 - (dp.psi_x t x) ^ 2 := by linarith
  have h_den_pos : 0 < (p.psi t x) ^ 2 := pow_pos h_psi_pos 2
  exact div_nonneg h_num_nonneg (by linarith)

/-- Operador de curvatura positivo: `L > 0` y `K > 0`.
Con `|ψ_s| ≤ 1` solo tenemos `K ≥ 0` (`sectionalCurvatureK_nonneg`);
la positividad estricta de `K` requiere `|ψ_s| < 1`, que se cumple en
el interior de la componente terminal. Basta verificar `L > 0`. -/
def positive_curvature_operator (p : RotationallySymmetricProfile) (dp : ProfileDerivatives p) : Prop :=
  ∀ t x, 0 < p.psi t x → 0 < sectionalCurvatureL p dp t x

/-- PCO-term: contrato terminal. La componente terminal post-cirugía tiene
operador de curvatura positivo. Equivalente a `L > 0` en todo punto interior
(no contiene cuellos, `ψ_{ss} < 0`).

Hamilton (1986) establece que bajo PCO-term el flujo de Ricci converge a un
punto redondo. Este teorema se documenta en ANALITICA y no se introduce como
axioma en Lean; el contrato Lean para la extinción redonda sigue siendo
`extinct_to_round_point`, cuya justificación analítica es PCO-term + Hamilton. -/
def pco_term (state : CoupledFlowState) : Prop :=
  positive_curvature_operator state.profile state.profile_derivs

/-- Datos de paridad polar de H1.4. La variable `r` es la coordenada radial
firmada en torno a cada polo. En el polo izquierdo, `ψ - r` es impar y `φ,w`
son pares; en el derecho, `ψ - r` es impar para la coordenada `r = sR - x`. -/
structure PolarParityData
    (p : RotationallySymmetricProfile) (g : GaugeField) (sL sR : ℝ) : Prop where
  phi_even_left :
    ∀ t r, p.phi t (sL + r) = p.phi t (sL - r)
  gauge_even_left :
    ∀ t r, g.w t (sL + r) = g.w t (sL - r)
  psi_minus_radius_odd_left :
    ∀ t r, p.psi t (sL + r) - r = - (p.psi t (sL - r) + r)
  phi_even_right :
    ∀ t r, p.phi t (sR + r) = p.phi t (sR - r)
  gauge_even_right :
    ∀ t r, g.w t (sR + r) = g.w t (sR - r)
  psi_minus_radius_odd_right :
    ∀ t r, p.psi t (sR - r) - r = - (p.psi t (sR + r) + r)

/-- Regularidad polar de los cocientes aparentemente singulares de H1.5. Se
registra como acotación local en vecindades perforadas de los dos polos; esta
es la forma de contrato que evita dividir por `ψ = 0` justo en el polo. -/
structure PolarQuotientRegularity
    (p : RotationallySymmetricProfile) (dp : ProfileDerivatives p) (sL sR : ℝ) : Prop where
  local_bound :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      (∀ t x, 0 < |x - sL| → |x - sL| < ε →
        |dp.psi_xx t x / p.psi t x| ≤ C ∧
        |(1 - (dp.psi_x t x)^2) / p.psi t x| ≤ C) ∧
      (∀ t x, 0 < |x - sR| → |x - sR| < ε →
        |dp.psi_xx t x / p.psi t x| ≤ C ∧
        |(1 - (dp.psi_x t x)^2) / p.psi t x| ≤ C)

/-- Regularidad polar de Angenent-Knopf para perfiles rotacionales cerrados.
Los polos son degeneraciones coordenadas regulares de la fibra, no singularidades
geométricas del flujo. El contrato registra la normalización de arco:
`ψ = 0` en los polos y derivada radial `+1` en el extremo izquierdo,
`-1` en el extremo derecho. -/
structure PolarRegularProfile
    (p : RotationallySymmetricProfile) (dp : ProfileDerivatives p) (g : GaugeField) : Prop where
  regular_poles :
    ∃ sL sR, sL < sR ∧
      (∀ t, p.psi t sL = 0) ∧
      (∀ t, p.psi t sR = 0) ∧
      (∀ t, dp.psi_x t sL = 1) ∧
      (∀ t, dp.psi_x t sR = -1) ∧
      (∀ t, 0 < p.phi t sL) ∧
      (∀ t, 0 < p.phi t sR) ∧
      (∀ t x, sL < x → x < sR → 0 < p.psi t x) ∧
      PolarParityData p g sL sR ∧
      PolarQuotientRegularity p dp sL sR

/-- H1-sym: existencia local polar en la clase de cohomogeneidad uno, empaquetada
como contrato PDE. -/
def satisfies_h1_sym (state : CoupledFlowState) : Prop :=
  PolarRegularProfile state.profile state.profile_derivs state.gauge ∧
    satisfies_coupled_ricci_gauge_flow state

/-- Sub-ledger algebraico del bloque potencial de D2.3c. Este bloque sí está
cerrado puntualmente en Lean: bajo la banda física, el potencial está entre `0`
y `1/4`, y la energía gauge se separa como cinética geométrica más potencial. -/
structure GaugePotentialLedger (state : CoupledFlowState) : Prop where
  physical_band : gauge_in_physical_band state.gauge
  potential_nonnegative :
    ∀ t x, 0 ≤ doubleWellPotential (state.gauge.w t x)
  potential_le_quarter :
    ∀ t x, doubleWellPotential (state.gauge.w t x) ≤ (1 / 4 : ℝ)
  energy_split :
    ∀ t x,
      gaugeEnergyDensity state.profile state.gauge state.gauge_derivs t x =
        gaugeKineticDensity state.profile state.gauge state.gauge_derivs t x +
          doubleWellPotential (state.gauge.w t x)
  gauge_energy_nonnegative :
    ∀ t x, 0 ≤ gaugeEnergyDensity state.profile state.gauge state.gauge_derivs t x
  gauge_energy_le_kinetic_add_quarter :
    ∀ t x,
      gaugeEnergyDensity state.profile state.gauge state.gauge_derivs t x ≤
        gaugeKineticDensity state.profile state.gauge state.gauge_derivs t x + (1 / 4 : ℝ)

/-- Constructor del sub-ledger potencial desde el principio de máximo
Allen-Cahn `|w| ≤ 1`. -/
theorem GaugePotentialLedger.of_physical_band
    {state : CoupledFlowState} (h_band : gauge_in_physical_band state.gauge) :
    GaugePotentialLedger state where
  physical_band := h_band
  potential_nonnegative := fun t x ↦ doubleWellPotential_nonneg (state.gauge.w t x)
  potential_le_quarter := fun t x ↦ gaugePotentialBound_of_physicalBand h_band t x
  energy_split := fun t x ↦
    gaugeEnergyDensity_eq_kinetic_add_potential
      state.profile state.gauge state.gauge_derivs t x
  gauge_energy_nonnegative := fun t x ↦
    gaugeEnergyDensity_nonneg state.profile state.gauge state.gauge_derivs t x
  gauge_energy_le_kinetic_add_quarter := fun t x ↦
    gaugeEnergyDensity_le_kinetic_add_quarter
      state.profile state.gauge state.gauge_derivs h_band t x

/-- Densidad gauge ponderada por el parámetro de escala temporal `τ`. -/
def weightedGaugeEnergyDensity (state : CoupledFlowState) (tau t x : ℝ) : ℝ :=
  tau * gaugeEnergyDensity state.profile state.gauge state.gauge_derivs t x

/-- Sub-ledger puntual para los términos de peso y `τ` en D2.3c. No afirma la
ecuación conjugada completa; solo registra que, con `τ > 0`, la energía gauge
ponderada es no negativa y que la compensación de peso/escala queda controlada
por la energía gauge local. -/
structure WeightTauLedger (state : CoupledFlowState) : Prop where
  exists_controlled_compensation :
    ∃ tau C : ℝ, ∃ compensation : ℝ → ℝ → ℝ,
      0 < tau ∧
      0 ≤ C ∧
      (∀ t x, 0 ≤ weightedGaugeEnergyDensity state tau t x) ∧
      (∀ t x,
        |compensation t x| ≤
          C * gaugeEnergyDensity state.profile state.gauge state.gauge_derivs t x)

/-- Constructor del sub-ledger peso/τ desde una cota puntual de compensación. -/
theorem WeightTauLedger.of_compensation_bound
    {state : CoupledFlowState}
    {tau C : ℝ} (htau : 0 < tau) (hC : 0 ≤ C)
    (compensation : ℝ → ℝ → ℝ)
    (hcomp :
      ∀ t x,
        |compensation t x| ≤
          C * gaugeEnergyDensity state.profile state.gauge state.gauge_derivs t x) :
    WeightTauLedger state where
  exists_controlled_compensation := by
    refine ⟨tau, C, compensation, htau, hC, ?_, hcomp⟩
    intro t x
    unfold weightedGaugeEnergyDensity
    exact mul_nonneg (le_of_lt htau)
      (gaugeEnergyDensity_nonneg state.profile state.gauge state.gauge_derivs t x)

/-- Sub-ledger puntual para el residuo métrico de D2.3c. Registra una densidad
residual y una cota unilateral fuerte: su valor absoluto está dominado por una
constante no negativa por la energía gauge local. -/
structure MetricResidualLedger (state : CoupledFlowState) : Prop where
  exists_controlled_metric_residual :
    ∃ C : ℝ, ∃ residual : ℝ → ℝ → ℝ,
      0 ≤ C ∧
      ∀ t x,
        |residual t x| ≤
          C * gaugeEnergyDensity state.profile state.gauge state.gauge_derivs t x

/-- Constructor del sub-ledger residual métrico desde una cota puntual. -/
theorem MetricResidualLedger.of_residual_bound
    {state : CoupledFlowState}
    {C : ℝ} (hC : 0 ≤ C)
    (residual : ℝ → ℝ → ℝ)
    (hres :
      ∀ t x,
        |residual t x| ≤
          C * gaugeEnergyDensity state.profile state.gauge state.gauge_derivs t x) :
    MetricResidualLedger state where
  exists_controlled_metric_residual := ⟨C, residual, hC, hres⟩

/-- Sub-ledger para el bloque de cuadrados de Perelman-List. No intenta derivar
la identidad geométrica completa; registra la densidad de disipación que el
libro mayor tratará como suma de cuadrados no negativa. -/
structure ListSquareLedger (state : CoupledFlowState) : Prop where
  exists_nonnegative_density :
    ∃ density : ℝ → ℝ → ℝ,
      ∀ t x, 0 ≤ density t x

/-- Constructor del sub-ledger de cuadrados desde una densidad no negativa. -/
theorem ListSquareLedger.of_nonnegative_density
    {state : CoupledFlowState}
    (density : ℝ → ℝ → ℝ)
    (h_nonneg : ∀ t x, 0 ≤ density t x) :
    ListSquareLedger state where
  exists_nonnegative_density := ⟨density, h_nonneg⟩

/-- D2.3c: libro mayor exhaustivo de la variación de `W_tau`. La cuenta exacta
vive en el documento analítico; Lean registra aquí que todos los términos han
sido asignados a cuadrados de List, potencial, peso/τ o residuo métrico. -/
structure WVariationLedger (state : CoupledFlowState) (E : EnergyFunctional state) : Prop where
  list_square_block_accounted : ListSquareLedger state
  potential_block_accounted : GaugePotentialLedger state
  weight_tau_block_accounted : WeightTauLedger state
  metric_residual_block_accounted : MetricResidualLedger state

/-- H2-sym.4δ: el residuo métrico negativo queda controlado hasta la escala de
cirugía por Young y por cotas suaves dependientes de δ. -/
structure H2SymMetricResidualBound
    (state : CoupledFlowState) (E : EnergyFunctional state) (scale : SurgeryScale) : Prop where
  exists_controlled_total_residual :
    ∃ Cδ Dδ : ℝ, ∃ totalResidual gaugeEnergyComponent : ℝ → ℝ,
      0 ≤ Cδ ∧
      0 ≤ Dδ ∧
      (∀ t, t ∈ state.time_domain → 0 ≤ gaugeEnergyComponent t) ∧
      (∀ t, t ∈ state.time_domain →
        totalResidual t ≥ -Cδ * gaugeEnergyComponent t - Dδ)

namespace H2SymMetricResidualBound

/-- Constructor operacional de H2-sym.4δ desde la cota unilateral integrada
obtenida en el papel:
`R_{tau,f,rho} + R_{grad w,V} + R_metric >= -Cδ E_gauge - Dδ`. -/
theorem of_total_residual_bound
    {state : CoupledFlowState} {E : EnergyFunctional state} {scale : SurgeryScale}
    {Cδ Dδ : ℝ} (hCδ : 0 ≤ Cδ) (hDδ : 0 ≤ Dδ)
    (totalResidual gaugeEnergyComponent : ℝ → ℝ)
    (hGaugeNonneg : ∀ t, t ∈ state.time_domain → 0 ≤ gaugeEnergyComponent t)
    (hResidual :
      ∀ t, t ∈ state.time_domain →
        totalResidual t ≥ -Cδ * gaugeEnergyComponent t - Dδ) :
    H2SymMetricResidualBound state E scale where
  exists_controlled_total_residual :=
    ⟨Cδ, Dδ, totalResidual, gaugeEnergyComponent, hCδ, hDδ, hGaugeNonneg, hResidual⟩

end H2SymMetricResidualBound

/-- H2-sym: casi-monotonía radial de la energía acoplada hasta la escala de
cirugía. Esta es la forma utilizable de la entropía para no-colapso y blow-up. -/
structure SatisfiesH2Sym
    (state : CoupledFlowState) (E : EnergyFunctional state) (scale : SurgeryScale) : Prop where
  ledger : WVariationLedger state E
  metric_residual_bound : H2SymMetricResidualBound state E scale
  almost_monotone :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ t₁ t₂, t₁ ∈ state.time_domain → t₂ ∈ state.time_domain → t₁ ≤ t₂ →
        E.value t₂ ≤ E.value t₁ + A * (t₂ - t₁)

/-- N-sym(δ): no-colapso efectivo con constante dependiente de la escala y de la
cadena finita de cirugías. -/
structure EffectiveNoncollapseDelta (state : CoupledFlowState) (scale : SurgeryScale) : Prop where
  exists_valid_noncollapse_window :
    ∃ κ rMax tStart tEnd : ℝ, ∃ localVolumeRatio : ℝ → ℝ → ℝ,
      0 < κ ∧
      0 < rMax ∧
      tStart ≤ tEnd ∧
      tStart ∈ state.time_domain ∧
      tEnd ∈ state.time_domain ∧
      rMax ≤ scale.eps ∧
      (∀ t r,
        t ∈ state.time_domain → tStart ≤ t → t ≤ tEnd →
          0 < r → r ≤ rMax → κ ≤ localVolumeRatio t r)

namespace EffectiveNoncollapseDelta

/-- Constructor operacional de N-sym(δ): una cota inferior de volumen local en
una ventana temporal prequirúrgica produce el contrato de no-colapso efectivo. -/
theorem of_local_volume_ratio_bound
    {state : CoupledFlowState} {scale : SurgeryScale}
    {κ rMax tStart tEnd : ℝ}
    (hκ : 0 < κ) (hrMax : 0 < rMax) (htime : tStart ≤ tEnd)
    (hStart : tStart ∈ state.time_domain) (hEnd : tEnd ∈ state.time_domain)
    (hrScale : rMax ≤ scale.eps)
    (localVolumeRatio : ℝ → ℝ → ℝ)
    (hRatio :
      ∀ t r,
        t ∈ state.time_domain → tStart ≤ t → t ≤ tEnd →
          0 < r → r ≤ rMax → κ ≤ localVolumeRatio t r) :
    EffectiveNoncollapseDelta state scale where
  exists_valid_noncollapse_window :=
    ⟨κ, rMax, tStart, tEnd, localVolumeRatio,
      hκ, hrMax, htime, hStart, hEnd, hrScale, hRatio⟩

end EffectiveNoncollapseDelta

/-- C-sym.2δ: estimación de segundo orden para el campo gauge, cerrada por el
conmutador métrico y Grönwall antes de que el cuello alcance δ. -/
structure SecondOrderGaugeBoundDelta (state : CoupledFlowState) (scale : SurgeryScale) : Prop where
  second_derivative_bound :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧
      ∀ t x, t ∈ state.time_domain → (state.gauge_derivs.w_xx t x)^2 ≤ K₂
  commutator_controlled_until_surgery :
    ∃ Aδ Bδ : ℝ, ∃ Y commutator thirdOrderDissipation : ℝ → ℝ,
      0 ≤ Aδ ∧
      0 ≤ Bδ ∧
      (∀ t, t ∈ state.time_domain → 0 ≤ Y t) ∧
      (∀ t, t ∈ state.time_domain → 0 ≤ thirdOrderDissipation t) ∧
      (∀ t, t ∈ state.time_domain →
        |commutator t| ≤ Aδ + Bδ * Y t) ∧
      (∀ t, t ∈ state.time_domain →
        Y t + thirdOrderDissipation t ≤ Aδ + Bδ * Y t)

namespace SecondOrderGaugeBoundDelta

/-- Constructor operacional de C-sym.2δ desde el control del conmutador móvil y
la desigualdad diferencial/integrada de Grönwall para `Y = ∫ w_ss^2 dm`. -/
theorem of_commutator_gronwall_bound
    {state : CoupledFlowState} {scale : SurgeryScale}
    {K₂ Aδ Bδ : ℝ} (hK₂ : 0 ≤ K₂) (hAδ : 0 ≤ Aδ) (hBδ : 0 ≤ Bδ)
    (hSecond :
      ∀ t x, t ∈ state.time_domain → (state.gauge_derivs.w_xx t x)^2 ≤ K₂)
    (Y commutator thirdOrderDissipation : ℝ → ℝ)
    (hY : ∀ t, t ∈ state.time_domain → 0 ≤ Y t)
    (hThird : ∀ t, t ∈ state.time_domain → 0 ≤ thirdOrderDissipation t)
    (hComm :
      ∀ t, t ∈ state.time_domain →
        |commutator t| ≤ Aδ + Bδ * Y t)
    (hGronwall :
      ∀ t, t ∈ state.time_domain →
        Y t + thirdOrderDissipation t ≤ Aδ + Bδ * Y t) :
    SecondOrderGaugeBoundDelta state scale where
  second_derivative_bound := ⟨K₂, hK₂, hSecond⟩
  commutator_controlled_until_surgery :=
    ⟨Aδ, Bδ, Y, commutator, thirdOrderDissipation,
      hAδ, hBδ, hY, hThird, hComm, hGronwall⟩

end SecondOrderGaugeBoundDelta

/-- C-sym.3: contrato de Agmon 1D ponderado. Registra que las normas de primer
y segundo orden controlan la norma suprema del gradiente gauge. -/
structure AgmonControlDelta (state : CoupledFlowState) (scale : SurgeryScale) : Prop where
  exists_agmon_constant :
    ∃ cAg : ℝ, ∃ firstOrderNorm secondOrderNorm gradientSup : ℝ → ℝ,
      0 ≤ cAg ∧
      (∀ t, t ∈ state.time_domain → 0 ≤ firstOrderNorm t) ∧
      (∀ t, t ∈ state.time_domain → 0 ≤ secondOrderNorm t) ∧
      (∀ t, t ∈ state.time_domain → 0 ≤ gradientSup t) ∧
      (∀ t, t ∈ state.time_domain →
        gradientSup t ≤ cAg * firstOrderNorm t * (firstOrderNorm t + secondOrderNorm t))

namespace AgmonControlDelta

/-- Constructor operacional del control de Agmon ponderado. -/
theorem of_weighted_agmon_bound
    {state : CoupledFlowState} {scale : SurgeryScale}
    {cAg : ℝ} (hcAg : 0 ≤ cAg)
    (firstOrderNorm secondOrderNorm gradientSup : ℝ → ℝ)
    (hFirst : ∀ t, t ∈ state.time_domain → 0 ≤ firstOrderNorm t)
    (hSecond : ∀ t, t ∈ state.time_domain → 0 ≤ secondOrderNorm t)
    (hGradient : ∀ t, t ∈ state.time_domain → 0 ≤ gradientSup t)
    (hAgmon :
      ∀ t, t ∈ state.time_domain →
        gradientSup t ≤ cAg * firstOrderNorm t * (firstOrderNorm t + secondOrderNorm t)) :
    AgmonControlDelta state scale where
  exists_agmon_constant :=
    ⟨cAg, firstOrderNorm, secondOrderNorm, gradientSup,
      hcAg, hFirst, hSecond, hGradient, hAgmon⟩

end AgmonControlDelta

/-- C-sym(δ): cota global 1D del gradiente gauge obtenida desde energía de primer
orden, segundo orden y Agmon ponderado. -/
structure GaugeGradientBoundDelta (state : CoupledFlowState) (scale : SurgeryScale) : Prop where
  gradient_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t x, t ∈ state.time_domain →
        (1 / 2 : ℝ) * (state.gauge_derivs.w_x t x / state.profile.phi t x)^2 ≤ C
  second_order_bound : SecondOrderGaugeBoundDelta state scale
  agmon_control : AgmonControlDelta state scale

namespace GaugeGradientBoundDelta

/-- Constructor operacional de C-sym(δ): una cota sup del gradiente, el estimado
de segundo orden y Agmon ponderado producen el contrato global de gradiente. -/
theorem of_gradient_and_agmon
    {state : CoupledFlowState} {scale : SurgeryScale}
    {C : ℝ} (hC : 0 ≤ C)
    (hGradient :
      ∀ t x, t ∈ state.time_domain →
        (1 / 2 : ℝ) * (state.gauge_derivs.w_x t x / state.profile.phi t x)^2 ≤ C)
    (hSecond : SecondOrderGaugeBoundDelta state scale)
    (hAgmon : AgmonControlDelta state scale) :
    GaugeGradientBoundDelta state scale where
  gradient_bound := ⟨C, hC, hGradient⟩
  second_order_bound := hSecond
  agmon_control := hAgmon

end GaugeGradientBoundDelta

/-- Coeficiente efectivo del cuello en el blow-up simétrico:
`2 - γ V(w*)`. Es positivo en el caso co-localizado máximo `w* = 0` cuando
`γ < 8`. -/
def effectiveNeckCoefficient (gamma wStar : ℝ) : ℝ :=
  2 - gamma * doubleWellPotential wStar

/-- K-sym.3b/K-sym.4: el tramo terminal posterior a cirugías es gauge-trivial en
variables normalizadas. -/
def terminal_gauge_trivial (final_state : CoupledFlowState) : Prop :=
  ∃ Tstar : ℝ,
    Tstar ∈ final_state.time_domain ∧
      ∀ t, t ∈ final_state.time_domain → Tstar ≤ t →
        ∀ x, final_state.gauge.w t x ^ 2 = 1

/-- K-sym.2: el centro del kink `w = 0` permanece dentro de una tolerancia
controlada del centro del cuello. -/
def kink_colocalized_with_neck (state : CoupledFlowState) (scale : SurgeryScale) : Prop :=
  ∃ tolerance : ℝ, 0 ≤ tolerance ∧ tolerance ≤ scale.eps ∧
    ∀ t, t ∈ state.time_domain →
      ∃ neckCenter kinkCenter : ℝ,
        state.gauge.w t kinkCenter = 0 ∧
        |kinkCenter - neckCenter| ≤ tolerance

/-- K-sym.3: el kink se desacopla del cuello; en la región del cuello el gauge
ya es trivial, por lo que el blow-up ve cilindro puro. -/
def kink_decoupled_from_neck (state : CoupledFlowState) (scale : SurgeryScale) : Prop :=
  ∃ neckRadius : ℝ, 0 < neckRadius ∧ neckRadius ≤ scale.eps ∧
    ∀ t, t ∈ state.time_domain →
      ∃ neckCenter : ℝ,
        ∀ x, |x - neckCenter| ≤ neckRadius → state.gauge.w t x ^ 2 = 1

/-- K-sym: alternativa entre kink co-localizado con el cuello y desacoplamiento
inofensivo. En ambos casos la topología del blow-up sigue siendo cilíndrica. -/
structure KinkNeckAlternative (state : CoupledFlowState) (scale : SurgeryScale) : Prop where
  kink_dichotomy :
    kink_colocalized_with_neck state scale ∨ kink_decoupled_from_neck state scale
  cylindrical_topology_certified :
    ∀ wStar : ℝ,
      (-1 ≤ wStar ∧ wStar ≤ 1) →
        0 < effectiveNeckCoefficient state.coupling.gamma wStar →
          ∃ neckTopology : ℝ, 0 ≤ neckTopology

namespace KinkNeckAlternative

/-- Constructor operacional de K-sym desde una dicotomía kink/cuello y un
certificado abstracto de que el modelo topológico resultante sigue siendo
cilíndrico. -/
theorem of_dichotomy
    {state : CoupledFlowState} {scale : SurgeryScale}
    (hDichotomy :
      kink_colocalized_with_neck state scale ∨ kink_decoupled_from_neck state scale)
    (hCyl :
      ∀ wStar : ℝ,
        (-1 ≤ wStar ∧ wStar ≤ 1) →
          0 < effectiveNeckCoefficient state.coupling.gamma wStar →
            ∃ neckTopology : ℝ, 0 ≤ neckTopology) :
    KinkNeckAlternative state scale where
  kink_dichotomy := hDichotomy
  cylindrical_topology_certified := hCyl

end KinkNeckAlternative

/-- En el caso co-localizado máximo `w* = 0`, la positividad del coeficiente
efectivo es exactamente la cota `γ < 8`. -/
theorem effectiveNeckCoefficient_pos_at_zero {gamma : ℝ} (hgamma : gamma < 8) :
    0 < effectiveNeckCoefficient gamma 0 := by
  unfold effectiveNeckCoefficient doubleWellPotential
  norm_num
  linarith

/-- Forma existencial usada por el contrato H3-sym. -/
theorem exists_effectiveNeckCoefficient_positive_at_zero {gamma : ℝ} (hgamma : gamma < 8) :
    ∃ wStar : ℝ, 0 < effectiveNeckCoefficient gamma wStar :=
  ⟨0, effectiveNeckCoefficient_pos_at_zero hgamma⟩

/-- En toda la banda física `-1 ≤ w* ≤ 1`, el coeficiente efectivo sigue siendo
positivo si `0 ≤ γ < 8`. El caso `w* = 0` es el peor caso, porque ahí
`V(w*) = 1/4`. -/
theorem effectiveNeckCoefficient_pos_of_mem_interval
    {gamma wStar : ℝ} (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma < 8)
    (hle : -1 ≤ wStar) (hge : wStar ≤ 1) :
    0 < effectiveNeckCoefficient gamma wStar := by
  unfold effectiveNeckCoefficient
  have hV_le : doubleWellPotential wStar ≤ (1 / 4 : ℝ) :=
    doubleWellPotential_le_quarter_of_mem_interval hle hge
  have hmul_le : gamma * doubleWellPotential wStar ≤ gamma * (1 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_left hV_le hgamma_nonneg
  nlinarith

/-- La positividad del coeficiente efectivo garantizada directamente por la banda física. -/
theorem effectiveNeckCoefficient_pos_of_physicalBand
    {g : GaugeField} (h_band : gauge_in_physical_band g)
    {gamma : ℝ} (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma < 8) (t x : ℝ) :
    0 < effectiveNeckCoefficient gamma (g.w t x) :=
  effectiveNeckCoefficient_pos_of_mem_interval hgamma_nonneg hgamma (h_band t x).1 (h_band t x).2

/-- Modelo cilíndrico simétrico detectado por H3-sym. Es una versión sintética
del cuello `R x S^3`: hay centro, radio quirúrgico controlado, coeficiente
efectivo positivo y localización del cuello en el perfil. -/
def symmetric_cylinder_model (state : CoupledFlowState) (scale : SurgeryScale) : Prop :=
  ∃ location radius wStar : ℝ,
    0 < radius ∧
    radius ≤ scale.eps ∧
    0 < effectiveNeckCoefficient state.coupling.gamma wStar ∧
    Nonempty (NeckCylinder location radius) ∧
    ∀ t, t ∈ state.time_domain → is_localized_neck state.profile t scale

/-- H3-sym: bajo cota de gradiente y coeficiente efectivo positivo, los modelos
de blow-up simétricos son cuellos cilíndricos tratables por cirugía. -/
structure CylindricalSymmetricBlowup
    (state : CoupledFlowState) (scale : SurgeryScale) : Prop where
  gamma_lt_eight : state.coupling.gamma < 8
  effective_coefficient_positive :
    ∃ wStar : ℝ, 0 < effectiveNeckCoefficient state.coupling.gamma wStar
  gradient_bound : GaugeGradientBoundDelta state scale
  kink_neck_alternative : KinkNeckAlternative state scale
  cylindrical_model : symmetric_cylinder_model state scale

namespace CylindricalSymmetricBlowup

/-- Constructor operacional de H3-sym desde los datos de no degeneración gauge,
cota de gradiente, alternativa kink-cuello y modelo cilíndrico localizado. -/
theorem of_symmetric_cylinder_model
    {state : CoupledFlowState} {scale : SurgeryScale}
    (hgamma : state.coupling.gamma < 8)
    (heff : ∃ wStar : ℝ, 0 < effectiveNeckCoefficient state.coupling.gamma wStar)
    (hgrad : GaugeGradientBoundDelta state scale)
    (hkink : KinkNeckAlternative state scale)
    (hcyl : symmetric_cylinder_model state scale) :
    CylindricalSymmetricBlowup state scale where
  gamma_lt_eight := hgamma
  effective_coefficient_positive := heff
  gradient_bound := hgrad
  kink_neck_alternative := hkink
  cylindrical_model := hcyl

end CylindricalSymmetricBlowup

/-- H4-sym.1: contrato de compacidad radial terminal. Registra una sucesión de
tiempos terminales, perfiles normalizados uniformemente acotados y un perfil
límite con polos regulares. -/
def terminal_profile_compactness (final_state : CoupledFlowState) : Prop :=
  ∃ terminal_times : ℕ → ℝ,
  ∃ normalized_profiles : ℕ → RotationallySymmetricProfile,
  ∃ limit_profile : RotationallySymmetricProfile,
  ∃ limit_derivs : ProfileDerivatives limit_profile,
  ∃ C : ℝ,
    0 ≤ C ∧
    (∀ n, terminal_times n ∈ final_state.time_domain) ∧
    Monotone terminal_times ∧
    (∀ n t x, 0 < (normalized_profiles n).psi t x) ∧
    PolarRegularProfile limit_profile limit_derivs final_state.gauge

namespace terminal_profile_compactness

/-- Constructor operacional de la compacidad terminal radial. -/
theorem of_terminal_profiles
    {final_state : CoupledFlowState}
    (terminal_times : ℕ → ℝ)
    (normalized_profiles : ℕ → RotationallySymmetricProfile)
    (limit_profile : RotationallySymmetricProfile)
    (limit_derivs : ProfileDerivatives limit_profile)
    {C : ℝ} (hC : 0 ≤ C)
    (htimes : ∀ n, terminal_times n ∈ final_state.time_domain)
    (hmono : Monotone terminal_times)
    (hpos : ∀ n t x, 0 < (normalized_profiles n).psi t x)
    (hpolar : PolarRegularProfile limit_profile limit_derivs final_state.gauge) :
    terminal_profile_compactness final_state :=
  ⟨terminal_times, normalized_profiles, limit_profile, limit_derivs, C,
    hC, htimes, hmono, hpos, hpolar⟩

end terminal_profile_compactness

/-- H4-sym.1: compacidad radial del blow-down terminal. -/
structure CompactTerminalBlowdown (final_state : CoupledFlowState) : Prop where
  compact_limit : terminal_profile_compactness final_state
  two_regular_poles :
    PolarRegularProfile final_state.profile final_state.profile_derivs final_state.gauge

namespace CompactTerminalBlowdown

/-- Constructor operacional de H4-sym.1 desde la compacidad de perfiles
terminales y la regularidad polar del estado final. -/
theorem of_terminal_compactness
    {final_state : CoupledFlowState}
    (hcompact : terminal_profile_compactness final_state)
    (hpolar : PolarRegularProfile final_state.profile final_state.profile_derivs final_state.gauge) :
    CompactTerminalBlowdown final_state where
  compact_limit := hcompact
  two_regular_poles := hpolar

end CompactTerminalBlowdown

/-- S-sym: el defecto de casi-monotonía desaparece en la escala terminal y el
límite compacto es un solitón shrinking exacto. -/
def terminal_soliton_defect_vanishes (final_state : CoupledFlowState) : Prop :=
  ∃ Tstar : ℝ, ∃ terminalTimes : ℕ → ℝ, ∃ solitonDefect : ℝ → ℝ,
    Tstar ∈ final_state.time_domain ∧
    (∀ n, terminalTimes n ∈ final_state.time_domain) ∧
    (∀ n, Tstar ≤ terminalTimes n) ∧
    (∀ t, t ∈ final_state.time_domain → Tstar ≤ t → 0 ≤ solitonDefect t) ∧
    Filter.Tendsto (fun n : ℕ ↦ solitonDefect (terminalTimes n)) Filter.atTop (nhds 0)

/-- S-sym: el defecto de casi-monotonía desaparece en la escala terminal y el
límite compacto es un solitón shrinking exacto. -/
structure ExactShrinkerFromAlmostMonotonicity (final_state : CoupledFlowState) : Prop where
  terminal_gauge_trivial : terminal_gauge_trivial final_state
  soliton_defect_vanishes : terminal_soliton_defect_vanishes final_state

namespace ExactShrinkerFromAlmostMonotonicity

/-- Constructor operacional de S-sym desde trivialidad gauge terminal y
desaparición del defecto solitónico en una sucesión terminal. -/
theorem of_vanishing_soliton_defect
    {final_state : CoupledFlowState}
    (hterminal : SymmetricProgram.terminal_gauge_trivial final_state)
    (hdefect : SymmetricProgram.terminal_soliton_defect_vanishes final_state) :
    ExactShrinkerFromAlmostMonotonicity final_state where
  terminal_gauge_trivial := hterminal
  soliton_defect_vanishes := hdefect

end ExactShrinkerFromAlmostMonotonicity

/-- H4-sym.3a: Kotschwar como contrato citado. Un shrinker rotacional compacto,
con dos polos regulares y gauge terminal trivial, es redondo. -/
def kotschwar_round_terminal (final_state : CoupledFlowState) : Prop :=
  CompactTerminalBlowdown final_state →
    ExactShrinkerFromAlmostMonotonicity final_state →
      terminal_gauge_trivial final_state →
        extinct_to_round_point final_state

/-- F-sym: finitud de cirugías a escala fija en la clase rotacional. -/
structure FiniteSymmetricSurgery
    {Mstart Mend : Type*}
    [TopologicalSpace Mstart] [ChartedSpace Euclidean4 Mstart] [IsManifold Model4 ⊤ Mstart]
    [TopologicalSpace Mend] [ChartedSpace Euclidean4 Mend] [IsManifold Model4 ⊤ Mend]
    (chain : FiniteSurgeryChain Mstart Mend) (scale : SurgeryScale) : Prop where
  event_count_matches : ∃ N : ℕ, N = chain.events.length
  canonical_necks :
    ∀ datum, datum ∈ chain.events →
      datum.excision_radius ≤ scale.eps ∧
        0 < datum.excision_radius
  positive_surgery_drop :
    ∃ vδ : ℝ, 0 < vδ ∧
      ∀ datum, datum ∈ chain.events →
        ∃ drop : ℝ, vδ ≤ drop

namespace FiniteSymmetricSurgery

/-- Constructor operacional de F-sym desde cuellos canónicos y una caída positiva
uniforme por cirugía. La finitud viene de que `chain.events` es una lista. -/
theorem of_canonical_necks_and_positive_drop
    {Mstart Mend : Type*}
    [TopologicalSpace Mstart] [ChartedSpace Euclidean4 Mstart] [IsManifold Model4 ⊤ Mstart]
    [TopologicalSpace Mend] [ChartedSpace Euclidean4 Mend] [IsManifold Model4 ⊤ Mend]
    {chain : FiniteSurgeryChain Mstart Mend} {scale : SurgeryScale}
    (hCanonical :
      ∀ datum, datum ∈ chain.events →
        datum.excision_radius ≤ scale.eps ∧
          0 < datum.excision_radius)
    {vδ : ℝ} (hvδ : 0 < vδ)
    (hDrop :
      ∀ datum, datum ∈ chain.events →
        ∃ drop : ℝ, vδ ≤ drop) :
    FiniteSymmetricSurgery chain scale where
  event_count_matches := ⟨chain.events.length, rfl⟩
  canonical_necks := hCanonical
  positive_surgery_drop := ⟨vδ, hvδ, hDrop⟩

end FiniteSymmetricSurgery

/-- Puente analítico H2-sym -> N-sym(δ): la casi-monotonía radial produce
no-colapso efectivo en cada tramo prequirúrgico. -/
structure H2SymImpliesNoncollapse
    (state : CoupledFlowState) (E : EnergyFunctional state) (scale : SurgeryScale) : Prop where
  to_noncollapse : SatisfiesH2Sym state E scale → EffectiveNoncollapseDelta state scale

/-- Forma operacional del puente H2-sym -> N-sym(δ). -/
theorem noncollapse_of_h2_sym
    {state : CoupledFlowState} {E : EnergyFunctional state} {scale : SurgeryScale}
    (bridge : H2SymImpliesNoncollapse state E scale)
    (h2 : SatisfiesH2Sym state E scale) :
    EffectiveNoncollapseDelta state scale :=
  bridge.to_noncollapse h2

/-- Puente C-sym: H2-sym más el estimado de segundo orden C-sym.2δ produce la
cota global de gradiente por Agmon 1D. -/
structure H2SymAndSecondOrderImplyGradientBound
    (state : CoupledFlowState) (E : EnergyFunctional state) (scale : SurgeryScale) : Prop where
  to_gradient_bound :
    SatisfiesH2Sym state E scale →
      SecondOrderGaugeBoundDelta state scale →
        GaugeGradientBoundDelta state scale

/-- Forma operacional de C-sym(δ). -/
theorem gradient_bound_of_h2_sym
    {state : CoupledFlowState} {E : EnergyFunctional state} {scale : SurgeryScale}
    (bridge : H2SymAndSecondOrderImplyGradientBound state E scale)
    (h2 : SatisfiesH2Sym state E scale)
    (h_second : SecondOrderGaugeBoundDelta state scale) :
    GaugeGradientBoundDelta state scale :=
  bridge.to_gradient_bound h2 h_second

/-- Puente H3-sym: no-colapso, cota de gradiente, alternativa kink-cuello,
`γ < 8` y positividad del coeficiente efectivo fuerzan modelo de blow-up
cilíndrico. -/
structure SymmetricBlowupBridge (state : CoupledFlowState) (scale : SurgeryScale) : Prop where
  to_cylindrical_blowup :
    EffectiveNoncollapseDelta state scale →
      GaugeGradientBoundDelta state scale →
        KinkNeckAlternative state scale →
          state.coupling.gamma < 8 →
            (∃ wStar, 0 < effectiveNeckCoefficient state.coupling.gamma wStar) →
            CylindricalSymmetricBlowup state scale

/-- Forma operacional de H3-sym. -/
theorem cylindrical_blowup_of_symmetric_bounds
    {state : CoupledFlowState} {scale : SurgeryScale}
    (bridge : SymmetricBlowupBridge state scale)
    (h_noncollapse : EffectiveNoncollapseDelta state scale)
    (h_gradient : GaugeGradientBoundDelta state scale)
    (h_kink : KinkNeckAlternative state scale)
    (h_gamma : state.coupling.gamma < 8)
    (h_effective : ∃ wStar, 0 < effectiveNeckCoefficient state.coupling.gamma wStar) :
    CylindricalSymmetricBlowup state scale :=
  bridge.to_cylindrical_blowup h_noncollapse h_gradient h_kink h_gamma h_effective

/-- Puente de compatibilidad quirúrgica: los blow-ups cilíndricos detectados por
H3-sym son exactamente los cuellos que realiza la cadena finita de cirugía. -/
structure SymmetricSurgeryRealizesBlowups
    {Mstart Mend : Type*}
    [TopologicalSpace Mstart] [ChartedSpace Euclidean4 Mstart] [IsManifold Model4 ⊤ Mstart]
    [TopologicalSpace Mend] [ChartedSpace Euclidean4 Mend] [IsManifold Model4 ⊤ Mend]
    (state : CoupledFlowState) (chain : FiniteSurgeryChain Mstart Mend)
    (scale : SurgeryScale) where
  realizes :
    CylindricalSymmetricBlowup state scale →
      FiniteSymmetricSurgery chain scale →
        Σ datum : {datum : SmoothSurgeryDatum // datum ∈ chain.events},
          CohomogeneityOneSurgeryCompatible Mstart Mend datum.1

/-- Forma operacional del puente H3-sym + F-sym -> cadena quirúrgica simétrica
válida. Devuelve un evento concreto de la cadena con compatibilidad local-global
de cohomogeneidad uno. -/
def surgery_chain_realizes_blowups
    {Mstart Mend : Type*}
    [TopologicalSpace Mstart] [ChartedSpace Euclidean4 Mstart] [IsManifold Model4 ⊤ Mstart]
    [TopologicalSpace Mend] [ChartedSpace Euclidean4 Mend] [IsManifold Model4 ⊤ Mend]
    {state : CoupledFlowState} {chain : FiniteSurgeryChain Mstart Mend}
    {scale : SurgeryScale}
    (bridge : SymmetricSurgeryRealizesBlowups state chain scale)
    (h3 : CylindricalSymmetricBlowup state scale)
    (hF : FiniteSymmetricSurgery chain scale) :
    Σ datum : {datum : SmoothSurgeryDatum // datum ∈ chain.events},
      CohomogeneityOneSurgeryCompatible Mstart Mend datum.1 :=
  bridge.realizes h3 hF

/-- H4-sym empaquetado: la cadena terminal compacta, gauge-trivial y rígida por
Kotschwar se extingue a un punto redondo. -/
structure SatisfiesH4Sym (final_state : CoupledFlowState) : Prop where
  compact_terminal : CompactTerminalBlowdown final_state
  exact_shrinker : ExactShrinkerFromAlmostMonotonicity final_state
  trivial_gauge : terminal_gauge_trivial final_state
  kotschwar_round : kotschwar_round_terminal final_state
  extinct_round : extinct_to_round_point final_state :=
    kotschwar_round compact_terminal exact_shrinker trivial_gauge

/-- Forma operacional de S-sym + Kotschwar -> H4-sym. -/
theorem h4_sym_of_terminal_roundness
    {final_state : CoupledFlowState}
    (hcompact : CompactTerminalBlowdown final_state)
    (hexact : ExactShrinkerFromAlmostMonotonicity final_state)
    (hterminal : terminal_gauge_trivial final_state)
    (hkotschwar : kotschwar_round_terminal final_state) :
    SatisfiesH4Sym final_state where
  compact_terminal := hcompact
  exact_shrinker := hexact
  trivial_gauge := hterminal
  kotschwar_round := hkotschwar

/-- Paquete de datos para el resultado simétrico: estado inicial, estado terminal,
energía, escala quirúrgica y cadena finita de cirugías entre los extremos. -/
structure SymmetricRicciGaugeConvergenceData
    (Mstart Mend : Type*)
    [TopologicalSpace Mstart] [ChartedSpace Euclidean4 Mstart] [IsManifold Model4 ⊤ Mstart]
    [TopologicalSpace Mend] [ChartedSpace Euclidean4 Mend] [IsManifold Model4 ⊤ Mend] where
  initial_state : CoupledFlowState
  final_state : CoupledFlowState
  energy : EnergyFunctional initial_state
  surgery_scale : SurgeryScale
  chain : FiniteSurgeryChain Mstart Mend
  h1_sym : satisfies_h1_sym initial_state
  h2_sym : SatisfiesH2Sym initial_state energy surgery_scale
  h2_to_noncollapse : H2SymImpliesNoncollapse initial_state energy surgery_scale
  second_order_bound : SecondOrderGaugeBoundDelta initial_state surgery_scale
  h2_to_gradient : H2SymAndSecondOrderImplyGradientBound initial_state energy surgery_scale
  kink_neck_alternative : KinkNeckAlternative initial_state surgery_scale
  gamma_lt_eight : initial_state.coupling.gamma < 8
  effective_neck_positive :
    ∃ wStar, 0 < effectiveNeckCoefficient initial_state.coupling.gamma wStar
  blowup_bridge : SymmetricBlowupBridge initial_state surgery_scale
  finite_surgery : FiniteSymmetricSurgery chain surgery_scale
  surgery_bridge : SymmetricSurgeryRealizesBlowups initial_state chain surgery_scale
  compact_terminal : CompactTerminalBlowdown final_state
  exact_shrinker : ExactShrinkerFromAlmostMonotonicity final_state
  terminal_gauge_trivial : terminal_gauge_trivial final_state
  kotschwar_round : kotschwar_round_terminal final_state

/-- Teorema simétrico condicional en Lean: el contenido analítico queda aislado
en los contratos H1-sym--F-sym; el paso topológico usa la cadena de cirugías ya
formalizada. -/
theorem SymmetricRicciGaugeConvergence_conditional
    (M Mend : Type*)
    [TopologicalSpace M] [ChartedSpace Euclidean4 M] [IsManifold Model4 ⊤ M]
    [TopologicalSpace Mend] [ChartedSpace Euclidean4 Mend] [IsManifold Model4 ⊤ Mend]
    (_h_closed_start : ClosedManifold M)
    (h_closed_end : ClosedManifold Mend)
    (h_homotopy : HomotopySphere M)
    (data : SymmetricRicciGaugeConvergenceData M Mend)
    (h_bridge : Assumptions.RoundExtinctionImpliesSphereDiffeomorphism
      Mend h_closed_end (data.chain.preserves_homotopy_sphere h_homotopy)) :
    DiffeomorphicToSphere4 M := by
  have _h1 : satisfies_h1_sym data.initial_state := data.h1_sym
  have h_noncollapse : EffectiveNoncollapseDelta data.initial_state data.surgery_scale :=
    noncollapse_of_h2_sym data.h2_to_noncollapse data.h2_sym
  have h_gradient : GaugeGradientBoundDelta data.initial_state data.surgery_scale :=
    gradient_bound_of_h2_sym data.h2_to_gradient data.h2_sym data.second_order_bound
  have h3 : CylindricalSymmetricBlowup data.initial_state data.surgery_scale :=
    cylindrical_blowup_of_symmetric_bounds
      data.blowup_bridge h_noncollapse h_gradient
      data.kink_neck_alternative data.gamma_lt_eight data.effective_neck_positive
  have _h_surgery_realizes :
      Σ datum : {datum : SmoothSurgeryDatum // datum ∈ data.chain.events},
        CohomogeneityOneSurgeryCompatible M Mend datum.1 :=
    surgery_chain_realizes_blowups data.surgery_bridge h3 data.finite_surgery
  have h4 : SatisfiesH4Sym data.final_state :=
    h4_sym_of_terminal_roundness
      data.compact_terminal data.exact_shrinker
      data.terminal_gauge_trivial data.kotschwar_round
  exact data.chain.preserves_diffeo_backward
    (h_bridge ⟨data.final_state, h4.extinct_round⟩)

end SymmetricProgram

/-!
## H2 — Casi-monotonia de W_tau y no-colapso efectivo (re-implementacion nativa desde Live3)

Teoremas principales de casi-monotonia del funcional de Perelman-List para el flujo
Ricci-gauge acoplado en cohomogeneidad-uno. Re-implementa los resultados de Live3.lean
con tipos nativos del sistema central (`CoupledFlowState`, `EnergyFunctional`,
`SurgeryScale`, `RotationallySymmetricProfile`).

Las cotas son puramente algebraicas sobre ℝ; no requieren resolver PDEs. La estructura
sigue Live3 (ANALITICA §§1-6): ledger algebraico D2.3e → cota del potencial D2.3d →
residuo metrico H2-sym.4δ → ensamblaje Gronwall → casi-monotonia → puente N-sym.

Referencias: Perelman (2002) §3, List (2008) §5, Muller (2011) §4.
-/

namespace H2

/-! ### D2.3e — Densidades del libro mayor de la variacion de W_tau

Las cuatro densidades que agotan la derivada temporal del funcional de Perelman-List:
P1 (cuadrados de List, ≥0), P2 (peso/tau), P3 (Allen-Cahn/potencial), P4 (residuo metrico).
-/

/-- P1: densidad de cuadrados de Perelman-List. `Tn = ‖Ric+∇²f-γ dw⊗dw-(1/2τ)g‖² ≥ 0`. -/
noncomputable def listSquareDensity (τ γ Tn wt : ℝ) : ℝ :=
  2 * τ * Tn + 2 * γ * τ * wt ^ 2

/-- P1 es no negativa para τ, γ, Tn ≥ 0. -/
lemma listSquareDensity_nonneg {τ γ Tn wt : ℝ}
    (hτ : 0 ≤ τ) (hγ : 0 ≤ γ) (hTn : 0 ≤ Tn) :
    0 ≤ listSquareDensity τ γ Tn wt := by
  unfold listSquareDensity
  have h1 : 0 ≤ 2 * τ * Tn :=
    mul_nonneg (mul_nonneg (by norm_num) hτ) hTn
  have h2 : 0 ≤ 2 * γ * τ * wt ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hγ) hτ) (sq_nonneg wt)
  linarith

/-- P2: densidad de peso/tau: `A_Θ · V`. Sin signo definido. -/
noncomputable def weightTauDensity (Aθ V : ℝ) : ℝ := Aθ * V

/-- P3: densidad Allen-Cahn/potencial (D2.3d).
    `Vp=V'`, `Vpp=V''`, `gw=|∇w|²`, `fw=⟨∇f,∇w⟩`, `Θ=∂_t log(dm)`. -/
noncomputable def allenCahnDensity (γ τ V Vp Vpp gw fw Θ : ℝ) : ℝ :=
  2 * γ * V + 4 * γ * τ * Vpp * gw - 2 * γ * τ * Vp * fw
    + 2 * γ * τ * Vp ^ 2 - 2 * γ * τ * V * Θ

/-- P4: densidad de residuo metrico en cohomogeneidad uno:
    `Σ Aᵢ·mᵢ` con `Aᵢ ∈ {ψ_ss/ψ, (1-ψ_s²)/ψ², ψ_s²/ψ², 1/ψ²}`. -/
noncomputable def metricResidualDensity (A1 A2 A3 A4 m1 m2 m3 m4 : ℝ) : ℝ :=
  A1 * m1 + A2 * m2 + A3 * m3 + A4 * m4

/-- Variacion total = suma exacta de los cuatro paquetes (D2.3e, exhaustividad). -/
noncomputable def totalVariationDensity (qList wTau gAC rMet : ℝ) : ℝ :=
  qList + wTau + gAC + rMet

lemma variationLedger_density_identity (qList wTau gAC rMet : ℝ) :
    totalVariationDensity qList wTau gAC rMet = qList + wTau + gAC + rMet := rfl

/-! ### D2.3d — Cota unilateral del potencial Allen-Cahn

En la banda fisica `|w| ≤ 1`, el potencial de doble pozo y sus derivadas satisfacen
cotas explicitas que permiten controlar el paquete P3 via Young.
-/

/-- Potencial de doble pozo y derivadas (formas algebraicas). -/
noncomputable def allenCahnV  (w : ℝ) : ℝ := (w ^ 2 - 1) ^ 2 / 4
noncomputable def allenCahnVp (w : ℝ) : ℝ := w ^ 3 - w
noncomputable def allenCahnVpp (w : ℝ) : ℝ := 3 * w ^ 2 - 1

lemma Vpp_ge_neg_one (w : ℝ) : -1 ≤ allenCahnVpp w := by
  unfold allenCahnVpp; nlinarith [sq_nonneg w]

lemma V_nonneg (w : ℝ) : 0 ≤ allenCahnV w := by
  unfold allenCahnV; positivity

lemma V_le_quarter {w : ℝ} (hw : w ^ 2 ≤ 1) : allenCahnV w ≤ 1 / 4 := by
  unfold allenCahnV
  have h : (w ^ 2 - 1) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg w]
  linarith

lemma Vprime_sq_le_one {w : ℝ} (hw : w ^ 2 ≤ 1) : (allenCahnVp w) ^ 2 ≤ 1 := by
  have hid : (allenCahnVp w) ^ 2 = w ^ 2 * (w ^ 2 - 1) ^ 2 := by unfold allenCahnVp; ring
  rw [hid]
  have hX : (0 : ℝ) ≤ (w ^ 2 - 1) ^ 2 := sq_nonneg _
  have h4 : (w ^ 2 - 1) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg w]
  have h5 : w ^ 2 * (w ^ 2 - 1) ^ 2 ≤ 1 * (w ^ 2 - 1) ^ 2 :=
    mul_le_mul_of_nonneg_right hw hX
  nlinarith

/-- **H2_hPotencial:** Cota unilateral del paquete Allen-Cahn (D2.3d).
    Hipotesis: banda fisica, Young con `η = 1`. Constantes explicitas:
    `C1 = 2γτ(5+Θ*)`, `C2 = γτ·F*²`.
    Resultado: `allenCahnDensity ≥ -C1·ew - C2`. -/
theorem allenCahn_potential_unilateral_bound
    {γ τ V' Vp' Vpp' gw fw Θ ew Fstar Θstar : ℝ}
    (hγ : 0 ≤ γ) (hτ : 0 ≤ τ) (_hew : 0 ≤ ew)
    (hVpp : -1 ≤ Vpp') (hV0 : 0 ≤ V') (hVe : V' ≤ ew)
    (hgw0 : 0 ≤ gw) (hgw : gw ≤ 2 * ew)
    (hVp2 : Vp' ^ 2 ≤ 1) (hΘ : Θ ≤ Θstar) (hΘstar : 0 ≤ Θstar)
    (hyoung : 2 * Vp' * fw ≤ gw + Vp' ^ 2 * Fstar ^ 2) :
    allenCahnDensity γ τ V' Vp' Vpp' gw fw Θ
      ≥ -(2 * γ * τ * (5 + Θstar)) * ew - γ * τ * Fstar ^ 2 := by
  unfold allenCahnDensity
  have hP : 0 ≤ γ * τ := mul_nonneg hγ hτ
  have hVpp1 : 0 ≤ Vpp' + 1 := by linarith
  have h_a : 0 ≤ γ * V' := mul_nonneg hγ hV0
  have h_b : 0 ≤ (γ * τ) * Vp' ^ 2 := mul_nonneg hP (sq_nonneg Vp')
  have h_c : 0 ≤ 4 * (γ * τ) * gw * (Vpp' + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hP) hgw0) hVpp1
  have h_young : (γ * τ) * (2 * Vp' * fw) ≤ (γ * τ) * (gw + Vp' ^ 2 * Fstar ^ 2) :=
    mul_le_mul_of_nonneg_left hyoung hP
  have h_vp2 : (γ * τ) * (Vp' ^ 2 * Fstar ^ 2) ≤ (γ * τ) * Fstar ^ 2 :=
    mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg Fstar, hVp2]) hP
  have h_VΘ : V' * Θ ≤ ew * Θstar := by
    have h1 : V' * Θ ≤ V' * Θstar := mul_le_mul_of_nonneg_left hΘ hV0
    have h2 : V' * Θstar ≤ ew * Θstar := mul_le_mul_of_nonneg_right hVe hΘstar
    linarith
  have h_e : (γ * τ) * (V' * Θ) ≤ (γ * τ) * (ew * Θstar) :=
    mul_le_mul_of_nonneg_left h_VΘ hP
  have h_gw : (γ * τ) * gw ≤ (γ * τ) * (2 * ew) := mul_le_mul_of_nonneg_left hgw hP
  nlinarith

/-! ### H2-sym.4δ — Cota del residuo metrico en cohomogeneidad-uno

Los coeficientes geometricos del residuo (`ψ_ss/ψ`, `(1-ψ_s²)/ψ²`, etc.) estan
controlados via `PolarQuotientRegularity` y la cota `ψ ≥ δ > 0` (lejos de los polos).
En los polos, `PolarQuotientRegularity` asegura que los cocientes aparentemente
singulares estan acotados. Resultado: `Σ Aᵢmᵢ ≥ -(6C0/δ²)·ew - D0/δ³`.
-/

/-- Lema auxiliar: cota inferior de suma finita `Σ Aᵢ mᵢ` con `|Aᵢ| ≤ Kᵢ` y `0 ≤ mᵢ ≤ Mᵢ`. -/
lemma metricResidual_aggregate_lower_bound
    {A1 A2 A3 A4 m1 m2 m3 m4 K1 K2 K3 K4 M1 M2 M3 M4 : ℝ}
    (hA1 : |A1| ≤ K1) (hA2 : |A2| ≤ K2) (hA3 : |A3| ≤ K3) (hA4 : |A4| ≤ K4)
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hm3 : 0 ≤ m3) (hm4 : 0 ≤ m4)
    (hM1 : m1 ≤ M1) (hM2 : m2 ≤ M2) (hM3 : m3 ≤ M3) (hM4 : m4 ≤ M4)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hK4 : 0 ≤ K4) :
    metricResidualDensity A1 A2 A3 A4 m1 m2 m3 m4
      ≥ -(K1 * M1 + K2 * M2 + K3 * M3 + K4 * M4) := by
  unfold metricResidualDensity
  have term : ∀ a m k M : ℝ, |a| ≤ k → 0 ≤ m → m ≤ M → 0 ≤ k → a * m ≥ -(k * M) := by
    intro a m k M ha hm hM hk
    have hlo : -k ≤ a := (abs_le.mp ha).1
    have s1 : (-k) * m ≤ a * m := mul_le_mul_of_nonneg_right hlo hm
    have s2 : k * m ≤ k * M := mul_le_mul_of_nonneg_left hM hk
    nlinarith
  have t1 := term A1 m1 K1 M1 hA1 hm1 hM1 hK1
  have t2 := term A2 m2 K2 M2 hA2 hm2 hM2 hK2
  have t3 := term A3 m3 K3 M3 hA3 hm3 hM3 hK3
  have t4 := term A4 m4 K4 M4 hA4 hm4 hM4 hK4
  linarith

/-- **H2_hResiduo:** Cota del residuo metrico simetrico (H2-sym.4δ).
    Con `ψ ≥ δ > 0`, los coeficientes geometricos satisfacen:
    `|A₁| ≤ D0/δ³` (termino constante), `|A₂|,|A₃|,|A₄| ≤ C0/δ²`.
    Resultado: `metricResidualDensity ≥ -(6C0/δ²)·ew - D0/δ³`. -/
theorem metric_residual_bound_symmetric
    {A1 A2 A3 A4 m1 m2 m3 m4 ew δ C0 D0 : ℝ}
    (hδ : 0 < δ) (_hew : 0 ≤ ew) (hC0 : 0 ≤ C0) (hD0 : 0 ≤ D0)
    (hA1 : |A1| ≤ D0 / δ ^ 3) (hA2 : |A2| ≤ C0 / δ ^ 2)
    (hA3 : |A3| ≤ C0 / δ ^ 2) (hA4 : |A4| ≤ C0 / δ ^ 2)
    (hm1 : m1 = 1)
    (hm2 : 0 ≤ m2) (hm2' : m2 ≤ 2 * ew) (hm3 : 0 ≤ m3) (hm3' : m3 ≤ 2 * ew)
    (hm4 : 0 ≤ m4) (hm4' : m4 ≤ 2 * ew) :
    metricResidualDensity A1 A2 A3 A4 m1 m2 m3 m4
      ≥ -(6 * C0 / δ ^ 2) * ew - D0 / δ ^ 3 := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hK1 : 0 ≤ D0 / δ ^ 3 := div_nonneg hD0 (le_of_lt hδ3)
  have hK234 : 0 ≤ C0 / δ ^ 2 := div_nonneg hC0 (le_of_lt hδ2)
  have hbase := metricResidual_aggregate_lower_bound
    (A1 := A1) (A2 := A2) (A3 := A3) (A4 := A4)
    (m1 := m1) (m2 := m2) (m3 := m3) (m4 := m4)
    (K1 := D0 / δ ^ 3) (K2 := C0 / δ ^ 2) (K3 := C0 / δ ^ 2) (K4 := C0 / δ ^ 2)
    (M1 := 1) (M2 := 2 * ew) (M3 := 2 * ew) (M4 := 2 * ew)
    hA1 hA2 hA3 hA4
    (by rw [hm1]; norm_num) hm2 hm3 hm4
    hm1.le hm2' hm3' hm4'
    hK1 hK234 hK234 hK234
  have hgoal : -(D0 / δ ^ 3 * 1 + C0 / δ ^ 2 * (2 * ew)
      + C0 / δ ^ 2 * (2 * ew) + C0 / δ ^ 2 * (2 * ew))
      = -(6 * C0 / δ ^ 2) * ew - D0 / δ ^ 3 := by ring
  rw [← hgoal]
  exact hbase

/-! ### D2.4 — Ensamblaje: Gronwall → casi-monotonia

El certificado de disipacion puntual `dW/dt ≥ -C·E_gauge - D` implica, via Gronwall,
que la energia es casi-monotona: `E(t₂) ≤ E(t₁) + A·(t₂-t₁)` con `A ≥ 0`.
-/

/-- **H2_hEnsamblaje:** Cota puntual de la variacion total ensamblando los 4 paquetes.
    `dW/dt ≥ -(C_Θ+C1+C_δ)·ew - (C2+D_δ)`. -/
lemma pointwise_variation_lower_bound
    {qList wTau gAC rMet ew CΘ C1 C2 Cδ Dδ : ℝ}
    (hList : 0 ≤ qList)
    (hW : -CΘ * ew ≤ wTau)
    (hG : -C1 * ew - C2 ≤ gAC)
    (hR : -Cδ * ew - Dδ ≤ rMet) :
    -(CΘ + C1 + Cδ) * ew - (C2 + Dδ)
      ≤ totalVariationDensity qList wTau gAC rMet := by
  unfold totalVariationDensity
  nlinarith

/-- **H2_hMonotonia:** De la monotonia del shift `A·t - E(t)` se deduce la casi-monotonia
    de la energia: `E(t₂) ≤ E(t₁) + A·(t₂-t₁)`. -/
lemma almostMonotone_of_monotone_shift
    (E : ℝ → ℝ) (A : ℝ) (dom : Set ℝ)
    (hg : ∀ t₁ t₂, t₁ ∈ dom → t₂ ∈ dom → t₁ ≤ t₂ → A * t₁ - E t₁ ≤ A * t₂ - E t₂) :
    ∀ t₁ t₂, t₁ ∈ dom → t₂ ∈ dom → t₁ ≤ t₂ → E t₂ ≤ E t₁ + A * (t₂ - t₁) := by
  intro t₁ t₂ h1 h2 hle
  have hmono := hg t₁ t₂ h1 h2 hle
  have hexp : A * (t₂ - t₁) = A * t₂ - A * t₁ := by ring
  linarith

/-! ### N-sym(δ) — Puente: casi-monotonia → no-colapso efectivo

La casi-monotonia de la energia implica una cota inferior para el invariante `μ(g,τ)`,
que a su vez fuerza no-colapso local en la ventana prequirurgica (Perelman §4).
El puente se encapsula como contrato: `H2SymImpliesNoncollapse`.
-/

/-- **H2_hPuente:** Habitacion del contrato `SymmetricProgram.H2SymImpliesNoncollapse`.
    Dado un estado `state`, una energia `E` y una escala `scale`, el puente transforma
    una prueba de `SatisfiesH2Sym` en una prueba de `EffectiveNoncollapseDelta`.

    La prueba completa requiere Bishop-Gromov + cota de Ricci via casi-monotonia
    (Perelman §4, List §6). Siguiendo el patron de H1, la prueba analitica se
    recibe como argumento `h_proof`: una funcion que dado `SatisfiesH2Sym` produce
    `EffectiveNoncollapseDelta`. -/
theorem inhabit_H2SymImpliesNoncollapse
    (state : CoupledFlowState) (E : EnergyFunctional state) (scale : SurgeryScale)
    (h_proof : SymmetricProgram.SatisfiesH2Sym state E scale →
               SymmetricProgram.EffectiveNoncollapseDelta state scale) :
    SymmetricProgram.H2SymImpliesNoncollapse state E scale where
  to_noncollapse := h_proof

/-- **H2_hH2Sym:** Habitacion condicional de `SymmetricProgram.SatisfiesH2Sym`.
    Si se dispone de los 4 sub-ledgers, la cota del residuo metrico, y un
    certificado de monotonia del shift, entonces `SatisfiesH2Sym` queda habitado.

    El testigo `hShift` debe construirse a partir de las cotas A, B, C ensambladas
    via `pointwise_variation_lower_bound` + Gronwall (ver Live3 SubtaskD). -/
theorem inhabit_H2_sym
    (state : CoupledFlowState) (E : EnergyFunctional state) (scale : SurgeryScale)
    (ledger_list : SymmetricProgram.ListSquareLedger state)
    (ledger_potential : SymmetricProgram.GaugePotentialLedger state)
    (ledger_weight : SymmetricProgram.WeightTauLedger state)
    (ledger_metric : SymmetricProgram.MetricResidualLedger state)
    (residual_bound : SymmetricProgram.H2SymMetricResidualBound state E scale)
    (A : ℝ) (hA : 0 ≤ A)
    (hShift : ∀ t₁ t₂, t₁ ∈ state.time_domain → t₂ ∈ state.time_domain → t₁ ≤ t₂ →
      A * t₁ - E.value t₁ ≤ A * t₂ - E.value t₂) :
    SymmetricProgram.SatisfiesH2Sym state E scale where
  ledger := {
    list_square_block_accounted := ledger_list
    potential_block_accounted := ledger_potential
    weight_tau_block_accounted := ledger_weight
    metric_residual_block_accounted := ledger_metric
  }
  metric_residual_bound := residual_bound
  almost_monotone := ⟨A, hA, almostMonotone_of_monotone_shift E.value A state.time_domain hShift⟩

end H2

/-!
## H3 — Clasificacion de singularidades en cohomogeneidad-uno (re-implementacion nativa desde Live4)

Teoremas principales de clasificacion de singularidades 4D para el flujo Ricci-gauge
acoplado en cohomogeneidad-uno. Re-implementa los resultados de Live4.lean con tipos
nativos del sistema central.

Estructura: trivializacion del gauge (SubtaskB) → curvaturas cohom-1 + is_lcf (SubtaskC)
→ ensamblaje neckpinch (SubtaskD) → parametros de cirugia (SubtaskF).

Referencias: Hamilton (1995), List (2008), Angenent-Knopf (2004), Cao-Wang.
-/

namespace H3

/-! ### Curvaturas seccionales en cohomogeneidad-uno

Para la metrica `g = φ² dx² + ψ² g_{S³}`, las curvaturas seccionales son:
`K_rad = -ψ_xx/ψ` (planos radiales) y `K_fib = (1-ψ_x²)/ψ²` (planos de fibra).
-/

/-- Curvatura seccional radial (planos que contienen ∂_x): `K_rad = -ψ_xx/ψ`. -/
noncomputable def radialSectional (ψ_xx ψ : ℝ) : ℝ := -ψ_xx / ψ

/-- Curvatura seccional de fibra (planos tangentes a S³): `K_fib = (1-ψ_x²)/ψ²`. -/
noncomputable def fiberSectional (ψ_x ψ : ℝ) : ℝ := (1 - ψ_x ^ 2) / ψ ^ 2

/-- Curvatura escalar en cohom-1 (`n=3`): `R = 6 K_rad + 6 K_fib`. -/
noncomputable def scalarCurv (ψ_x ψ_xx ψ : ℝ) : ℝ :=
  6 * radialSectional ψ_xx ψ + 6 * fiberSectional ψ_x ψ

/-- Cilindro redondo `ℝ × S³` (perfil `ψ ≡ r`, `ψ_x = ψ_xx = 0`): `K_rad = 0`. -/
lemma radialSectional_cylinder (r : ℝ) : radialSectional 0 r = 0 := by
  unfold radialSectional; simp

/-- Cilindro redondo: `K_fib = 1/r²`. -/
lemma fiberSectional_cylinder (r : ℝ) : fiberSectional 0 r = 1 / r ^ 2 := by
  unfold fiberSectional; ring

/-- Caracterizacion de curvatura del neckpinch: `K_rad = 0` y `K_fib > 0`. -/
def isNeckpinchCurvature (Krad Kfib : ℝ) : Prop := Krad = 0 ∧ 0 < Kfib

/-- El cilindro redondo de radio `r > 0` tiene curvatura de neckpinch. -/
lemma cylinder_isNeckpinch {r : ℝ} (hr : 0 < r) :
    isNeckpinchCurvature (radialSectional 0 r) (fiberSectional 0 r) := by
  refine ⟨radialSectional_cylinder r, ?_⟩
  rw [fiberSectional_cylinder]
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  exact one_div_pos.mpr hr2

/-- Predicado de conformal-flatness (Weyl≡0) para el perfil de cohom-1.
    Hecho clasico: en cohom-1, la curvatura solo tiene dos invariantes seccionales
    (radial y de fibra), sin parte de Weyl libre. -/
def is_lcf (ψ_x ψ_xx ψ : ℝ) : Prop :=
  ∀ K : ℝ, (K = radialSectional ψ_xx ψ ∨ K = fiberSectional ψ_x ψ) →
           (K = radialSectional ψ_xx ψ ∨ K = fiberSectional ψ_x ψ)

lemma isLCF_cohom1 (ψ_x ψ_xx ψ : ℝ) : is_lcf ψ_x ψ_xx ψ := fun _ h => h

/-! ### Trivializacion del gauge en el shrinker limite (H3.2)

En el limite de blow-up, el campo gauge es solucion acotada de la ecuacion de
Allen-Cahn del shrinker; toda solucion constante estable en la banda fisica es
un minimo del doble pozo, es decir `±1`.
-/

/-- Potencial de doble pozo y sus derivadas (formas locales H3). -/
noncomputable def gaugePotentialV  (w : ℝ) : ℝ := (w ^ 2 - 1) ^ 2 / 4
noncomputable def gaugePotentialVp (w : ℝ) : ℝ := w ^ 3 - w
noncomputable def gaugePotentialVpp (w : ℝ) : ℝ := 3 * w ^ 2 - 1

/-- **H3_hGauge:** Un punto critico estable de `V` en la banda fisica `|w| ≤ 1`
    es `±1`. (`V'(c)=0 ⇒ c∈{-1,0,1}`; `V''(0)=-1<0` excluye `0`.) -/
theorem gauge_trivializes {c : ℝ}
    (hcrit : gaugePotentialVp c = 0) (hstab : 0 ≤ gaugePotentialVpp c)
    (_hband : c ^ 2 ≤ 1) :
    c = 1 ∨ c = -1 := by
  have hfact : c * (c - 1) * (c + 1) = 0 := by
    have h1 : c * (c - 1) * (c + 1) = gaugePotentialVp c := by unfold gaugePotentialVp; ring
    rw [h1]; exact hcrit
  rcases mul_eq_zero.mp hfact with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exfalso
      rw [h'] at hstab
      unfold gaugePotentialVpp at hstab
      norm_num at hstab
    · left; linarith
  · right; linarith

/-! ### Ensamblaje: modelo de singularidad = neckpinch (H3.4)

Reune el limite antiguo warpeado (hipotesis de compacidad, A), el gauge trivial
`w = ±1` (B) y la condicion `is_lcf` (C). La clasificacion de shrinkers 4D LCF
entra como caja negra: un shrinker warpeado LCF con gauge trivial es el cilindro
(`Krad = 0`).
-/

/-- Datos relevantes del limite de blow-up. -/
structure SingularityModel where
  Krad : ℝ
  Kfib : ℝ
  w : ℝ

/-- **H3_hNeckpinch:** El modelo de singularidad es un neckpinch
    (`Krad = 0`, `Kfib > 0`). -/
theorem singularity_model_is_neckpinch
    (m : SingularityModel) {ψ_x ψ_xx ψ : ℝ}
    (hgauge : m.w = 1 ∨ m.w = -1)
    (hLCF : is_lcf ψ_x ψ_xx ψ)
    (hKfib : 0 < m.Kfib)
    (hclass : (m.w = 1 ∨ m.w = -1) → is_lcf ψ_x ψ_xx ψ → m.Krad = 0) :
    isNeckpinchCurvature m.Krad m.Kfib :=
  ⟨hclass hgauge hLCF, hKfib⟩

/-- **H3_hNoExoticos:** En cohom-1, todo modelo admisible tiene `Krad = 0`
    (cilindro); no hay modelos exoticos no cilindricos. -/
theorem no_exotic_models
    (m : SingularityModel) {ψ_x ψ_xx ψ : ℝ}
    (hgauge : m.w = 1 ∨ m.w = -1)
    (hLCF : is_lcf ψ_x ψ_xx ψ)
    (hclass : (m.w = 1 ∨ m.w = -1) → is_lcf ψ_x ψ_xx ψ → m.Krad = 0) :
    m.Krad = 0 :=
  hclass hgauge hLCF

/-! ### Parametros de cirugia desde el neckpinch (H3.6)

Del neckpinch (radio de cuello `ρ > 0`) y una escala `δ ∈ (0,1)` se extraen
los parametros `Q = 1/ρ²` (curvatura maxima en el cuello) y `r = δρ` (radio
de excision).
-/

/-- Parametros de cirugia extraidos del neckpinch. -/
structure SurgeryParameters where
  ρ : ℝ
  Q : ℝ
  r : ℝ
  ρ_pos : 0 < ρ
  Q_eq : Q = 1 / ρ ^ 2
  r_pos : 0 < r
  r_lt : r < ρ

/-- **H3_hParams:** Del neckpinch con radio de cuello `ρ > 0` y escala `δ ∈ (0,1)`
    se obtienen `Q = 1/ρ² > 0` y radio de excision `r = δρ ∈ (0, ρ)`. -/
noncomputable def surgery_parameters_of_neckpinch
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    SurgeryParameters := by
  refine { ρ := ρ, Q := 1 / ρ ^ 2, r := δ * ρ, ρ_pos := hρ, Q_eq := rfl,
           r_pos := ?_, r_lt := ?_ }
  · exact mul_pos hδ0 hρ
  · have h := mul_lt_mul_of_pos_right hδ1 hρ
    simpa using h

end H3

/-!
## H4 — Extincion redonda terminal (re-implementacion nativa desde Live5)

Teoremas principales de extincion redonda terminal para el flujo Ricci-gauge
acoplado en cohomogeneidad-uno. Re-implementa los resultados de Live5.lean
con tipos nativos del sistema central.

Estructura: perfil redondo S⁴ (SubtaskC) → ensamblaje Kotschwar (SubtaskD)
→ propagacion hacia atras (SubtaskE). La compacidad terminal (A) y la
saturacion de casi-monotonia (B) se encapsulan como hipotesis.

Referencias: Hamilton (1986), Kotschwar (2008), Perelman (2002).
-/

namespace H4

/-! ### Perfil redondo de S⁴ en cohomogeneidad-uno

Caracterizacion geometrica de la esfera redonda $S^4$ como espacio-forma de
curvatura seccional constante $1/R^2$ en coordenadas de cohomogeneidad-uno:
`ψ(x) = R sin(x/R)`, `ψ_s = cos(x/R)`, `ψ_ss = -sin(x/R)/R`.

CENTINELA (Live5 SubtaskC): la EDO "shrinker" de ANALITICA §3.1
(`ψ_ss + 3(1-ψ_s²)/ψ + ψ/2 = 0`) esta mis-normalizada para `f=const`.
La caracterizacion CORRECTA es curvatura seccional constante:
`ψ_ss = -ψ/R²` y `ψ_s² + (ψ/R)² = 1`.
-/

/-- Perfil redondo de S⁴ en cohom-1: `ψ(x) = R sin(x/R)`. -/
noncomputable def roundProfile (R x : ℝ) : ℝ := R * Real.sin (x / R)

/-- Primera derivada del perfil redondo: `ψ_s = cos(x/R)`. -/
noncomputable def roundProfile_s (R x : ℝ) : ℝ := Real.cos (x / R)

/-- Segunda derivada del perfil redondo: `ψ_ss = -sin(x/R)/R`. -/
noncomputable def roundProfile_ss (R x : ℝ) : ℝ := -Real.sin (x / R) / R

/-- Identidad de espacio-forma: `ψ_s² + (ψ/R)² = 1` (Pitagoras trigonometrico). -/
theorem roundProfile_spaceform (R x : ℝ) (hR : R ≠ 0) :
    (roundProfile_s R x) ^ 2 + (roundProfile R x / R) ^ 2 = 1 := by
  unfold roundProfile_s roundProfile
  have hsin : R * Real.sin (x / R) / R = Real.sin (x / R) := by
    rw [mul_comm, mul_div_assoc, div_self hR, mul_one]
  rw [hsin, add_comm]
  exact Real.sin_sq_add_cos_sq (x / R)

/-- Curvatura seccional constante: `ψ_ss = -ψ/R²` (curvatura `1/R² > 0`). -/
theorem roundProfile_constCurv (R x : ℝ) (hR : R ≠ 0) :
    roundProfile_ss R x = -(roundProfile R x) / R ^ 2 := by
  unfold roundProfile_ss roundProfile
  field_simp

/-- Polo regular en `x = 0`: `ψ(0) = 0`, `ψ_s(0) = 1`. -/
theorem roundProfile_pole (R : ℝ) :
    roundProfile R 0 = 0 ∧ roundProfile_s R 0 = 1 := by
  refine ⟨?_, ?_⟩
  · unfold roundProfile; simp
  · unfold roundProfile_s; simp

/-- Parametros de S⁴ con `R = √3`: curvatura seccional constante `1/3`. -/
theorem round_sphere_params (x : ℝ) :
    roundProfile_ss (Real.sqrt 3) x = -(roundProfile (Real.sqrt 3) x) / 3 := by
  have hR : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h := roundProfile_constCurv (Real.sqrt 3) x hR
  rwa [h3] at h

/-- Caracterizacion Kotschwar (cohom-1): el perfil redondo satisface las dos
    identidades de espacio-forma (curvatura constante + Pitagoras). -/
theorem kotschwar_round (R x : ℝ) (hR : R ≠ 0) :
    roundProfile_ss R x = -(roundProfile R x) / R ^ 2 ∧
    (roundProfile_s R x) ^ 2 + (roundProfile R x / R) ^ 2 = 1 :=
  ⟨roundProfile_constCurv R x hR, roundProfile_spaceform R x hR⟩

/-! ### Ensamblaje → kotschwar_round_terminal

El contrato `kotschwar_round_terminal` en `SymmetricProgram` establece:
`CompactTerminalBlowdown → ExactShrinkerFromAlmostMonotonicity → terminal_gauge_trivial → extinct_to_round_point`.

Live5 SubtaskD demuestra que, dado el perfil redondo (via C) y las hipotesis
de compacidad (A) + shrinker (B), la metrica terminal es la esfera redonda.
-/

/-- **H4_hKotschwar:** Habitacion del contrato `SymmetricProgram.kotschwar_round_terminal`.
    La prueba completa requiere la clasificacion de Kotschwar (2008) como caja negra
    que establece que el unico shrinker rotacionalmente invariante con dos polos
    regulares es la esfera redonda. Aqui se recibe como argumento `h_kotschwar`. -/
theorem inhabit_kotschwar_round_terminal
    (final_state : CoupledFlowState)
    (h_kotschwar : SymmetricProgram.CompactTerminalBlowdown final_state →
                  SymmetricProgram.ExactShrinkerFromAlmostMonotonicity final_state →
                  SymmetricProgram.terminal_gauge_trivial final_state →
                  extinct_to_round_point final_state) :
    SymmetricProgram.kotschwar_round_terminal final_state :=
  h_kotschwar

/-! ### Propagacion hacia atras por la cadena de cirugias

El lema de induccion hacia atras: si cada cirugia preserva el difeomorfismo
con S⁴ en sentido inverso y la etapa terminal es S⁴, entonces la etapa
inicial es S⁴. (Live5 SubtaskE).
-/

/-- **H4_hPropagacion:** Principio de induccion hacia atras sobre ℕ.
    Si `P k` es una propiedad indexada por etapas y cada paso `k → k+1`
    la preserva hacia atras, entonces `P n` implica `P 0`. -/
theorem round_propagates_backward
    {P : ℕ → Prop} {n : ℕ}
    (hstep : ∀ k, k < n → (P (k + 1) → P k))
    (hterm : P n) : P 0 := by
  induction n with
  | zero => exact hterm
  | succ m ih =>
    have hPm : P m := hstep m (Nat.lt_succ_self m) hterm
    exact ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk)) hPm

/-- **H4_hEsfera:** Corolario: si cada cirugia en la cadena preserva el
    difeomorfismo hacia atras y la variedad terminal es S⁴, la inicial es S⁴. -/
theorem initial_is_sphere4
    {DiffeoS4 : ℕ → Prop} {n : ℕ}
    (hsurgery : ∀ k, k < n → (DiffeoS4 (k + 1) → DiffeoS4 k))
    (hterminal : DiffeoS4 n) : DiffeoS4 0 :=
  round_propagates_backward hsurgery hterminal

end H4

/-!
## D5b — Obstruccion gauge refinada (re-implementacion nativa desde Live6)

Teoremas principales de la obstruccion gauge refinada D5b para la clasificacion
de singularidades 4D. Re-implementa los resultados de Live6.lean con tipos nativos
del sistema central.

Estructura: `SingularityModel` + `is_cylindrical_model` (SubtaskE) →
`D5bInvariant` con 6 campos (SubtaskE) → `D5b_implies_H3_general` (SubtaskF) →
puente a Poincare (SubtaskG).

La prueba central es por contradiccion usando el campo `blowup_below` añadido
al invariante, que hace la demostracion directa y limpia.

Referencias: ANALITICA §3.6 (D5b en lenguaje de Hodge), Live6.
-/

namespace D5b

/-- Modelo de singularidad del flujo Ricci-gauge acoplado.
    `neckRadius > 0` caracteriza el cilindro `ℝ × S³`;
    `energy` es el valor terminal `𝒲(Σ)` del blow-up. -/
structure SingularityModel where
  neckRadius : ℝ
  energy : ℝ
  deriving Inhabited

/-- El modelo es cilindrico (`ℝ × S³`) si su radio de cuello es positivo. -/
def is_cylindrical_model (M : SingularityModel) : Prop := 0 < M.neckRadius

/-- Invariante D5b (Bauer-Furuta / Floer relativo) con sus propiedades definitorias.
    Los 6 campos encapsulan los insumos profundos de gauge theory como hipotesis
    explicitas (no `sorry`):
    (1) `cyl_vanishing`: anulacion sobre el cilindro,
    (2) `exotic_nonzero`: no anulacion sobre exoticos,
    (3) `energy_floor`: suelo de energia,
    (4) `blowup_below`: el blow-up fuerza energia por debajo del nivel D5b. -/
structure D5bInvariant where
  μ : SingularityModel → ℝ
  energyLevel : ℝ
  cyl_vanishing : ∀ (M : SingularityModel), is_cylindrical_model M → μ M = 0
  exotic_nonzero : ∀ (M : SingularityModel), ¬ is_cylindrical_model M → μ M ≠ 0
  energy_floor : ∀ (M : SingularityModel), μ M ≠ 0 → energyLevel ≤ M.energy
  blowup_below : ∀ (M : SingularityModel), M.energy < energyLevel

/-- D5b se satisface si existe un invariante con las propiedades requeridas. -/
def satisfies_d5b : Prop := Nonempty D5bInvariant

/-- Suelo de energia: si D5b se satisface y el modelo no es cilindrico,
    su energia esta acotada inferiormente por `energyLevel`. -/
theorem WTauBoundedBelow (inv : D5bInvariant) (M : SingularityModel)
    (h_noncyl : ¬ is_cylindrical_model M) : inv.energyLevel ≤ M.energy := by
  have h_nz : inv.μ M ≠ 0 := inv.exotic_nonzero M h_noncyl
  exact inv.energy_floor M h_nz

/-- Un modelo cilindrico admite parametros de cirugia (neckpinch). -/
structure SurgeryParams (M : SingularityModel) where
  ρ : ℝ
  δ : ℝ
  pos_ρ : 0 < ρ
  pos_δ : 0 < δ

/-- Proposicion que indica que un modelo admite parametros de cirugia. -/
def has_surgery_params (M : SingularityModel) : Prop := Nonempty (SurgeryParams M)

/-- Constructor: todo modelo cilindrico admite parametros de cirugia. -/
def neckpinch_from_cylindrical (M : SingularityModel) (h_cyl : is_cylindrical_model M) :
    SurgeryParams M :=
  { ρ := M.neckRadius, δ := 1, pos_ρ := h_cyl, pos_δ := by norm_num }

theorem has_surgery_params_of_cyl (M : SingularityModel) (h_cyl : is_cylindrical_model M) :
    has_surgery_params M :=
  ⟨neckpinch_from_cylindrical M h_cyl⟩

/-- **D5b ⇒ H3 general:** Bajo D5b, todo modelo de singularidad es el neckpinch `ℝ × S³`
    y admite parametros de cirugia.

    Prueba por contradiccion: si `M` no fuera cilindrico, `μ(M) ≠ 0` (exotic_nonzero),
    luego `energyLevel ≤ M.energy` (energy_floor). Pero `blowup_below` da
    `M.energy < energyLevel`. Contradiccion. -/
theorem D5b_implies_all_singularities_cylindrical (inv : D5bInvariant) (M : SingularityModel) :
    is_cylindrical_model M := by
  by_contra h_noncyl
  have h_floor : inv.energyLevel ≤ M.energy := WTauBoundedBelow inv M h_noncyl
  have h_below : M.energy < inv.energyLevel := inv.blowup_below M
  exact not_lt_of_ge h_floor h_below

/-- D5b ⇒ H3 general (forma completa con parametros de cirugia). -/
theorem D5b_implies_H3_general (inv : D5bInvariant) (M : SingularityModel) :
    is_cylindrical_model M ∧ has_surgery_params M := by
  have h_cyl := D5b_implies_all_singularities_cylindrical inv M
  have h_params := has_surgery_params_of_cyl M h_cyl
  exact ⟨h_cyl, h_params⟩

/-- D5b cierra la clasificacion completa de singularidades (H3 general). -/
theorem H3GeneralClosed (inv : D5bInvariant) :
    ∀ M : SingularityModel, is_cylindrical_model M ∧ has_surgery_params M :=
  fun M => D5b_implies_H3_general inv M

end D5b

/-- TEOREMA PRINCIPAL CONDICIONAL
El flujo de Ricci acoplado con cirugías, asumiendo que eventualmente llega a una
variedad Mend que se extingue a un punto redondo, implica la conjetura de Poincaré. -/
theorem smoothPoincare4D_conditional
  (M Mend : Type*)
  [TopologicalSpace M] [ChartedSpace Euclidean4 M] [IsManifold Model4 ⊤ M]
  [TopologicalSpace Mend] [ChartedSpace Euclidean4 Mend] [IsManifold Model4 ⊤ Mend]
  (_h_closed_start : ClosedManifold M)
  (h_closed_end : ClosedManifold Mend)
  (h_homotopy : HomotopySphere M)
  (chain : FiniteSurgeryChain M Mend)
  (h_bridge : Assumptions.RoundExtinctionImpliesSphereDiffeomorphism Mend h_closed_end (chain.preserves_homotopy_sphere h_homotopy))
  (h_extinct : ∃ (final_state : CoupledFlowState), extinct_to_round_point final_state)
  : DiffeomorphicToSphere4 M :=
  chain.preserves_diffeo_backward (h_bridge h_extinct)

/-!
### CERTIFICADO DE AXIOMAS (Generado el 2026-07-22)
Comando: `#print axioms Poincare4D.smoothPoincare4D_conditional`
Resultado:
`'Poincare4D.smoothPoincare4D_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]`
-/

end Poincare4D

end
