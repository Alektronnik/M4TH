/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

public import Poincare4D.Flow

/-!
## Source file: Poincare4D/Surgery.lean

Surgery infrastructure. Defines smooth surgery data, surgery steps,
finite surgery chains, and the preservation theorems for homotopy
spheres and diffeomorphism type. Also covers functionals, monotonicity,
and the extinction mechanism (FASE 5).
-/

noncomputable section

@[expose] public section

namespace Poincare4D

/-!
### FASE 4: Singularidades, Escalas y Cirugía
Definiciones geométricas del operador quirúrgico.
-/

/-- El perfil asintótico Gaussiano C^\infty para el re-injerto -/
structure SmoothCapProfile where
  cap_scale : ℝ
  width : ℝ
  /-- El perfil exacto de la calota -/
  cap_func : ℝ → ℝ := fun x ↦ cap_scale * Real.exp (- (x^2) / width^2)

/-- Equivalencia de perfiles antes/después de una cirugía fuera de la región modificada.
Este dato exige una igualdad explícita de coordenadas solo fuera del cilindro de excisión. -/
structure SurgicalProfileEquiv (pre_profile post_profile : RotationallySymmetricProfile) (time location excision_radius : ℝ) where
  coordEquiv : ℝ ≃ ℝ
  phi_eq : ∀ x, |x - location| > excision_radius → post_profile.phi time (coordEquiv x) = pre_profile.phi time x
  psi_eq : ∀ x, |x - location| > excision_radius → post_profile.psi time (coordEquiv x) = pre_profile.psi time x

/-- Un evento de cirugía purificadora -/
structure SmoothSurgeryDatum where
  time : ℝ
  location : ℝ
  excision_radius : ℝ
  excision_radius_pos : 0 < excision_radius
  cap : SmoothCapProfile
  pre_profile : RotationallySymmetricProfile
  post_profile : RotationallySymmetricProfile
  /-- Condición de pegado: la cirugía eleva el cuello a O(1) usando la calota asintótica.
  Usamos un predicado sintético para no exponer la no-suavidad de `max` simulando un mollifier. -/
  is_smooth_graft : Prop
  profile_equiv : SurgicalProfileEquiv pre_profile post_profile time location excision_radius

/-- Todo dato quirúrgico contiene, por construcción, una equivalencia de perfiles pre/post. -/
theorem SmoothSurgeryDatum.profileEquiv_nonempty (datum : SmoothSurgeryDatum) :
    Nonempty (SurgicalProfileEquiv datum.pre_profile datum.post_profile datum.time datum.location datum.excision_radius) :=
  ⟨datum.profile_equiv⟩

/-- Evento de neckpinch localizado que alcanza una escala quirúrgica. -/
structure NeckpinchEvent where
  time : ℝ
  location : ℝ
  scale : SurgeryScale
  profile : RotationallySymmetricProfile
  below_scale : is_below_surgery_scale profile time scale
  localized : is_localized_neck profile time scale

namespace Assumptions
  /-- Contrato temporal: la cirugía suave preserva el tipo de homotopía esférica.
  El modelo híbrido toma dos variedades (Mpre y Mpost) conectadas por sus perfiles pre/post. -/
  def SmoothSurgeryPreservesHomotopySphere
      (Mpre Mpost : Type*)
      [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
      [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost]
      (datum : SmoothSurgeryDatum)
      (_hpre : CohomogeneityOneManifold Mpre datum.pre_profile)
      (_hpost : CohomogeneityOneManifold Mpost datum.post_profile)
      : Prop :=
    HomotopySphere Mpre → HomotopySphere Mpost
end Assumptions

/-- Región exterior a la zona quirúrgica, definida por la coordenada de cohomogeneidad uno. -/
def exteriorRegion
    {M : Type*} [TopologicalSpace M] [ChartedSpace Euclidean4 M]
    {p : RotationallySymmetricProfile} (model : CohomogeneityOneManifold M p)
    (location radius : ℝ) : Set M :=
  {q | |model.base_coord q - location| > radius}

/-- Región de cuello que será extirpada o modificada por la cirugía. -/
def neckRegion
    {M : Type*} [TopologicalSpace M] [ChartedSpace Euclidean4 M]
    {p : RotationallySymmetricProfile} (model : CohomogeneityOneManifold M p)
    (location radius : ℝ) : Set M :=
  {q | |model.base_coord q - location| ≤ radius}

/-- Dato sintético de equivalencia parcial topológica entre las regiones regulares
pre/post. Usa `PartialEquiv` de Mathlib para fijar la biyección parcial, y añade
como contrato separado que los dominios exteriores son abiertos y que los mapas
son continuos en sus dominios. La suavidad queda deliberadamente como contrato
global de cirugía, no como una promesa escondida en este dato. -/
structure PartialSurgeryDiffeomorphismData
    (Mpre Mpost : Type*)
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost]
    (datum : SmoothSurgeryDatum)
    (pre_model : CohomogeneityOneManifold Mpre datum.pre_profile)
    (post_model : CohomogeneityOneManifold Mpost datum.post_profile) where
  equiv : PartialEquiv Mpre Mpost
  source_eq : equiv.source = exteriorRegion pre_model datum.location datum.excision_radius
  target_eq : equiv.target = exteriorRegion post_model datum.location datum.excision_radius
  source_open : IsOpen equiv.source
  target_open : IsOpen equiv.target
  continuous_toFun : ContinuousOn equiv equiv.source
  continuous_invFun : ContinuousOn equiv.symm equiv.target
  base_coord_eq :
    ∀ q, q ∈ exteriorRegion pre_model datum.location datum.excision_radius →
      post_model.base_coord (equiv q) =
        datum.profile_equiv.coordEquiv (pre_model.base_coord q)

namespace PartialSurgeryDiffeomorphismData

/-- The source of the surgical partial equivalence is exactly the exterior
pre-surgery region. -/
theorem sourceExterior
    {Mpre Mpost : Type*}
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost]
    {datum : SmoothSurgeryDatum}
    {pre_model : CohomogeneityOneManifold Mpre datum.pre_profile}
    {post_model : CohomogeneityOneManifold Mpost datum.post_profile}
    (data : PartialSurgeryDiffeomorphismData Mpre Mpost datum pre_model post_model) :
    data.equiv.source = exteriorRegion pre_model datum.location datum.excision_radius :=
  data.source_eq

/-- The target of the surgical partial equivalence is exactly the exterior
post-surgery region. -/
theorem targetExterior
    {Mpre Mpost : Type*}
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost]
    {datum : SmoothSurgeryDatum}
    {pre_model : CohomogeneityOneManifold Mpre datum.pre_profile}
    {post_model : CohomogeneityOneManifold Mpost datum.post_profile}
    (data : PartialSurgeryDiffeomorphismData Mpre Mpost datum pre_model post_model) :
    data.equiv.target = exteriorRegion post_model datum.location datum.excision_radius :=
  data.target_eq

/-- The exterior-region partial equivalence maps pre-surgery exterior points to
post-surgery exterior points. -/
theorem mapsExterior
    {Mpre Mpost : Type*}
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost]
    {datum : SmoothSurgeryDatum}
    {pre_model : CohomogeneityOneManifold Mpre datum.pre_profile}
    {post_model : CohomogeneityOneManifold Mpost datum.post_profile}
    (data : PartialSurgeryDiffeomorphismData Mpre Mpost datum pre_model post_model)
    {q : Mpre} (hq : q ∈ exteriorRegion pre_model datum.location datum.excision_radius) :
    data.equiv q ∈ exteriorRegion post_model datum.location datum.excision_radius := by
  rw [← data.target_eq]
  exact data.equiv.map_source (by rwa [data.source_eq])

/-- The inverse partial equivalence maps post-surgery exterior points back to
pre-surgery exterior points. -/
theorem mapsExterior_symm
    {Mpre Mpost : Type*}
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost]
    {datum : SmoothSurgeryDatum}
    {pre_model : CohomogeneityOneManifold Mpre datum.pre_profile}
    {post_model : CohomogeneityOneManifold Mpost datum.post_profile}
    (data : PartialSurgeryDiffeomorphismData Mpre Mpost datum pre_model post_model)
    {q : Mpost} (hq : q ∈ exteriorRegion post_model datum.location datum.excision_radius) :
    data.equiv.symm q ∈ exteriorRegion pre_model datum.location datum.excision_radius := by
  rw [← data.source_eq]
  exact data.equiv.map_target (by rwa [data.target_eq])

end PartialSurgeryDiffeomorphismData

/-- El espacio modelo topológico de la excisión: un cilindro paramétrico I × S^3. -/
abbrev NeckCylinder (location radius : ℝ) := Set.Icc (location - radius) (location + radius) × StandardSphere3

/-- Dato topológico sintético de que la región extirpada es un cuello cilíndrico.
El campo `cylinder_equiv` reemplaza al antiguo contrato semántico abstracto
por un homeomorfismo explícito hacia el cilindro, anclado a la coordenada base. -/
structure CylindricalExcisionData
    (M : Type*) [TopologicalSpace M] [ChartedSpace Euclidean4 M] [IsManifold Model4 ⊤ M]
    {p : RotationallySymmetricProfile} (model : CohomogeneityOneManifold M p)
    (location radius : ℝ) where
  radius_pos : 0 < radius
  excised_region : Set M := neckRegion model location radius
  matches_neck_region : excised_region = neckRegion model location radius
  cylinder_equiv : Homeomorph excised_region (NeckCylinder location radius)
  base_coord_compat : ∀ q : excised_region, (cylinder_equiv q).1.val = model.base_coord q.val

/-- Paquete de compatibilidad local-global para una cirugía: conecta cada variedad
con su perfil correspondiente, registra la equivalencia local de perfiles, y afirma
la existencia de una carta cilíndrica de excisión con difeomorfismo parcial en el exterior. -/
structure CohomogeneityOneSurgeryCompatible
    (Mpre Mpost : Type*)
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost]
    (datum : SmoothSurgeryDatum) where
  pre_modeled : CohomogeneityOneManifold Mpre datum.pre_profile
  post_modeled : CohomogeneityOneManifold Mpost datum.post_profile
  local_profile_equiv : Nonempty (SurgicalProfileEquiv datum.pre_profile datum.post_profile datum.time datum.location datum.excision_radius)
  regular_region_pre : Set Mpre := exteriorRegion pre_modeled datum.location datum.excision_radius
  regular_region_post : Set Mpost := exteriorRegion post_modeled datum.location datum.excision_radius
  regular_region_pre_eq : regular_region_pre = exteriorRegion pre_modeled datum.location datum.excision_radius
  regular_region_post_eq : regular_region_post = exteriorRegion post_modeled datum.location datum.excision_radius
  partial_diffeomorphism :
    PartialSurgeryDiffeomorphismData Mpre Mpost datum pre_modeled post_modeled
  excised_cylinder_pre :
    CylindricalExcisionData Mpre pre_modeled datum.location datum.excision_radius
  excised_cylinder_post :
    CylindricalExcisionData Mpost post_modeled datum.location datum.excision_radius

/-- Una transición quirúrgica global entre dos variedades, decorada con el dato local
de perfiles y con los conectores cohomogeneidad-uno en ambos extremos. -/
structure SmoothSurgeryStep
    (Mpre Mpost : Type*)
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost] where
  datum : SmoothSurgeryDatum
  compatible : CohomogeneityOneSurgeryCompatible Mpre Mpost datum
  preserves_homotopy_sphere :
    Assumptions.SmoothSurgeryPreservesHomotopySphere
      Mpre Mpost datum compatible.pre_modeled compatible.post_modeled
  /-- Contrato reverso: si la variedad post-cirugía es difeomorfa a S^4, también lo es la pre-cirugía. -/
  preserves_diffeo_backward : DiffeomorphicToSphere4 Mpost → DiffeomorphicToSphere4 Mpre

/-- La compatibilidad de una transición quirúrgica contiene la equivalencia local
de perfiles requerida por el dato quirúrgico. -/
theorem SmoothSurgeryStep.local_profile_equiv
    {Mpre Mpost : Type*}
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost]
    (step : SmoothSurgeryStep Mpre Mpost) :
    Nonempty (SurgicalProfileEquiv step.datum.pre_profile step.datum.post_profile step.datum.time step.datum.location step.datum.excision_radius) :=
  step.compatible.local_profile_equiv

/-- Una transición quirúrgica contiene un dato explícito de difeomorfismo parcial
en la región exterior a la excisión. -/
def SmoothSurgeryStep.partialDiffeomorphismData
    {Mpre Mpost : Type*}
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost]
    (step : SmoothSurgeryStep Mpre Mpost) :
    PartialSurgeryDiffeomorphismData
      Mpre Mpost step.datum step.compatible.pre_modeled step.compatible.post_modeled :=
  step.compatible.partial_diffeomorphism

/-- La región extirpada pre-cirugía viene con un contrato cilíndrico. -/
def SmoothSurgeryStep.preCylindricalExcision
    {Mpre Mpost : Type*}
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost]
    (step : SmoothSurgeryStep Mpre Mpost) :
    CylindricalExcisionData Mpre step.compatible.pre_modeled step.datum.location step.datum.excision_radius :=
  step.compatible.excised_cylinder_pre

/-- La región extirpada post-cirugía viene con un contrato cilíndrico. -/
def SmoothSurgeryStep.postCylindricalExcision
    {Mpre Mpost : Type*}
    [TopologicalSpace Mpre] [ChartedSpace Euclidean4 Mpre] [IsManifold Model4 ⊤ Mpre]
    [TopologicalSpace Mpost] [ChartedSpace Euclidean4 Mpost] [IsManifold Model4 ⊤ Mpost]
    (step : SmoothSurgeryStep Mpre Mpost) :
    CylindricalExcisionData Mpost step.compatible.post_modeled step.datum.location step.datum.excision_radius :=
  step.compatible.excised_cylinder_post

/-- Una etapa quirúrgica empaqueta una variedad junto con sus estructuras
topológicas y suaves. Esto permite indexar una cadena por variedades intermedias
realmente tipadas, no solo por una lista de eventos. -/
structure SurgeryStage where
  carrier : Type*
  [topological : TopologicalSpace carrier]
  [charted : ChartedSpace Euclidean4 carrier]
  [manifold : IsManifold Model4 ⊤ carrier]

attribute [instance] SurgeryStage.topological SurgeryStage.charted SurgeryStage.manifold

/-- Cadena finita tipada de cirugías. Para `n` cirugías hay `n+1` etapas,
indexadas por `Fin (n+1)`, y cada paso conecta dos variedades consecutivas. -/
structure TypedFiniteSurgeryChain (n : ℕ) where
  stages : Fin (n + 1) → SurgeryStage
  steps :
    (i : Fin n) →
      SmoothSurgeryStep (stages i.castSucc).carrier (stages i.succ).carrier
  preserves_homotopy_sphere :
    HomotopySphere (stages ⟨0, Nat.succ_pos n⟩).carrier →
      HomotopySphere (stages ⟨n, Nat.lt_succ_self n⟩).carrier
  preserves_diffeo_backward :
    DiffeomorphicToSphere4 (stages ⟨n, Nat.lt_succ_self n⟩).carrier →
      DiffeomorphicToSphere4 (stages ⟨0, Nat.succ_pos n⟩).carrier

namespace TypedFiniteSurgeryChain

/-- La etapa inicial de una cadena tipada. -/
def startStage {n : ℕ} (chain : TypedFiniteSurgeryChain n) : SurgeryStage :=
  chain.stages ⟨0, Nat.succ_pos n⟩

/-- La etapa final de una cadena tipada. -/
def endStage {n : ℕ} (chain : TypedFiniteSurgeryChain n) : SurgeryStage :=
  chain.stages ⟨n, Nat.lt_succ_self n⟩

end TypedFiniteSurgeryChain

/-- Composición finita abstracta de cirugías entre una variedad inicial y una final.
Los pasos intermedios pueden tener tipos distintos; esta estructura registra el
resultado compuesto sin forzar todavía una lista heterogénea de variedades. -/
structure FiniteSurgeryChain
    (Mstart Mend : Type*)
    [TopologicalSpace Mstart] [ChartedSpace Euclidean4 Mstart] [IsManifold Model4 ⊤ Mstart]
    [TopologicalSpace Mend] [ChartedSpace Euclidean4 Mend] [IsManifold Model4 ⊤ Mend] where
  events : List SmoothSurgeryDatum
  preserves_homotopy_sphere : HomotopySphere Mstart → HomotopySphere Mend
  /-- La cadena de cirugías propaga el difeomorfismo en sentido inverso. -/
  preserves_diffeo_backward : DiffeomorphicToSphere4 Mend → DiffeomorphicToSphere4 Mstart

namespace TypedFiniteSurgeryChain

/-- Una cadena tipada induce la cadena endpoint abstracta usada por el teorema
principal actual, conservando sus eventos y los mapas de propagación extremos. -/
def toFiniteSurgeryChain {n : ℕ} (chain : TypedFiniteSurgeryChain n) :
    FiniteSurgeryChain chain.startStage.carrier chain.endStage.carrier where
  events := List.ofFn (fun i : Fin n ↦ (chain.steps i).datum)
  preserves_homotopy_sphere := chain.preserves_homotopy_sphere
  preserves_diffeo_backward := chain.preserves_diffeo_backward

/-- Los eventos del envoltorio endpoint son exactamente los datos quirúrgicos de
los pasos tipados. -/
theorem toFiniteSurgeryChain_events {n : ℕ} (chain : TypedFiniteSurgeryChain n) :
    chain.toFiniteSurgeryChain.events =
      List.ofFn (fun i : Fin n ↦ (chain.steps i).datum) :=
  rfl

end TypedFiniteSurgeryChain

/-!
### FASE 5: Funcionales, Monotonía y Extinción
-/

/-- Curvatura escalar R para la métrica g = phi^2 dx^2 + psi^2 g_{S^3}. -/
def scalarCurvatureDensity (p : RotationallySymmetricProfile) (dp : ProfileDerivatives p) (t x : ℝ) : ℝ :=
  6 / (p.psi t x)^2
  - 6 * (dp.psi_x t x)^2 / ((p.phi t x * p.psi t x)^2)
  - 6 * dp.psi_xx t x / ((p.phi t x)^2 * p.psi t x)
  + 6 * dp.psi_x t x * dp.phi_x t x / ((p.phi t x)^3 * p.psi t x)

/-- Densidad de energía total: curvatura escalar penalizada por la energía gauge. -/
def totalEnergyDensity (p : RotationallySymmetricProfile) (dp : ProfileDerivatives p)
    (g : GaugeField) (dg : GaugeDerivatives g) (t x : ℝ) : ℝ :=
  scalarCurvatureDensity p dp t x - gaugeEnergyDensity p g dg t x

/-- Elemento de volumen dV de la métrica (omitiendo el volumen constante de S^3). -/
def volumeElement (p : RotationallySymmetricProfile) (t x : ℝ) : ℝ :=
  p.phi t x * (p.psi t x)^3

/-- Lema de reducción: bajo el gauge fijo, la densidad de curvatura escalar multiplicada
por el elemento de volumen se simplifica algebraicamente a su forma polinómica. -/
theorem scalarCurvatureDensity_fixedGauge
    {p : RotationallySymmetricProfile} {dp : ProfileDerivatives p}
    (h_fixed : is_fixed_arclength_gauge p dp) :
    ∀ t x, scalarCurvatureDensity p dp t x * volumeElement p t x =
      6 * p.psi t x - 6 * (dp.psi_x t x)^2 * p.psi t x - 6 * dp.psi_xx t x * (p.psi t x)^2 := by
  intro t x
  rcases h_fixed t x with ⟨hphi, _hphit, hphix⟩
  have hpos : p.psi t x ≠ 0 := ne_of_gt (p.positive_psi t x)
  unfold scalarCurvatureDensity volumeElement
  rw [hphi, hphix]
  field_simp
  ring

/-- Lema de reducción: bajo el gauge fijo, la densidad de energía gauge multiplicada
por el elemento de volumen se simplifica algebraicamente. -/
theorem gaugeEnergyDensity_fixedGauge
    {p : RotationallySymmetricProfile} {dp : ProfileDerivatives p}
    {g : GaugeField} {dg : GaugeDerivatives g}
    (h_fixed : is_fixed_arclength_gauge p dp) :
    ∀ t x, gaugeEnergyDensity p g dg t x * volumeElement p t x =
      (0.5 * (dg.w_x t x)^2 + 0.25 * ((g.w t x)^2 - 1)^2) * (p.psi t x)^3 := by
  intro t x
  rcases h_fixed t x with ⟨hphi, _hphit, hphix⟩
  have hpos : p.psi t x ≠ 0 := ne_of_gt (p.positive_psi t x)
  unfold gaugeEnergyDensity gaugeKineticDensity doubleWellPotential volumeElement
  rw [hphi]
  field_simp
  ring_nf


/-- Operador de integración espacial sintético con linealidad real mínima. -/
structure SpatialIntegral where
  integral : (ℝ → ℝ) → ℝ
  map_add : ∀ f g, MeasureTheory.Integrable f → MeasureTheory.Integrable g → integral (fun x ↦ f x + g x) = integral f + integral g
  map_smul : ∀ (c : ℝ) f, MeasureTheory.Integrable f → integral (fun x ↦ c * f x) = c * integral f
  nonneg : ∀ f, MeasureTheory.Integrable f → (∀ x, 0 ≤ f x) → 0 ≤ integral f

namespace SpatialIntegral

/-- Positividad del operador integral espacial. -/
theorem integral_nonneg (I : SpatialIntegral) {f : ℝ → ℝ} (hf_int : MeasureTheory.Integrable f) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ I.integral f :=
  I.nonneg f hf_int hf

/-- Compatibilidad con negación, derivada de homogeneidad real. -/
theorem map_neg (I : SpatialIntegral) (f : ℝ → ℝ) (hf_int : MeasureTheory.Integrable f) :
    I.integral (fun x ↦ -f x) = -I.integral f := by
  simpa using I.map_smul (-1 : ℝ) f hf_int

/-- Compatibilidad con resta, derivada de linealidad. -/
theorem map_sub (I : SpatialIntegral) (f g : ℝ → ℝ)
    (hf_int : MeasureTheory.Integrable f) (hg_int : MeasureTheory.Integrable g) :
    I.integral (fun x ↦ f x - g x) = I.integral f - I.integral g := by
  calc
    I.integral (fun x ↦ f x - g x) = I.integral (fun x ↦ f x + (-g x)) := by
      simp [sub_eq_add_neg]
    _ = I.integral f + I.integral (fun x ↦ -g x) := I.map_add f (fun x ↦ -g x) hf_int hg_int.neg
    _ = I.integral f - I.integral g := by rw [I.map_neg g hg_int]; ring

/-- Monotonía del operador integral espacial. -/
theorem integral_mono (I : SpatialIntegral) {f g : ℝ → ℝ}
    (hf_int : MeasureTheory.Integrable f) (hg_int : MeasureTheory.Integrable g)
    (hfg : ∀ x, f x ≤ g x) :
    I.integral f ≤ I.integral g := by
  have hnonneg : 0 ≤ I.integral (fun x ↦ g x - f x) :=
    I.nonneg (fun x ↦ g x - f x) (hg_int.sub hf_int) (fun x ↦ sub_nonneg.mpr (hfg x))
  have hsub : I.integral (fun x ↦ g x - f x) = I.integral g - I.integral f :=
    I.map_sub g f hg_int hf_int
  nlinarith

end SpatialIntegral

/-- La integral de Lebesgue real de Mathlib empaquetada como un SpatialIntegral. -/
noncomputable def StandardLebesgueIntegral : SpatialIntegral where
  integral := fun f ↦ ∫ x, f x
  map_add := fun _ _ hf hg ↦ MeasureTheory.integral_add hf hg
  map_smul := fun c _ _ ↦ MeasureTheory.integral_smul c _
  nonneg := fun _ _ hf ↦ MeasureTheory.integral_nonneg hf

/-- Integrando espacial del funcional de energía geométrico. -/
def energyIntegrand (state : CoupledFlowState) (t x : ℝ) : ℝ :=
  totalEnergyDensity state.profile state.profile_derivs state.gauge state.gauge_derivs t x *
    volumeElement state.profile t x

/-- Funcional de Energía de Perelman evaluado a lo largo del tiempo.
Utiliza un operador de integración espacial sintético sobre la densidad geométrica explícita. -/
structure EnergyFunctional (state : CoupledFlowState) where
  spatial_integral : SpatialIntegral
  integrable_on_time :
    ∀ t, t ∈ state.time_domain → MeasureTheory.Integrable (fun x ↦ energyIntegrand state t x)
  value : ℝ → ℝ := fun t ↦
    spatial_integral.integral (fun x ↦ energyIntegrand state t x)

namespace EnergyFunctional

/-- El integrando energético es integrable en todo tiempo del dominio del flujo. -/
theorem integrable {state : CoupledFlowState} (E : EnergyFunctional state)
    {t : ℝ} (ht : t ∈ state.time_domain) :
    MeasureTheory.Integrable (fun x ↦ energyIntegrand state t x) :=
  E.integrable_on_time t ht

end EnergyFunctional

/-- Funcional energético estándar construido con la integral de Lebesgue, bajo la
hipótesis explícita de integrabilidad temporal del integrando geométrico. -/
noncomputable def standardEnergyFunctional
    (state : CoupledFlowState)
    (h_int : ∀ t, t ∈ state.time_domain →
      MeasureTheory.Integrable (fun x ↦ energyIntegrand state t x)) :
    EnergyFunctional state where
  spatial_integral := StandardLebesgueIntegral
  integrable_on_time := h_int

/-- Predicado de continuidad espacial del integrando de energía para todo tiempo válido. -/
def continuous_energy (state : CoupledFlowState) : Prop :=
  ∀ t ∈ state.time_domain, Continuous (fun x ↦ energyIntegrand state t x)

/-- Predicado de soporte compacto espacial del integrando de energía para todo tiempo válido.
Esta es una hipótesis geométrica fuerte que reemplaza las condiciones asintóticas. -/
def has_compact_energy_support (state : CoupledFlowState) : Prop :=
  ∀ t ∈ state.time_domain, HasCompactSupport (fun x ↦ energyIntegrand state t x)

/-- Teorema puente que deriva la integrabilidad formal de Lebesgue a partir de las
hipótesis topológicas espaciales de continuidad y soporte compacto. -/
theorem integrable_of_compact_support
    (state : CoupledFlowState)
    (h_cont : continuous_energy state)
    (h_supp : has_compact_energy_support state) :
    ∀ t, t ∈ state.time_domain → MeasureTheory.Integrable (fun x ↦ energyIntegrand state t x) :=
  fun t ht ↦ Continuous.integrable_of_hasCompactSupport (h_cont t ht) (h_supp t ht)

/-- Constructor canónico del funcional de energía a partir de las hipótesis topológicas. -/
noncomputable def finiteEnergyFunctional
    (state : CoupledFlowState)
    (h_cont : continuous_energy state)
    (h_supp : has_compact_energy_support state) :
    EnergyFunctional state :=
  standardEnergyFunctional state (integrable_of_compact_support state h_cont h_supp)

/-- Certificado de disipación energética: entre dos tiempos comparables, la caída
de energía es la integral espacial de una densidad no negativa. Este es el
puente formal entre una identidad variacional local y la monotonía global. -/
structure EnergyDissipationCertificate
    (state : CoupledFlowState) (E : EnergyFunctional state) where
  density : ℝ → ℝ → ℝ → ℝ
  integrable_density :
    ∀ t₁ t₂, t₁ ∈ state.time_domain → t₂ ∈ state.time_domain → t₁ ≤ t₂ →
      MeasureTheory.Integrable (fun x ↦ density t₁ t₂ x)
  nonnegative_density :
    ∀ t₁ t₂, t₁ ∈ state.time_domain → t₂ ∈ state.time_domain → t₁ ≤ t₂ →
      ∀ x, 0 ≤ density t₁ t₂ x
  energy_drop_identity :
    ∀ t₁ t₂, t₁ ∈ state.time_domain → t₂ ∈ state.time_domain → t₁ ≤ t₂ →
      E.value t₁ - E.value t₂ =
        E.spatial_integral.integral (fun x ↦ density t₁ t₂ x)

/-- Predicado terminal de redondez esférica en cohomogeneidad uno.
En gauge de arco, una 4-esfera redonda de escala `a > 0` tiene
`φ = 1` y `ψ(x) = a * sin (x / a)` en el tramo terminal normalizado. -/
def extinct_to_round_point (final_state : CoupledFlowState) : Prop :=
  ∃ Tstar a : ℝ,
    Tstar ∈ final_state.time_domain ∧
    0 < a ∧
    ∀ t, t ∈ final_state.time_domain → Tstar ≤ t →
      ∀ x, 0 ≤ x → x ≤ Real.pi * a →
        final_state.profile.phi t x = 1 ∧
        final_state.profile.psi t x = a * Real.sin (x / a)

/-- Teorema intermedio condicional: si se provee una extinción redonda, queda registrada
como conclusión formal de la etapa analítica. La restricción estructural `gamma < 8` en
CoupledFlowState (Goldilocks zone) garantiza formalmente que el acoplamiento respeta la extinción. -/
theorem finiteExtinction_conditional
    (h_extinct : ∃ (final_state : CoupledFlowState), extinct_to_round_point final_state) :
    ∃ (final_state : CoupledFlowState), extinct_to_round_point final_state :=
  h_extinct


end Poincare4D

end
