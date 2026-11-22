/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.JonesFrameCorrespondence

public section
set_option autoImplicit false
namespace GSTC.Scattering.JonesFrameSpectralMinimum
open JonesFrameCorrespondence PauliRepresentation OrthogonalSpectralPhase
open BIFeasibility BIPolynomials MaterialSpace ClassFeasibility ClassMinimumBudget
open SusceptibilityBudget

theorem efficiency_eq_one_iff (a : ℂ) : efficiency a = 1 ↔ ‖a‖ = 1 := by
  rw [efficiency, Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg a]

theorem material_feasible_iff (cfg : Config) (cls : SheetClass) (U V : Ten2)
    (hU : U ∈ unitary Ten2) (hV : V ∈ unitary Ten2) (x : MaterialCoordinates) :
    x ∈ classMaterials cfg cls (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1) ↔
    InClass cls (parameters x) ∧ frameFamily U V (biForwardT cfg (parameters x)) := by
  rw [mem_classMaterials_iff, conversionMaterials_iff_conversions cfg _ _ _ _ _ _
    (column_normalized V hV 0) (column_normalized V hV 1),
    frameFamily_iff_columns U V _ hU]
  simp only [efficiency_eq_one_iff]
  constructor
  · rintro ⟨⟨⟨a,ha,hea⟩,⟨b,hb,heb⟩⟩,hc⟩
    exact ⟨hc,a,b,hea,heb,ha,hb⟩
  · rintro ⟨hc,a,b,hea,heb,ha,hb⟩
    exact ⟨⟨⟨a,ha,hea⟩,⟨b,hb,heb⟩⟩,hc⟩

private theorem minimum_of_bounds (cfg : Config) (cls : SheetClass)
    (U V : Ten2) (B : ℝ)
    (hl : ∀ x ∈ classMaterials cfg cls (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1), B ≤ spectralTotalBudget cfg x)
    (hw : ∃ x ∈ classMaterials cfg cls (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1), spectralTotalBudget cfg x = B) :
    minimumBudget cfg cls (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1) = (B : WithTop ℝ) := by
  obtain ⟨x,hx,hb⟩ := hw
  obtain ⟨y,hy,hm,hmin⟩ := minimumBudget_attained cfg cls _ _ _ _ (1,1) ⟨x,hx⟩
  rw [hm]
  congr 1
  exact le_antisymm ((hmin x hx).trans hb.le) (hl y hy)

theorem bi_minimum_eq (cfg : Config) (U V : Ten2) (z : ℂ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hU : U ∈ unitary Ten2) (hV : V ∈ unitary Ten2) (hz : ‖z‖ = 1)
    (hd : (base U V z).det = 1) (t₀ : ℝ)
    (hmin : ∀ t, phaseMinimum cfg (frameCoefficients U V z) t₀ ≤
      phaseMinimum cfg (frameCoefficients U V z) t) :
    minimumBudget cfg .BI (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1) =
        (phaseMinimum cfg (frameCoefficients U V z) t₀ : WithTop ℝ) ∧
    ∃ p : BIParams, assign p ∈ classMaterials cfg .BI (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1) ∧
      spectralTotalBudget cfg (assign p) = phaseMinimum cfg (frameCoefficients U V z) t₀ := by
  obtain ⟨h₁,h₂,h₃⟩ := frameCoefficients_orthonormal U V z hU hV hz hd
  obtain ⟨hl,_,α,p,hp,hb⟩ :=
    biMinimum_eq_phaseFamily cfg _ t₀ hk heq h₁ h₂ h₃ hmin
  have hlow : ∀ x ∈ classMaterials cfg .BI (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1),
      phaseMinimum cfg (frameCoefficients U V z) t₀ ≤ spectralTotalBudget cfg x := by
    intro x hx
    have hf := ((material_feasible_iff cfg .BI U V hU hV x).mp hx).2
    obtain ⟨t,β,ht⟩ := (frameFamily_iff_phaseTransmission U V z hU hV hz hd _).mp hf
    simpa only [assign_parameters] using hl t β (parameters x) ht
  have hmem : assign p ∈ classMaterials cfg .BI (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1) := by
    apply (material_feasible_iff cfg .BI U V hU hV _).mpr
    refine ⟨trivial,?_⟩
    rw [parameters_assign]
    exact (frameFamily_iff_phaseTransmission U V z hU hV hz hd _).mpr ⟨t₀,α,hp⟩
  exact ⟨minimum_of_bounds cfg .BI U V _ hlow ⟨assign p,hmem,hb⟩,p,hmem,hb⟩

theorem nb_minimum_eq (cfg : Config) (U V : Ten2) (z : ℂ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hU : U ∈ unitary Ten2) (hV : V ∈ unitary Ten2) (hz : ‖z‖ = 1)
    (hd : (base U V z).det = 1) (t₀ : ℝ)
    (hadm : nbAdmissible (frameCoefficients U V z) t₀)
    (hmin : ∀ t, nbAdmissible (frameCoefficients U V z) t →
      phaseMinimum cfg (frameCoefficients U V z) t₀ ≤
        phaseMinimum cfg (frameCoefficients U V z) t) :
    minimumBudget cfg .NB (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1) =
        (phaseMinimum cfg (frameCoefficients U V z) t₀ : WithTop ℝ) ∧
    ∃ p : BIParams, assign p ∈ classMaterials cfg .NB (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1) ∧
      spectralTotalBudget cfg (assign p) = phaseMinimum cfg (frameCoefficients U V z) t₀ := by
  obtain ⟨h₁,h₂,h₃⟩ := frameCoefficients_orthonormal U V z hU hV hz hd
  obtain ⟨hl,_,α,p,hnc,hp,hb⟩ :=
    nbMinimum_eq_phaseFamily cfg _ t₀ hk heq h₁ h₂ h₃ hadm hmin
  have hlow : ∀ x ∈ classMaterials cfg .NB (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1),
      phaseMinimum cfg (frameCoefficients U V z) t₀ ≤ spectralTotalBudget cfg x := by
    intro x hx
    obtain ⟨hc,hf⟩ := (material_feasible_iff cfg .NB U V hU hV x).mp hx
    obtain ⟨t,β,ht⟩ := (frameFamily_iff_phaseTransmission U V z hU hV hz hd _).mp hf
    simpa only [assign_parameters] using hl t β (parameters x) hc ht
  have hmem : assign p ∈ classMaterials cfg .NB (column U 0) (column U 1)
      (column V 0) (column V 1) (1,1) := by
    apply (material_feasible_iff cfg .NB U V hU hV _).mpr
    rw [parameters_assign]
    exact ⟨hnc,(frameFamily_iff_phaseTransmission U V z hU hV hz hd _).mpr ⟨t₀,α,hp⟩⟩
  exact ⟨minimum_of_bounds cfg .NB U V _ hlow ⟨assign p,hmem,hb⟩,p,hmem,hb⟩

theorem frame_minima_attained (cfg : Config) (U V : Ten2)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hU : U ∈ unitary Ten2) (hV : V ∈ unitary Ten2) :
    ∃ z : ℂ, ∃ tBI tNB : ℝ,
      ‖z‖ = 1 ∧ (base U V z).det = 1 ∧
      (∀ t, phaseMinimum cfg (frameCoefficients U V z) tBI ≤
        phaseMinimum cfg (frameCoefficients U V z) t) ∧
      nbAdmissible (frameCoefficients U V z) tNB ∧
      (∀ t, nbAdmissible (frameCoefficients U V z) t →
        phaseMinimum cfg (frameCoefficients U V z) tNB ≤
          phaseMinimum cfg (frameCoefficients U V z) t) ∧
      minimumBudget cfg .BI (column U 0) (column U 1)
        (column V 0) (column V 1) (1,1) =
          (phaseMinimum cfg (frameCoefficients U V z) tBI : WithTop ℝ) ∧
      minimumBudget cfg .NB (column U 0) (column U 1)
        (column V 0) (column V 1) (1,1) =
          (phaseMinimum cfg (frameCoefficients U V z) tNB : WithTop ℝ) ∧
      (∃ p : BIParams, assign p ∈ classMaterials cfg .BI (column U 0) (column U 1)
        (column V 0) (column V 1) (1,1) ∧ spectralTotalBudget cfg (assign p) =
          phaseMinimum cfg (frameCoefficients U V z) tBI) ∧
      (∃ p : BIParams, assign p ∈ classMaterials cfg .NB (column U 0) (column U 1)
        (column V 0) (column V 1) (1,1) ∧ spectralTotalBudget cfg (assign p) =
          phaseMinimum cfg (frameCoefficients U V z) tNB) := by
  obtain ⟨z,hz,hd⟩ := exists_frameCoefficients U V hU hV
  obtain ⟨tBI,hBI⟩ := biPhaseMinimum_exists cfg (frameCoefficients U V z)
  obtain ⟨tNB,hadm,hNB⟩ := nbPhaseMinimum_exists cfg (frameCoefficients U V z)
  have hb := bi_minimum_eq cfg U V z hk heq hU hV hz hd tBI hBI
  have hn := nb_minimum_eq cfg U V z hk heq hU hV hz hd tNB hadm hNB
  exact ⟨z,tBI,tNB,hz,hd,hBI,hadm,hNB,hb.1,hn.1,hb.2,hn.2⟩

end GSTC.Scattering.JonesFrameSpectralMinimum
