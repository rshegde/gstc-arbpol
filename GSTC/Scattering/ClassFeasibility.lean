/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.MaterialSpace

public section
namespace GSTC.Scattering.ClassFeasibility
open MaterialSpace BIFeasibility BIPhysicalFeasibility BIPolynomials BIAmplitudeFree
open scoped Matrix

@[expose] noncomputable def freeSpaceK0 (cfg : Config) : ℝ :=
  cfg.omega / cfg.vac.c0

theorem freeSpaceK0_pos (cfg : Config) : 0 < freeSpaceK0 cfg :=
  div_pos cfg.omega_pos cfg.vac.c0_pos

theorem freeSpaceK0_nonneg (cfg : Config) : 0 ≤ freeSpaceK0 cfg :=
  le_of_lt (freeSpaceK0_pos cfg)

@[expose] noncomputable def classMaterials (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) : Set MaterialCoordinates :=
  conversionMaterials cfg u₁ u₂ v₁ v₂ η ∩ classCoordinates c

theorem classMaterials_closed (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    IsClosed (classMaterials cfg c u₁ u₂ v₁ v₂ η) :=
  (conversionMaterials_closed cfg u₁ u₂ v₁ v₂ η).inter (classCoordinates_closed c)

theorem classMaterials_mem (cfg : Config) (c : SheetClass) (u₁ u₂ v₁ v₂ : Vec2)
    (η : ℝ × ℝ) (x : MaterialCoordinates)
    (hx : x ∈ conversionMaterials cfg u₁ u₂ v₁ v₂ η)
    (hc : InClass c (parameters x)) :
    x ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η :=
  ⟨hx, hc⟩

theorem mem_classMaterials_iff (cfg : Config) (c : SheetClass) (u₁ u₂ v₁ v₂ : Vec2)
    (η : ℝ × ℝ) (x : MaterialCoordinates) :
    x ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η ↔
      x ∈ conversionMaterials cfg u₁ u₂ v₁ v₂ η ∧ InClass c (parameters x) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩

theorem classMaterials_NB_subset_BI (cfg : Config) (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    classMaterials cfg .NB u₁ u₂ v₁ v₂ η ⊆ classMaterials cfg .BI u₁ u₂ v₁ v₂ η := by
  intro x hx
  have hsplit := (mem_classMaterials_iff cfg .NB u₁ u₂ v₁ v₂ η x).mp hx
  exact classMaterials_mem cfg .BI u₁ u₂ v₁ v₂ η x hsplit.1
    (NB_implies_BI (parameters x) hsplit.2)

end GSTC.Scattering.ClassFeasibility
