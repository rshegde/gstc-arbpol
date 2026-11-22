/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.ClassFeasibility
public import GSTC.Scattering.OrthogonalClasses

public section
namespace GSTC.Scattering.ClassPeakEfficiency
open MaterialSpace ClassFeasibility BIFeasibility BIPhysicalFeasibility BIPolynomials BIAmplitudeFree
open scoped Matrix

@[expose] noncomputable def classRealizes (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η₁ η₂ : ℝ) : Prop :=
  ∃ p : BIParams, InClass c p ∧
    ∃ α₁ α₂ : ℂ,
      biForwardT cfg p *ᵥ u₁ = α₁ • v₁ ∧
      biForwardT cfg p *ᵥ u₂ = α₂ • v₂ ∧
      efficiency α₁ = η₁ ∧ efficiency α₂ = η₂

@[expose] noncomputable def classEqualEfficiencies (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) : Set ℝ :=
  {η | classRealizes cfg c u₁ u₂ v₁ v₂ η η}

@[expose] noncomputable def classPeakEqualEfficiency (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) : ℝ :=
  sSup (classEqualEfficiencies cfg c u₁ u₂ v₁ v₂)

theorem classRealizes_iff (cfg : Config) (c : SheetClass) (u₁ u₂ v₁ v₂ : Vec2)
    (η₁ η₂ : ℝ) (hv₁ : isNormalizedJones v₁) (hv₂ : isNormalizedJones v₂) :
    classRealizes cfg c u₁ u₂ v₁ v₂ η₁ η₂
      ↔ (classMaterials cfg c u₁ u₂ v₁ v₂ (η₁, η₂)).Nonempty := by
  constructor
  · rintro ⟨p, hc, α₁, α₂, h₁, h₂, he₁, he₂⟩
    refine ⟨assign p, ?_⟩
    rw [mem_classMaterials_iff]
    refine ⟨?_, ?_⟩
    · have h := (conversionMaterials_iff_conversions cfg u₁ u₂ v₁ v₂ (η₁, η₂) (assign p)
        hv₁ hv₂).mpr ⟨⟨α₁, by simpa only [parameters_assign] using h₁, he₁⟩,
          ⟨α₂, by simpa only [parameters_assign] using h₂, he₂⟩⟩
      simpa only [parameters_assign] using h
    · simpa only [parameters_assign] using hc
  · rintro ⟨x, hx⟩
    have hsplit := (mem_classMaterials_iff cfg c u₁ u₂ v₁ v₂ (η₁, η₂) x).mp hx
    obtain ⟨⟨α₁, h₁, he₁⟩, ⟨α₂, h₂, he₂⟩⟩ :=
      (conversionMaterials_iff_conversions cfg u₁ u₂ v₁ v₂ (η₁, η₂) x hv₁ hv₂).mp hsplit.1
    exact ⟨parameters x, hsplit.2, α₁, α₂, h₁, h₂, he₁, he₂⟩

@[expose] noncomputable def classPeakAttained (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) : Prop :=
  classRealizes cfg c u₁ u₂ v₁ v₂ (classPeakEqualEfficiency cfg c u₁ u₂ v₁ v₂)
    (classPeakEqualEfficiency cfg c u₁ u₂ v₁ v₂)

end GSTC.Scattering.ClassPeakEfficiency
