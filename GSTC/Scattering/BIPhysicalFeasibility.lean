/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIFeasibility
public import GSTC.Scattering.Efficiency

open scoped Matrix

public section

namespace GSTC.Scattering
namespace BIPhysicalFeasibility

open GSTC.Scattering.BIFeasibility

@[expose] noncomputable def jonesNorm (u : Vec2) : ℝ := Real.sqrt (jonesNormSqR u)

theorem jonesInner_eq_cast (u : Vec2) : jonesInner u u = ↑(jonesNormSqR u) := by
  have h := jonesInner_conj u u
  rw [eq_star_iff_eq_ofReal_re h.symm]
  rfl

@[expose] def isNormalizedJones (u : Vec2) : Prop := jonesNorm u = 1

theorem isNormalizedJones_iff (u : Vec2) : isNormalizedJones u ↔ isNormalized u := by
  constructor
  · intro h
    simp only [isNormalizedJones] at h
    rw [jonesNorm] at h
    have h1 := Real.sq_sqrt (jonesNormSqR_nonneg u)
    rw [h] at h1
    simp at h1
    rw [isNormalized, jonesInner_eq_cast]
    exact_mod_cast h1.symm
  · intro h
    have hsq : jonesNormSqR u = 1 := congrArg Complex.re h
    rw [isNormalizedJones, jonesNorm, hsq]
    simp

theorem jonesNormSqR_eq_one_of_normalized {u : Vec2} (h : isNormalizedJones u) :
    jonesNormSqR u = 1 :=
  isNormalized_jonesNormSqR u ((isNormalizedJones_iff u).mp h)

@[expose] def PhysicalFeasible (cfg : Config) (c : SheetClass) (b : Budget)
    (u₁ u₂ v₁ v₂ : Vec2) (η₁ η₂ : ℝ) : Prop :=
  isNormalizedJones u₁ ∧ isNormalizedJones u₂ ∧ isNormalizedJones v₁ ∧
    isNormalizedJones v₂ ∧
  ∃ p : BIParams, InClass c p ∧ WithinBudget b p ∧
    ∃ α₁ α₂ : ℂ,
      biForwardT cfg p *ᵥ u₁ = α₁ • v₁ ∧
      biForwardT cfg p *ᵥ u₂ = α₂ • v₂ ∧
      efficiency α₁ = η₁ ∧ efficiency α₂ = η₂

end BIPhysicalFeasibility

end GSTC.Scattering
