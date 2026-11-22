/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.NBPeakEfficiency

public section
namespace GSTC.Scattering
namespace NBFeasibilityClassification

open scoped Matrix
open JonesOperatorClassification NBPeakEfficiency NBPhaseConstraints BIFeasibility

theorem spectralNorm_le_one_of_unitary {T : Ten2} (hT : T ∈ unitary Ten2) :
    spectralNorm T ≤ 1 := by
  apply (spectralNorm_le_one_iff T).mpr
  intro a
  have hunit : JonesUnitary T := (jonesUnitary_iff_mem_unitary T).mpr hT
  have h := jonesInner_of_jonesUnitary hunit a a
  rw [jonesInner_self_eq, jonesInner_self_eq] at h
  have heq : jonesNormSqR (T *ᵥ a) = jonesNormSqR a := by exact_mod_cast h
  exact le_of_eq heq

theorem nb_unitary_feasible_iff_symmetric (cfg : Config) (T : Ten2)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hT : T ∈ unitary Ten2) :
    (∃ z : ℂ, ∃ p : BIParams, ‖z‖ = 1 ∧ NoCoupling p ∧
        biForwardT cfg p = z • T) ↔ T.transpose = T := by
  constructor
  · rintro ⟨z, p, hz, hp, hzT⟩
    have hsym := forward_symmetric cfg p hk heq hp
    rw [hzT] at hsym
    have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0, norm_zero] at hz
      norm_num at hz
    have hcancel : z • T.transpose = z • T := by
      simpa only [Matrix.transpose_smul] using hsym
    have : T.transpose = T := by
      ext i j
      have h := congrArg (fun M : Ten2 => M i j) hcancel
      simp only [Matrix.smul_apply, smul_eq_mul] at h
      exact mul_left_cancel₀ hz0 h
    exact this
  · intro hsym
    exact nb_contraction_attained cfg T hk heq hsym
      (spectralNorm_le_one_of_unitary hT)

theorem two_state_symmetry_iff_cross {T : Ten2} {u₁ u₂ v₁ v₂ : Vec2} {α₁ α₂ : ℂ}
    (h1 : T *ᵥ u₁ = α₁ • v₁) (h2 : T *ᵥ u₂ = α₂ • v₂)
    (hu : Matrix.det (jonesColMatrix u₁ u₂) ≠ 0) :
    T.transpose = T ↔ α₁ * bilinear u₂ v₁ = α₂ * bilinear u₁ v₂ := by
  constructor
  · intro hT
    exact nb_two_state_phase_forced hT h1 h2
  · intro hc
    refine symmetric_of_cross T u₁ u₂ hu ?_
    rw [h1, h2, bilinear_smul_right, bilinear_smul_right]
    exact hc

theorem two_state_nb_feasibility (cfg : Config) (T : Ten2) {u₁ u₂ v₁ v₂ : Vec2}
    {α₁ α₂ : ℂ}
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hT : T ∈ unitary Ten2)
    (h1 : T *ᵥ u₁ = α₁ • v₁) (h2 : T *ᵥ u₂ = α₂ • v₂)
    (hu : Matrix.det (jonesColMatrix u₁ u₂) ≠ 0) :
    (∃ z : ℂ, ∃ p : BIParams, ‖z‖ = 1 ∧ NoCoupling p ∧
        biForwardT cfg p = z • T) ↔
      α₁ * bilinear u₂ v₁ = α₂ * bilinear u₁ v₂ := by
  constructor
  · rintro ⟨z, p, hz, hp, hzT⟩
    have hsym : T.transpose = T :=
      (nb_unitary_feasible_iff_symmetric cfg T hk heq hT).mp ⟨z, p, hz, hp, hzT⟩
    exact nb_two_state_phase_forced hsym h1 h2
  · intro hc
    have hsym : T.transpose = T := (two_state_symmetry_iff_cross h1 h2 hu).mpr hc
    exact (nb_unitary_feasible_iff_symmetric cfg T hk heq hT).mpr hsym

end NBFeasibilityClassification
end GSTC.Scattering
