/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIFrontierCompletion

public section
namespace GSTC.Scattering
namespace BIUnitaryRealizability

open scoped Matrix
open BIFeasibility BIRankOneCompletion BIRankOneEndpoint BIFrontierCompletion
open OrthogonalClasses JonesOperatorClassification BIInverse
open NBPeakEfficiency NBPhaseConstraints
open GSTC.Scattering.Operator

theorem theta_eq_block : (Theta : Mat4) = block 0 1 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Theta, parityExchange, block, scatteringMatrix4]

theorem block_add (A B C D A' B' C' D' : Ten2) :
    block A B C D + block A' B' C' D' =
      block (A + A') (B + B') (C + C') (D + D') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, scatteringMatrix4, Matrix.add_apply]

theorem smul_block (z : ℂ) (A B C D : Ten2) :
    z • block A B C D = block (z • A) (z • B) (z • C) (z • D) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, scatteringMatrix4, Matrix.smul_apply, smul_eq_mul]

theorem parity_mul_block (A B C D : Ten2) :
    (Theta : Mat4) * block A B C D = block C D A B := by
  rw [theta_eq_block, block_mul]
  refine (block_eq_iff (0 * A + 1 * C) (0 * B + 1 * D) (1 * A + 0 * C) (1 * B + 0 * D)
    C D A B).mpr ⟨?_, ?_, ?_, ?_⟩
  · ext i j; simp
  · ext i j; simp
  · ext i j; simp
  · ext i j; simp

theorem one_add_block (A B C D : Ten2) :
    (1 : Mat4) + block A B C D = block (1 + A) B C (1 + D) := by
  have h1 : (1 : Mat4) = block 1 0 0 1 := block_one.symm
  rw [h1, block_add]
  refine (block_eq_iff (1 + A) (0 + B) (0 + C) (1 + D) (1 + A) B C (1 + D)).mpr
    ⟨rfl, ?_, ?_, rfl⟩
  · ext i j; simp
  · ext i j; simp

theorem smul_completion_zero (z : ℂ) (X : Ten2) :
    z • completion X 0 0 = completion (z • X) 0 0 := by
  rw [completion, completion, smul_block]
  simp only [smul_zero, Matrix.transpose_smul]

theorem one_add_parity_completion (X : Ten2) (z : ℂ) :
    (1 : Mat4) + (Theta : Mat4) * (z • completion X 0 0) =
      block (1 + z • X) 0 0 (1 + z • Xᵀ) := by
  rw [smul_completion_zero, completion, parity_mul_block, one_add_block]
  rw [Matrix.transpose_smul]

theorem one_add_parity_completion_isUnit (X : Ten2) (z : ℂ)
    (hdet : (1 + z • X).det ≠ 0) :
    IsUnit ((1 + (Theta : Mat4) * (z • completion X 0 0)).det) := by
  have hB : IsUnit (1 + z • X).det := isUnit_iff_ne_zero.mpr hdet
  have hBt : IsUnit (1 + z • Xᵀ).det := by
    have htr : (1 + z • Xᵀ).det = (1 + z • X).det := by
      have h : (1 + z • Xᵀ) = (1 + z • X)ᵀ := by
        rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]
      rw [h, Matrix.det_transpose]
    rw [htr]
    exact hB
  rw [one_add_parity_completion]
  have hAN : (block (1 + z • X) 0 0 (1 + z • Xᵀ)) *
      (block (1 + z • X)⁻¹ 0 0 (1 + z • Xᵀ)⁻¹) = 1 := by
    rw [block_mul]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [Matrix.mul_nonsing_inv _ hB, Matrix.mul_nonsing_inv _ hBt, block_one]
  exact isUnit_iff_ne_zero.mpr (Matrix.det_ne_zero_of_right_inverse hAN)

theorem bi_unitary_realizable (cfg : Config) (X : Ten2) (hX : X ∈ unitary Ten2) :
    ∃ z : ℂ, ∃ p : BIParams, ‖z‖ = 1 ∧ biForwardT cfg p = z • X := by
  obtain ⟨z, hz, hA, hB⟩ := phase_avoids_both X X
  have hzunit : z ∈ unitary ℂ := NBPhaseConstraints.nb_phase_mem_unitary z hz
  have hzX : z • X ∈ unitary Ten2 := Unitary.smul_mem_of_mem hzunit hX
  obtain ⟨hzu1, hzu2⟩ := Unitary.mem_iff.mp hzX
  have hzu1' : (z • X).conjTranspose * (z • X) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hzu1
  have hzu2' : (z • X) * (z • X).conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hzu2

  have hSsym : (completion (z • X) 0 0 : Mat4).transpose = completion (z • X) 0 0 := by
    simp only [completion, block_transpose, Matrix.transpose_zero, Matrix.transpose_transpose]
  have hSunit : (completion (z • X) 0 0 : Mat4).conjTranspose *
      completion (z • X) 0 0 = 1 := by
    rw [completion_unitary_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hh := (transpose_mul_conj_eq_one_iff (z • X)).mpr hzu1'
      simpa using hh
    · simp
    · simp
    · simpa using hzu2'

  have hpole : IsUnit ((1 + (Theta : Mat4) * (completion (z • X) 0 0)).det) := by
    rw [← smul_completion_zero]
    exact one_add_parity_completion_isUnit X z hA
  obtain ⟨p, hp⟩ := bi_inverse_complete cfg (completion (z • X) 0 0) hSsym hSunit hpole
  refine ⟨z, p, hz, ?_⟩
  have h1 : ∀ u : Vec2, biForwardT cfg p *ᵥ u = (z • X) *ᵥ u := by
    intro u
    rw [← readT_biPowerResponse4_pack cfg p u, hp.1, readT_completion]
  ext i j
  have hh := congrArg (fun w : Vec2 => (w) i) (h1 (jonesStd j))
  rw [mulVec_jonesStd, mulVec_jonesStd] at hh
  simp only [Matrix.smul_apply, smul_eq_mul] at hh ⊢
  exact hh

theorem two_state_bi_feasibility_iff_overlap (cfg : Config) (u₁ u₂ v₁ v₂ : Vec2)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hu₁ : isNormalized u₁) (hu₂ : isNormalized u₂)
    (hv₁ : isNormalized v₁) (hv₂ : isNormalized v₂)
    (hind : JonesIndependent u₁ u₂) :
    (∃ p : BIParams, ∃ α₁ α₂ : ℂ,
        biForwardT cfg p *ᵥ u₁ = α₁ • v₁ ∧ biForwardT cfg p *ᵥ u₂ = α₂ • v₂ ∧
        ‖α₁‖ = 1 ∧ ‖α₂‖ = 1) ↔
      jonesOverlap u₁ u₂ = jonesOverlap v₁ v₂ := by
  constructor
  · rintro ⟨p, α₁, α₂, h1, h2, ha1, ha2⟩
    have he1 : efficiency α₁ = 1 := by
      rw [efficiency, Complex.normSq_eq_norm_sq, ha1]
      norm_num
    have he2 : efficiency α₂ = 1 := by
      rw [efficiency, Complex.normSq_eq_norm_sq, ha2]
      norm_num
    have hunit := biForwardT_unitary_of_two_unit_efficiencies cfg p hk heq u₁ u₂ v₁ v₂
      hu₁ hu₂ hv₁ hv₂ hind α₁ α₂ h1 h2 he1 he2
    by_contra hne
    exact (not_exists_jonesUnitary_of_neq_overlap u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hind hne)
      ⟨biForwardT cfg p, hunit.2, α₁, α₂, ha1, ha2, h1, h2⟩
  · intro hoverlap
    obtain ⟨T, hT, α₁, α₂, ha1, ha2, hT1, hT2⟩ :=
      (exists_jonesUnitary_iff u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hind).mp hoverlap
    obtain ⟨z, p, hz, hzp⟩ := bi_unitary_realizable cfg T ((jonesUnitary_iff_mem_unitary T).mp hT)
    refine ⟨p, z • α₁, z • α₂, ?_, ?_, ?_, ?_⟩
    · rw [hzp, Matrix.smul_mulVec, hT1, smul_smul]
      simp [smul_eq_mul]
    · rw [hzp, Matrix.smul_mulVec, hT2, smul_smul]
      simp [smul_eq_mul]
    · rw [norm_smul, hz, ha1]
      norm_num
    · rw [norm_smul, hz, ha2]
      norm_num

end BIUnitaryRealizability
end GSTC.Scattering
