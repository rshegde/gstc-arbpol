/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.OrthogonalSpectralPhase
public import GSTC.Scattering.JonesFrameSpectralMinimum
public import GSTC.Scattering.MaterialSpace
public import GSTC.Scattering.ClassFeasibility
public import GSTC.Scattering.ClassMinimumBudget
public import GSTC.Scattering.JonesOperatorClassification
public import GSTC.Scattering.PauliRepresentation

public section
set_option autoImplicit false

namespace GSTC.Scattering.UnitaryRotationCapacity

open scoped Matrix
open Matrix PauliRepresentation OrthogonalSpectralPhase OrthogonalSpectralOptimum
open OrthogonalSpectralPole OrthogonalSpectralNB OrthogonalSpectralBridge
open JonesOperatorClassification MaterialSpace ClassFeasibility ClassMinimumBudget
open BIFeasibility BIPolynomials SusceptibilityBudget JonesFrameCorrespondence
open JonesFrameSpectralMinimum

structure Axis where

  n_x : ℝ

  n_y : ℝ

  n_z : ℝ

  unit : n_x ^ 2 + n_y ^ 2 + n_z ^ 2 = 1

@[expose] noncomputable def rotationOperator (n : Axis) (Θ : ℝ) : Ten2 :=
  pauliForm (Real.cos (Θ / 2)) (-Real.sin (Θ / 2) * n.n_x)
    (-Real.sin (Θ / 2) * n.n_y) (-Real.sin (Θ / 2) * n.n_z)

@[expose] noncomputable def rotationCoefficients (n : Axis) (Θ : ℝ) : PhaseCoefficients :=
  ⟨Real.cos (Θ / 2), -Real.sin (Θ / 2) * n.n_x, -Real.sin (Θ / 2) * n.n_y,
    -Real.sin (Θ / 2) * n.n_z, 0, 0, 0, 0⟩

theorem rotationOperator_unitary (n : Axis) (Θ : ℝ) :
    rotationOperator n Θ ∈ unitary Ten2 ∧ (rotationOperator n Θ).det = 1 := by
  have hs : (Real.cos (Θ / 2)) ^ 2 + (-Real.sin (Θ / 2) * n.n_x) ^ 2
      + (-Real.sin (Θ / 2) * n.n_y) ^ 2 + (-Real.sin (Θ / 2) * n.n_z) ^ 2 = 1 := by
    calc Real.cos (Θ / 2) ^ 2
        + (-Real.sin (Θ / 2) * n.n_x) ^ 2
        + (-Real.sin (Θ / 2) * n.n_y) ^ 2
        + (-Real.sin (Θ / 2) * n.n_z) ^ 2
        = Real.cos (Θ / 2) ^ 2
          + Real.sin (Θ / 2) ^ 2 * (n.n_x ^ 2 + n.n_y ^ 2 + n.n_z ^ 2) := by ring
      _ = Real.cos (Θ / 2) ^ 2 + Real.sin (Θ / 2) ^ 2 := by rw [n.unit]; ring
      _ = 1 := Real.cos_sq_add_sin_sq (Θ / 2)
  exact pauliForm_special_unitary (Real.cos (Θ / 2)) (-Real.sin (Θ / 2) * n.n_x)
    (-Real.sin (Θ / 2) * n.n_y) (-Real.sin (Θ / 2) * n.n_z) hs

theorem rotationOperator_eq_phaseMatrix (n : Axis) (Θ : ℝ) :
    rotationOperator n Θ = phaseMatrix (rotationCoefficients n Θ) 0 := by
  rw [OrthogonalSpectralNB.phaseMatrix_eq_pauliForm]
  simp [phaseQ, phaseRx, phaseRy, phaseRz, rotationCoefficients, rotationOperator,
    Real.cos_zero, Real.sin_zero]

theorem rotationCoefficients_sphere (n : Axis) (Θ : ℝ) :
    phaseQ (rotationCoefficients n Θ) 0 ^ 2 + phaseRx (rotationCoefficients n Θ) 0 ^ 2
      + phaseRy (rotationCoefficients n Θ) 0 ^ 2 + phaseRz (rotationCoefficients n Θ) 0 ^ 2 = 1 := by
  simp [phaseQ, phaseRx, phaseRy, phaseRz, rotationCoefficients, Real.cos_zero,
    Real.sin_zero]
  calc Real.cos (Θ / 2) ^ 2
      + (Real.sin (Θ / 2) * n.n_x) ^ 2
      + (Real.sin (Θ / 2) * n.n_y) ^ 2
      + (Real.sin (Θ / 2) * n.n_z) ^ 2
      = Real.cos (Θ / 2) ^ 2
        + Real.sin (Θ / 2) ^ 2 * (n.n_x ^ 2 + n.n_y ^ 2 + n.n_z ^ 2) := by ring
    _ = Real.cos (Θ / 2) ^ 2 + Real.sin (Θ / 2) ^ 2 := by rw [n.unit]; ring
    _ = 1 := Real.cos_sq_add_sin_sq (Θ / 2)

theorem rotation_phaseCoordinates (n : Axis) (Θ : ℝ) :
    phaseQ (rotationCoefficients n Θ) 0 = Real.cos (Θ / 2) ∧
    phaseRx (rotationCoefficients n Θ) 0 = -Real.sin (Θ / 2) * n.n_x ∧
    phaseRy (rotationCoefficients n Θ) 0 = -Real.sin (Θ / 2) * n.n_y ∧
    phaseRz (rotationCoefficients n Θ) 0 = -Real.sin (Θ / 2) * n.n_z := by
  simp [phaseQ, phaseRx, phaseRy, phaseRz, rotationCoefficients, Real.cos_zero,
    Real.sin_zero]

private theorem rotation_half_angle (Θ : ℝ) (hΘ : 0 ≤ Θ) (hΘπ : Θ ≤ Real.pi) :
    2 * Real.sin (Θ / 2) / (1 + Real.cos (Θ / 2)) = 2 * Real.tan (Θ / 4) := by
  have hcos4 : 0 < Real.cos (Θ / 4) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin2 : Real.sin (Θ / 2) = 2 * Real.sin (Θ / 4) * Real.cos (Θ / 4) := by
    have h : Θ / 2 = 2 * (Θ / 4) := by ring
    rw [h, Real.sin_two_mul]
  have hcos2 : Real.cos (Θ / 2) = 2 * Real.cos (Θ / 4) ^ 2 - 1 := by
    have h : Θ / 2 = 2 * (Θ / 4) := by ring
    rw [h, Real.cos_two_mul]
  have h1 : 2 * Real.sin (Θ / 2) / (1 + Real.cos (Θ / 2))
      = 2 * (2 * Real.sin (Θ / 4) * Real.cos (Θ / 4)) / (2 * Real.cos (Θ / 4) ^ 2) := by
    rw [hsin2, hcos2]; ring
  have h2 : 2 * (2 * Real.sin (Θ / 4) * Real.cos (Θ / 4)) / (2 * Real.cos (Θ / 4) ^ 2)
      = 2 * (Real.sin (Θ / 4) / Real.cos (Θ / 4)) := by
    field_simp
  rw [h1, h2, Real.tan_eq_sin_div_cos]

theorem rotation_phaseMinimum (cfg : Config) (n : Axis) (Θ : ℝ)
    (hΘ : 0 ≤ Θ) (hΘπ : Θ ≤ Real.pi)
    (hω : cfg.omega = 1) (hηu : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1) :
    phaseMinimum cfg (rotationCoefficients n Θ) 0
      = 2 * Real.tan (Θ / 4) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| := by
  have hE : spectralElectricScale cfg = 1 := by
    simp [spectralElectricScale, hω, hηu, heps]
  have hM : spectralMagneticScale cfg = 1 := by
    simp [spectralMagneticScale, hηu, hω, hmu]
  have hC : spectralChiralScale cfg = 1 := by
    simp [spectralChiralScale, hc0, hω]
  have hK : ClassFeasibility.freeSpaceK0 cfg = 1 := by
    simp [ClassFeasibility.freeSpaceK0, hω, hc0]
  have hs : 0 ≤ Real.sin (Θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hc : 0 ≤ Real.cos (Θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hxz : n.n_x ^ 2 + n.n_z ^ 2 = 1 - n.n_y ^ 2 := by linarith [n.unit]
  obtain ⟨hq, hrx, hry, hrz⟩ := rotation_phaseCoordinates n Θ
  have hsqrt : Real.sqrt (phaseRx (rotationCoefficients n Θ) 0 ^ 2
      + phaseRz (rotationCoefficients n Θ) 0 ^ 2)
      = Real.sin (Θ / 2) * Real.sqrt (n.n_x ^ 2 + n.n_z ^ 2) := by
    calc Real.sqrt (phaseRx (rotationCoefficients n Θ) 0 ^ 2
          + phaseRz (rotationCoefficients n Θ) 0 ^ 2)
        = Real.sqrt (Real.sin (Θ / 2) ^ 2 * (n.n_x ^ 2 + n.n_z ^ 2)) := by
          rw [hrx, hrz]; ring
      _ = Real.sqrt (Real.sin (Θ / 2) ^ 2) * Real.sqrt (n.n_x ^ 2 + n.n_z ^ 2) :=
        Real.sqrt_mul (sq_nonneg _) (n.n_x ^ 2 + n.n_z ^ 2)
      _ = Real.sin (Θ / 2) * Real.sqrt (n.n_x ^ 2 + n.n_z ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
  have hmax : max (Real.sin (Θ / 2) * Real.sqrt (1 - n.n_y ^ 2))
      (Real.sin (Θ / 2) * |n.n_y|)
      = Real.sin (Θ / 2) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| := by
    calc max (Real.sin (Θ / 2) * Real.sqrt (1 - n.n_y ^ 2)) (Real.sin (Θ / 2) * |n.n_y|)
        = max (Real.sqrt (1 - n.n_y ^ 2) * Real.sin (Θ / 2))
          (|n.n_y| * Real.sin (Θ / 2)) := by
            rw [mul_comm (Real.sin (Θ / 2)) (Real.sqrt (1 - n.n_y ^ 2)),
              mul_comm (Real.sin (Θ / 2)) |n.n_y|]
      _ = max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| * Real.sin (Θ / 2) :=
        (max_mul_of_nonneg _ _ hs).symm
      _ = Real.sin (Θ / 2) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| := by
        rw [mul_comm]
  have hmax0 : max (max 1 1 * Real.sqrt (phaseRx (rotationCoefficients n Θ) 0 ^ 2
        + phaseRz (rotationCoefficients n Θ) 0 ^ 2))
      (1 * |phaseRy (rotationCoefficients n Θ) 0|)
      = max (Real.sqrt (phaseRx (rotationCoefficients n Θ) 0 ^ 2
        + phaseRz (rotationCoefficients n Θ) 0 ^ 2))
        (|phaseRy (rotationCoefficients n Θ) 0|) := by
    rw [max_eq_left (le_refl 1), one_mul, one_mul]
  simp only [phaseMinimum, hE, hM, hC, hK]
  rw [hmax0]
  simp only [one_mul]
  rw [hsqrt, hxz, hry, hq, abs_mul, abs_neg, abs_of_nonneg hs,
    abs_of_nonneg hc, hmax]
  have hfinal : 2 * (Real.sin (Θ / 2) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y|)
      / (1 + Real.cos (Θ / 2))
      = (2 * Real.sin (Θ / 2) / (1 + Real.cos (Θ / 2)))
        * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| := by ring
  rw [hfinal, rotation_half_angle Θ hΘ hΘπ]

example (cfg : Config) (n : Axis)
    (hω : cfg.omega = 1) (hηu : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1) :
    phaseMinimum cfg (rotationCoefficients n 0) 0 = 0 := by
  have h := rotation_phaseMinimum cfg n 0 (by norm_num) (by linarith [Real.pi_pos])
    hω hηu heps hmu hc0
  rw [h]
  simp

example (cfg : Config) (n : Axis)
    (hω : cfg.omega = 1) (hηu : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1) :
    phaseMinimum cfg (rotationCoefficients n Real.pi) 0
      = 2 * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| := by
  have h := rotation_phaseMinimum cfg n Real.pi (by linarith [Real.pi_pos]) (by norm_num)
    hω hηu heps hmu hc0
  rw [h, Real.tan_pi_div_four]
  ring

theorem rotationOperator_eq_phaseTransmission (n : Axis) (Θ φ : ℝ) :
    Complex.exp (Complex.I * φ) • rotationOperator n Θ
      = phaseTransmission (rotationCoefficients n Θ) 0 φ := by
  simp only [phaseTransmission, rotationOperator_eq_phaseMatrix n Θ]

theorem rotation_budget_lower_bound (cfg : Config) (n : Axis) (Θ : ℝ)
    (hΘ : 0 ≤ Θ) (hΘπ : Θ ≤ Real.pi)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hω : cfg.omega = 1) (hηu : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1)
    (φ : ℝ) (p : BIParams)
    (hp : biForwardT cfg p = Complex.exp (Complex.I * φ) • rotationOperator n Θ) :
    2 * Real.tan (Θ / 4) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y|
      ≤ spectralTotalBudget cfg (assign p) := by
  have hp' : biForwardT cfg p = phaseTransmission (rotationCoefficients n Θ) 0 φ := by
    calc biForwardT cfg p = Complex.exp (Complex.I * φ) • rotationOperator n Θ := hp
      _ = phaseTransmission (rotationCoefficients n Θ) 0 φ :=
        rotationOperator_eq_phaseTransmission n Θ φ
  have hopt := fixedPhase_spectral_optimum_all cfg (rotationCoefficients n Θ) 0 φ hk heq
    (rotationCoefficients_sphere n Θ) p hp'
  rw [rotation_phaseMinimum cfg n Θ hΘ hΘπ hω hηu heps hmu hc0] at hopt
  exact hopt

private theorem rotation_forwardT_eq_phase (cfg : Config) (n : Axis) (Θ : ℝ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (u₁ u₂ v₁ v₂ : Vec2)
    (hu₁ : isNormalized u₁) (hu₂ : isNormalized u₂)
    (hv₁ : isNormalized v₁) (hv₂ : isNormalized v₂)
    (hind : JonesIndependent u₁ u₂)
    (hoverlap : jonesInner v₁ v₂ ≠ 0)
    (hU₁ : v₁ = rotationOperator n Θ *ᵥ u₁)
    (hU₂ : v₂ = rotationOperator n Θ *ᵥ u₂)
    (x : MaterialCoordinates)
    (hx : x ∈ classMaterials cfg .BI u₁ u₂ v₁ v₂ (1,1)) :
    ∃ φ : ℝ, biForwardT cfg (parameters x) = Complex.exp (Complex.I * φ) • rotationOperator n Θ := by
  have hsplit := (mem_classMaterials_iff cfg .BI u₁ u₂ v₁ v₂ (1,1) x).mp hx
  obtain ⟨⟨α₁, ht₁, he₁⟩, ⟨α₂, ht₂, he₂⟩⟩ :=
    (conversionMaterials_iff_conversions cfg u₁ u₂ v₁ v₂ (1,1) x
      ((BIPhysicalFeasibility.isNormalizedJones_iff v₁).mpr hv₁)
      ((BIPhysicalFeasibility.isNormalizedJones_iff v₂).mpr hv₂)).mp hsplit.1
  have hrel := biForwardT_relative_phase_at_unit_efficiency cfg (parameters x) hk heq
    u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hind α₁ α₂ ht₁ ht₂ he₁ he₂
  have hunit : JonesUnitary (rotationOperator n Θ) :=
    (jonesUnitary_iff_mem_unitary (rotationOperator n Θ)).mpr (rotationOperator_unitary n Θ).1
  have hpair := jonesInner_of_jonesUnitary hunit u₁ u₂
  have hvv : jonesInner v₁ v₂ = jonesInner u₁ u₂ := by
    rw [hU₁, hU₂]; exact hpair
  have hrel' : star α₁ * α₂ * jonesInner v₁ v₂ = jonesInner v₁ v₂ := hrel.trans hvv.symm

  have hphase : star α₁ * α₂ = (1 : ℂ) := by
    apply mul_right_cancel₀ hoverlap
    simpa only [one_mul] using hrel'
  have hn₁ : ‖α₁‖ = 1 := (efficiency_eq_one_iff α₁).mp he₁
  have hα₂ : α₂ = α₁ := by
    have h1 : α₁ * star α₁ = 1 := by
      rw [mul_comm]; exact unit_phase_star_mul α₁ hn₁
    have h2 : α₁ * (star α₁ * α₂) = α₁ := by rw [hphase, mul_one]
    rw [← mul_assoc] at h2
    rw [h1, one_mul] at h2
    exact h2
  have hdet : (jonesColMatrix u₁ u₂).det ≠ 0 := jonesIndependent_det_ne_zero u₁ u₂ hind
  have hM₁ : (biForwardT cfg (parameters x) - α₁ • rotationOperator n Θ) *ᵥ u₁ = 0 := by
    rw [Matrix.sub_mulVec, ht₁, hU₁, smul_mulVec]
    simp
  have hM₂ : (biForwardT cfg (parameters x) - α₁ • rotationOperator n Θ) *ᵥ u₂ = 0 := by
    rw [Matrix.sub_mulVec, ht₂, hα₂, hU₂, smul_mulVec]
    simp
  have hT : biForwardT cfg (parameters x) = α₁ • rotationOperator n Θ :=
    eq_of_sub_eq_zero (ten2_eq_zero_of_mulVec_eq_zero hM₁ hM₂ hdet)
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff α₁).mp hn₁
  refine ⟨θ, ?_⟩
  rw [hT, hθ.symm, mul_comm]

theorem rotation_material_minimum (cfg : Config) (n : Axis) (Θ : ℝ)
    (hΘ : 0 ≤ Θ) (hΘπ : Θ ≤ Real.pi)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hω : cfg.omega = 1) (hηu : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1)
    (u₁ u₂ v₁ v₂ : Vec2)
    (hu₁ : BIPhysicalFeasibility.isNormalizedJones u₁)
    (hu₂ : BIPhysicalFeasibility.isNormalizedJones u₂)
    (hw₁ : BIPhysicalFeasibility.isNormalizedJones v₁)
    (hw₂ : BIPhysicalFeasibility.isNormalizedJones v₂)
    (hind : JonesIndependent u₁ u₂)
    (hoverlap : jonesInner v₁ v₂ ≠ 0)
    (hv₁ : v₁ = rotationOperator n Θ *ᵥ u₁)
    (hv₂ : v₂ = rotationOperator n Θ *ᵥ u₂) :
    minimumBudget cfg .BI u₁ u₂ v₁ v₂ (1,1)
        = (2 * Real.tan (Θ / 4) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| : WithTop ℝ) ∧
    ∃ x ∈ classMaterials cfg .BI u₁ u₂ v₁ v₂ (1,1),
      spectralTotalBudget cfg x
        = 2 * Real.tan (Θ / 4) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| := by
  have hu₁' : isNormalized u₁ := (BIPhysicalFeasibility.isNormalizedJones_iff u₁).mp hu₁
  have hu₂' : isNormalized u₂ := (BIPhysicalFeasibility.isNormalizedJones_iff u₂).mp hu₂
  have hw₁' : isNormalized v₁ := (BIPhysicalFeasibility.isNormalizedJones_iff v₁).mp hw₁
  have hw₂' : isNormalized v₂ := (BIPhysicalFeasibility.isNormalizedJones_iff v₂).mp hw₂

  have hlow : ∀ x ∈ classMaterials cfg .BI u₁ u₂ v₁ v₂ (1,1),
      2 * Real.tan (Θ / 4) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y|
        ≤ spectralTotalBudget cfg x := by
    intro x hx
    obtain ⟨φ, hφ⟩ :=
      rotation_forwardT_eq_phase cfg n Θ hk heq u₁ u₂ v₁ v₂ hu₁' hu₂' hw₁' hw₂'
        hind hoverlap hv₁ hv₂ x hx
    have hb := rotation_budget_lower_bound cfg n Θ hΘ hΘπ hk heq hω hηu heps hmu hc0
      φ (parameters x) hφ
    rwa [assign_parameters] at hb

  have hq : 0 ≤ phaseQ (rotationCoefficients n Θ) 0 := by
    have hc : 0 ≤ Real.cos (Θ / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    simpa [phaseQ, rotationCoefficients, Real.cos_zero] using hc
  obtain ⟨p, hp, hb⟩ := fixedPhase_spectral_optimum_attained_zero cfg
    (rotationCoefficients n Θ) 0 (rotationCoefficients_sphere n Θ) hq
  have hpT : biForwardT cfg p = rotationOperator n Θ := by
    rw [hp, phaseTransmission]
    simp
    exact (rotationOperator_eq_phaseMatrix n Θ).symm
  have hb' : spectralTotalBudget cfg (assign p)
      = 2 * Real.tan (Θ / 4) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| :=
    hb.trans (rotation_phaseMinimum cfg n Θ hΘ hΘπ hω hηu heps hmu hc0)
  have hmem : assign p ∈ classMaterials cfg .BI u₁ u₂ v₁ v₂ (1,1) := by
    apply classMaterials_mem cfg .BI u₁ u₂ v₁ v₂ (1,1) (assign p)
    · rw [conversionMaterials_iff_conversions cfg u₁ u₂ v₁ v₂ (1,1) (assign p) hw₁ hw₂]
      refine ⟨⟨1, ?_, ?_⟩, ⟨1, ?_, ?_⟩⟩
      · rw [parameters_assign, hpT, hv₁]
        simp
      · exact (efficiency_eq_one_iff (1 : ℂ)).mpr (by simp)
      · rw [parameters_assign, hpT, hv₂]
        simp
      · exact (efficiency_eq_one_iff (1 : ℂ)).mpr (by simp)
    · trivial

  have hne : (classMaterials cfg .BI u₁ u₂ v₁ v₂ (1,1)).Nonempty := ⟨assign p, hmem⟩
  obtain ⟨y, hy, hm, hmin⟩ := minimumBudget_attained cfg .BI u₁ u₂ v₁ v₂ (1,1) hne
  refine ⟨?_, ⟨assign p, hmem, hb'⟩⟩
  rw [hm]
  congr 1
  exact le_antisymm ((hmin (assign p) hmem).trans hb'.le) (hlow y hy)

theorem rotation_budget_monotone (n : Axis) {Θ Θ' : ℝ}
    (hΘ : 0 ≤ Θ) (hΘπ : Θ ≤ Real.pi)
    (hΘ' : Θ ≤ Θ') (hΘ'π : Θ' ≤ Real.pi) :
    2 * Real.tan (Θ / 4) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y|
      ≤ 2 * Real.tan (Θ' / 4) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| := by
  have hx₁ : -(Real.pi / 2) < Θ / 4 := by
    have h0 : 0 ≤ Θ / 4 := div_nonneg hΘ (by norm_num)
    linarith [Real.pi_pos]
  have hx₂ : Θ' / 4 < Real.pi / 2 := by
    have h4 : Θ' / 4 ≤ Real.pi / 4 := div_le_div_of_nonneg_right hΘ'π (by norm_num)
    linarith [Real.pi_pos]
  have h4 : Θ / 4 ≤ Θ' / 4 := div_le_div_of_nonneg_right hΘ' (by norm_num)
  have htan : Real.tan (Θ / 4) ≤ Real.tan (Θ' / 4) := by
    by_cases h : Θ / 4 < Θ' / 4
    · exact le_of_lt (Real.tan_lt_tan_of_lt_of_lt_pi_div_two hx₁ hx₂ h)
    · have h4' : Θ' / 4 ≤ Θ / 4 := le_of_not_gt h
      have heq : Θ' / 4 = Θ / 4 := le_antisymm h4' h4
      rw [heq]
  have hM : 0 ≤ max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| :=
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have h1 : 2 * Real.tan (Θ / 4) ≤ 2 * Real.tan (Θ' / 4) :=
    mul_le_mul_of_nonneg_left htan (by norm_num)
  exact mul_le_mul_of_nonneg_right h1 hM

theorem rotation_capacity (n : Axis) :
    2 * Real.tan (Real.pi / 4) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y|
      = 2 * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| := by
  rw [Real.tan_pi_div_four]
  ring

private theorem mulVec_column (M U : Ten2) (j : Fin 2) :
    M *ᵥ column U j = column (M * U) j := by
  funext i
  simp [column, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]

theorem rotation_orthonormal_minimum_le (cfg : Config) (n : Axis) (Θ : ℝ)
    (hΘ : 0 ≤ Θ) (hΘπ : Θ ≤ Real.pi)
    (_hk : cfg.kPar = 0) (_heq : cfg.lower.eta = cfg.upper.eta)
    (hω : cfg.omega = 1) (hηu : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1)
    (U : Ten2) (hU : U ∈ unitary Ten2) :
    minimumBudget cfg .BI (column U 0) (column U 1)
      (column (rotationOperator n Θ * U) 0)
      (column (rotationOperator n Θ * U) 1) (1,1)
      ≤ (2 * Real.tan (Θ / 4) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| : WithTop ℝ) := by
  have hq : 0 ≤ phaseQ (rotationCoefficients n Θ) 0 := by
    have hc : 0 ≤ Real.cos (Θ / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    simpa [phaseQ, rotationCoefficients, Real.cos_zero] using hc
  obtain ⟨p, hp, hb⟩ := fixedPhase_spectral_optimum_attained_zero cfg
    (rotationCoefficients n Θ) 0 (rotationCoefficients_sphere n Θ) hq
  have hpT : biForwardT cfg p = rotationOperator n Θ := by
    rw [hp, phaseTransmission]
    simp
    exact (rotationOperator_eq_phaseMatrix n Θ).symm
  have hrotU : rotationOperator n Θ * U ∈ unitary Ten2 :=
    (unitary Ten2).mul_mem (rotationOperator_unitary n Θ).1 hU
  have hw₀ := column_normalized (rotationOperator n Θ * U) hrotU 0
  have hw₁ := column_normalized (rotationOperator n Θ * U) hrotU 1
  have hmem : assign p ∈ classMaterials cfg .BI (column U 0) (column U 1)
      (column (rotationOperator n Θ * U) 0)
      (column (rotationOperator n Θ * U) 1) (1,1) := by
    apply classMaterials_mem cfg .BI _ _ _ _ (1,1) (assign p)
    · rw [conversionMaterials_iff_conversions cfg _ _ _ _ (1,1) (assign p) hw₀ hw₁]
      refine ⟨⟨1, ?_, ?_⟩, ⟨1, ?_, ?_⟩⟩
      · rw [parameters_assign, hpT, mulVec_column]
        simp
      · exact (efficiency_eq_one_iff (1 : ℂ)).mpr (by simp)
      · rw [parameters_assign, hpT, mulVec_column]
        simp
      · exact (efficiency_eq_one_iff (1 : ℂ)).mpr (by simp)
    · trivial
  have hb' : spectralTotalBudget cfg (assign p)
      = 2 * Real.tan (Θ / 4) * max (Real.sqrt (1 - n.n_y ^ 2)) |n.n_y| :=
    hb.trans (rotation_phaseMinimum cfg n Θ hΘ hΘπ hω hηu heps hmu hc0)
  have hle := minimumBudget_le_of_mem cfg .BI _ _ _ _ (1,1) (assign p) hmem
  rwa [hb'] at hle

private theorem norm_of_smul_of_normalized (α : ℂ) (v w : Vec2)
    (hv : BIPhysicalFeasibility.isNormalizedJones v)
    (hw : BIPhysicalFeasibility.isNormalizedJones w) (h : v = α • w) :
    ‖α‖ = 1 := by
  have h1 := BIPhysicalFeasibility.jonesNormSqR_eq_one_of_normalized hv
  have h2 := BIPhysicalFeasibility.jonesNormSqR_eq_one_of_normalized hw
  have h3 : Complex.normSq α = 1 := by
    have hh : jonesNormSqR v = Complex.normSq α * jonesNormSqR w := by
      rw [h, jonesNormSqR_smul]
    rw [h1, h2] at hh
    linarith
  rw [Complex.normSq_eq_norm_sq] at h3
  nlinarith [norm_nonneg α]

theorem rotation_degenerate_minimum_zero (cfg : Config) (n : Axis) (Θ : ℝ)
    (U : Ten2) (hU : U ∈ unitary Ten2)
    (h1 : ∃ α₁ : ℂ, column U 0 = α₁ • column (rotationOperator n Θ * U) 0)
    (h2 : ∃ α₂ : ℂ, column U 1 = α₂ • column (rotationOperator n Θ * U) 1) :
    minimumBudget cfg .BI (column U 0) (column U 1)
      (column (rotationOperator n Θ * U) 0)
      (column (rotationOperator n Θ * U) 1) (1,1) = 0 := by
  have hrotU : rotationOperator n Θ * U ∈ unitary Ten2 :=
    (unitary Ten2).mul_mem (rotationOperator_unitary n Θ).1 hU
  have hw₀ := column_normalized (rotationOperator n Θ * U) hrotU 0
  have hw₁ := column_normalized (rotationOperator n Θ * U) hrotU 1
  have hu₀ := column_normalized U hU 0
  have hu₁ := column_normalized U hU 1
  obtain ⟨α₁, hα₁⟩ := h1
  obtain ⟨α₂, hα₂⟩ := h2
  have hn₁ : ‖α₁‖ = 1 :=
    norm_of_smul_of_normalized α₁ (column U 0) (column (rotationOperator n Θ * U) 0)
      hu₀ hw₀ hα₁
  have hn₂ : ‖α₂‖ = 1 :=
    norm_of_smul_of_normalized α₂ (column U 1) (column (rotationOperator n Θ * U) 1)
      hu₁ hw₁ hα₂
  have hmem : assign biZeroParams ∈ classMaterials cfg .BI (column U 0) (column U 1)
      (column (rotationOperator n Θ * U) 0)
      (column (rotationOperator n Θ * U) 1) (1,1) := by
    apply classMaterials_mem cfg .BI _ _ _ _ (1,1) (assign biZeroParams)
    · rw [conversionMaterials_iff_conversions cfg _ _ _ _ (1,1) (assign biZeroParams) hw₀ hw₁]
      refine ⟨⟨α₁, ?_, ?_⟩, ⟨α₂, ?_, ?_⟩⟩
      · rw [parameters_assign, biForwardT_zero, Matrix.one_mulVec]
        exact hα₁
      · exact (efficiency_eq_one_iff α₁).mpr hn₁
      · rw [parameters_assign, biForwardT_zero, Matrix.one_mulVec]
        exact hα₂
      · exact (efficiency_eq_one_iff α₂).mpr hn₂
    · rw [parameters_assign]
      exact zero_params_in_all_classes .BI
  have hz : assign biZeroParams = 0 := by
    have hbi : biZeroParams = parameters 0 := by simp [biZeroParams, parameters]
    rw [hbi, assign_parameters]
  have hb : spectralTotalBudget cfg (assign biZeroParams) = 0 :=
    (spectralTotalBudget_eq_zero_iff cfg (freeSpaceK0_pos cfg) (assign biZeroParams)).mpr hz
  have hle := minimumBudget_le_of_mem cfg .BI _ _ _ _ (1,1) (assign biZeroParams) hmem
  have hne : (classMaterials cfg .BI (column U 0) (column U 1)
      (column (rotationOperator n Θ * U) 0)
      (column (rotationOperator n Θ * U) 1) (1,1)).Nonempty :=
    ⟨assign biZeroParams, hmem⟩
  obtain ⟨x, hx, hm, _⟩ := minimumBudget_attained cfg .BI _ _ _ _ (1,1) hne
  rw [hm] at hle
  rw [hb] at hle
  rw [hm]
  exact le_antisymm hle (WithTop.coe_le_coe.mpr (spectralTotalBudget_nonneg cfg x))

end GSTC.Scattering.UnitaryRotationCapacity
