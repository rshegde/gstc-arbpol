/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.JonesFrameSpectralMinimum
public import GSTC.Scattering.OrthogonalSpectralMinimum
public import GSTC.Scattering.PauliRepresentation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

public section
set_option autoImplicit false
namespace GSTC.Scattering.LinearRotationSpectralMinimum

open Matrix PauliRepresentation JonesFrameCorrespondence OrthogonalSpectralPhase
open ClassFeasibility ClassMinimumBudget SusceptibilityBudget BIFeasibility
open BIPolynomials MaterialSpace
open scoped Matrix

@[expose] noncomputable def linearRotation (θ : ℝ) : Ten2 :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem linearRotation_eq_pauliForm (θ : ℝ) :
    linearRotation θ = pauliForm (Real.cos θ) 0 (-Real.sin θ) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
      simp [linearRotation, pauliForm, sigmaX, sigmaY, sigmaZ,
        Matrix.smul_apply, Matrix.add_apply]

theorem linearRotation_unitary (θ : ℝ) : linearRotation θ ∈ unitary Ten2 := by
  rw [linearRotation_eq_pauliForm]
  exact (pauliForm_special_unitary (Real.cos θ) 0 (-Real.sin θ) 0
    (by nlinarith [Real.cos_sq_add_sin_sq θ])).1

theorem linearRotation_det (θ : ℝ) : (linearRotation θ).det = 1 := by
  rw [linearRotation_eq_pauliForm]
  exact (pauliForm_special_unitary (Real.cos θ) 0 (-Real.sin θ) 0
    (by nlinarith [Real.cos_sq_add_sin_sq θ])).2

theorem base_linearRotation (θ : ℝ) :
    base (1 : Ten2) (linearRotation θ) 1 = linearRotation θ := by
  simp [base, one_smul, Matrix.conjTranspose_one]

theorem tangent_linearRotation (θ : ℝ) :
    tangent (1 : Ten2) (linearRotation θ) 1 = linearRotation θ * generator := by
  simp [tangent, one_smul, Matrix.conjTranspose_one]

theorem mul_generator_eq_pauliForm (θ : ℝ) :
    linearRotation θ * generator = pauliForm 0 (Real.sin θ) 0 (Real.cos θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
      simp [linearRotation, generator, pauliForm, sigmaX, sigmaY, sigmaZ,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]

theorem coordinates_linearRotation (θ : ℝ) :
    coordinates (linearRotation θ) = ![Real.cos θ, 0, -Real.sin θ, 0] := by
  rw [linearRotation_eq_pauliForm, coordinates_pauliForm]

theorem coordinates_mul_generator (θ : ℝ) :
    coordinates (linearRotation θ * generator) = ![0, Real.sin θ, 0, Real.cos θ] := by
  rw [mul_generator_eq_pauliForm, coordinates_pauliForm]

@[expose] noncomputable def rotCoeffs (θ : ℝ) : PhaseCoefficients :=
  ⟨Real.cos θ, 0, -Real.sin θ, 0, 0, Real.sin θ, 0, Real.cos θ⟩

theorem rotCoeffs_eq (θ : ℝ) :
    rotCoeffs θ = ⟨Real.cos θ, 0, -Real.sin θ, 0, 0, Real.sin θ, 0, Real.cos θ⟩ := rfl

theorem frameCoefficients_linearRotation (θ : ℝ) :
    frameCoefficients (1 : Ten2) (linearRotation θ) 1 = rotCoeffs θ := by
  simp only [frameCoefficients]
  rw [base_linearRotation, tangent_linearRotation,
    coordinates_linearRotation, coordinates_mul_generator]
  rfl

theorem phaseQ_linearRotation (θ t : ℝ) :
    phaseQ (rotCoeffs θ) t = Real.cos θ * Real.cos t := by
  simp [phaseQ, rotCoeffs]

theorem phaseRx_linearRotation (θ t : ℝ) :
    phaseRx (rotCoeffs θ) t = Real.sin θ * Real.sin t := by
  simp [phaseRx, rotCoeffs]

theorem phaseRy_linearRotation (θ t : ℝ) :
    phaseRy (rotCoeffs θ) t = -Real.sin θ * Real.cos t := by
  simp [phaseRy, rotCoeffs]

theorem phaseRz_linearRotation (θ t : ℝ) :
    phaseRz (rotCoeffs θ) t = Real.cos θ * Real.sin t := by
  simp [phaseRz, rotCoeffs]

theorem phaseMinimum_linearRotation (cfg : Config) (θ t : ℝ)
    (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    phaseMinimum cfg (frameCoefficients (1 : Ten2) (linearRotation θ) 1) t
      = freeSpaceK0 cfg * 2 *
        max
          (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
            * |Real.sin t|)
          (spectralChiralScale cfg * Real.sin θ * |Real.cos t|)
        / (1 + Real.cos θ * |Real.cos t|) := by
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  unfold phaseMinimum
  rw [frameCoefficients_linearRotation, phaseRx_linearRotation,
    phaseRz_linearRotation, phaseRy_linearRotation, phaseQ_linearRotation]
  have hs : (Real.sin θ * Real.sin t) ^ 2 + (Real.cos θ * Real.sin t) ^ 2
      = (Real.sin t) ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  have hry : |-Real.sin θ * Real.cos t| = Real.sin θ * |Real.cos t| := by
    rw [abs_mul, abs_neg, abs_of_nonneg (le_of_lt hsin)]
  have hq : |Real.cos θ * Real.cos t| = Real.cos θ * |Real.cos t| := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hcos)]
  rw [hs, Real.sqrt_sq_eq_abs, hry, hq]
  simp [mul_assoc]

@[expose] noncomputable def rotationBudget (θ t : ℝ) : ℝ :=
  2 * max |Real.sin t| (Real.sin θ * |Real.cos t|)
    / (1 + Real.cos θ * |Real.cos t|)

theorem phaseMinimum_linearRotation_freeSpace (cfg : Config) (θ t : ℝ)
    (hω : cfg.omega = 1) (hη : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1)
    (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    phaseMinimum cfg (frameCoefficients (1 : Ten2) (linearRotation θ) 1) t
      = rotationBudget θ t := by
  rw [phaseMinimum_linearRotation cfg θ t hθ hθ']
  simp [rotationBudget, freeSpaceK0, spectralElectricScale,
    spectralMagneticScale, spectralChiralScale, hω, hη, heps, hmu, hc0]

@[expose] noncomputable def rotationOptimumPhase (θ : ℝ) : ℝ := Real.arctan (Real.sin θ)

@[expose] noncomputable def rotationBudgetMin (θ : ℝ) : ℝ :=
  2 * Real.sin θ / (Real.sqrt (1 + (Real.sin θ)^2) + Real.cos θ)

theorem abs_sin_cos_sq (t : ℝ) : |Real.cos t| ^ 2 + |Real.sin t| ^ 2 = 1 := by
  rw [sq_abs, sq_abs, Real.cos_sq_add_sin_sq]

theorem rotationBudget_le_of_unit (θ u v : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u ^ 2 + v ^ 2 = 1) :
    max v (Real.sin θ * u) * (Real.sqrt (1 + (Real.sin θ)^2) + Real.cos θ)
      ≥ Real.sin θ * (1 + Real.cos θ * u) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith)
  have hs0 : 0 ≤ Real.sin θ := le_of_lt hs
  have hc0 : 0 ≤ Real.cos θ := le_of_lt hc
  have hs2 : 0 ≤ (Real.sin θ)^2 := sq_nonneg _
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  set D := Real.sqrt (1 + (Real.sin θ)^2) with hD
  have hDpos : 0 < D :=
    Real.sqrt_pos_of_pos (by nlinarith [sq_nonneg (Real.sin θ)])
  have hD2 : D ^ 2 = 1 + (Real.sin θ)^2 := by
    have h := Real.sq_sqrt (show 0 ≤ 1 + (Real.sin θ)^2 by
      nlinarith [sq_nonneg (Real.sin θ)])
    simpa [hD] using h
  by_cases hA : v ≥ Real.sin θ * u
  ·
    have hmax : max v (Real.sin θ * u) = v := max_eq_left hA
    have hsq : v ^ 2 ≥ (Real.sin θ * u) ^ 2 := by
      have h := mul_le_mul_of_nonneg hA hA (mul_nonneg hs0 hu) hv
      linarith [h]
    have h1 : (u * D) ^ 2 ≤ 1 := by nlinarith [hsq, huv, hD2]
    have h2 : u * D ≤ 1 := by nlinarith [h1, mul_nonneg hu (le_of_lt hDpos)]
    have h4 : v ^ 2 + (Real.sin θ)^2 * v ^ 2 ≥ (Real.sin θ)^2 := by
      nlinarith [hsq, huv, hs2]
    have h5 : (v * D) ^ 2 ≥ (Real.sin θ)^2 := by nlinarith [h4, hD2]
    have h6 : 0 ≤ v * D := mul_nonneg hv (le_of_lt hDpos)
    have h3 : v * D ≥ Real.sin θ := by nlinarith [h5, h6, hs0]
    rw [hmax]
    nlinarith [h3, hA, hc0]
  ·
    have hA' : v ≤ Real.sin θ * u := le_of_not_ge hA
    have hmax : max v (Real.sin θ * u) = Real.sin θ * u := max_eq_right hA'
    have hsq : v ^ 2 ≤ (Real.sin θ * u) ^ 2 := by
      have h := mul_le_mul_of_nonneg hA' hA' hv (mul_nonneg hs0 hu)
      linarith [h]
    have h1 : (u * D) ^ 2 ≥ 1 := by nlinarith [hsq, huv, hD2]
    have h2 : u * D ≥ 1 := by nlinarith [h1, mul_nonneg hu (le_of_lt hDpos)]
    rw [hmax]
    nlinarith [h2, hs0]

theorem rotationBudget_le (θ t : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    rotationBudget θ t ≥ rotationBudgetMin θ := by
  have h := rotationBudget_le_of_unit θ |Real.cos t| |Real.sin t| hθ hθ'
    (abs_nonneg _) (abs_nonneg _) (abs_sin_cos_sq t)
  have hden : 0 < 1 + Real.cos θ * |Real.cos t| := by
    have hc : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith)
    have ha : 0 ≤ |Real.cos t| := abs_nonneg _
    have hm : 0 ≤ Real.cos θ * |Real.cos t| := mul_nonneg (le_of_lt hc) ha
    linarith
  have hDpos : 0 < Real.sqrt (1 + (Real.sin θ)^2) + Real.cos θ := by
    have h1 : 0 < Real.sqrt (1 + (Real.sin θ)^2) :=
      Real.sqrt_pos_of_pos (by nlinarith [sq_nonneg (Real.sin θ)])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith)
    linarith
  have h2 : 2 * Real.sin θ * (1 + Real.cos θ * |Real.cos t|)
      ≤ 2 * max |Real.sin t| (Real.sin θ * |Real.cos t|)
        * (Real.sqrt (1 + (Real.sin θ)^2) + Real.cos θ) := by linarith [h]
  have h3 := (div_le_div_iff₀ hDpos hden).mpr h2
  unfold rotationBudget rotationBudgetMin
  exact h3

theorem rotationBudget_eq_optimum (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    rotationBudget θ (rotationOptimumPhase θ) = rotationBudgetMin θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  have hDpos : 0 < Real.sqrt (1 + (Real.sin θ)^2) :=
    Real.sqrt_pos_of_pos (by nlinarith [sq_nonneg (Real.sin θ)])
  unfold rotationBudget rotationBudgetMin rotationOptimumPhase
  rw [Real.cos_arctan, Real.sin_arctan]
  have h1 : |1 / Real.sqrt (1 + (Real.sin θ)^2)|
      = 1 / Real.sqrt (1 + (Real.sin θ)^2) := abs_of_pos (by positivity)
  have h2 : |Real.sin θ / Real.sqrt (1 + (Real.sin θ)^2)|
      = Real.sin θ / Real.sqrt (1 + (Real.sin θ)^2) :=
    abs_of_pos (by positivity)
  rw [h1, h2]
  have heq : Real.sin θ * (1 / Real.sqrt (1 + (Real.sin θ)^2))
      = Real.sin θ / Real.sqrt (1 + (Real.sin θ)^2) := by
    have hone : (1 : ℝ) / Real.sqrt (1 + (Real.sin θ)^2)
        = (Real.sqrt (1 + (Real.sin θ)^2))⁻¹ := by
      rw [div_eq_mul_inv, one_mul]
    rw [hone, div_eq_mul_inv]
  rw [heq, max_self]
  have hne : Real.sqrt (1 + (Real.sin θ)^2) ≠ 0 := ne_of_gt hDpos
  field_simp

theorem rotationBudget_zero_angle : rotationBudget 0 0 = 0 := by
  simp [rotationBudget]

theorem rotationBudget_right_angle :
    rotationBudget (Real.pi / 2) (Real.pi / 2) = 2 := by
  simp [rotationBudget]

theorem rotationBudget_eq_of_abs (θ t u : ℝ)
    (hsin : |Real.sin t| = |Real.sin u|)
    (hcos : |Real.cos t| = |Real.cos u|) :
    rotationBudget θ t = rotationBudget θ u := by
  unfold rotationBudget
  rw [hsin, hcos]

theorem exists_rotationPhase_quarter (θ t : ℝ) :
    ∃ u ∈ Set.Icc 0 (Real.pi / 2), rotationBudget θ u = rotationBudget θ t := by
  refine ⟨Real.arcsin |Real.sin t|, ⟨?_, ?_⟩, ?_⟩
  · exact (Real.arcsin_nonneg (x := |Real.sin t|)).mpr (abs_nonneg (Real.sin t))
  · exact Real.arcsin_le_pi_div_two _
  · have h1 : |Real.sin t| = |Real.sin (Real.arcsin |Real.sin t|)| := by
      have h := Real.sin_arcsin (by linarith [abs_nonneg (Real.sin t)])
        (by linarith [Real.abs_sin_le_one t])
      rw [h]
      exact (abs_of_nonneg (abs_nonneg (Real.sin t))).symm
    have h2 : |Real.cos t| = |Real.cos (Real.arcsin |Real.sin t|)| := by
      rw [Real.cos_arcsin]
      have h : Real.sqrt (1 - |Real.sin t| ^ 2) = |Real.cos t| := by
        have h1 : 1 - |Real.sin t| ^ 2 = Real.cos t ^ 2 := by
          rw [sq_abs]
          nlinarith [Real.sin_sq_add_cos_sq t]
        rw [h1, Real.sqrt_sq_eq_abs]
      rw [h]
      exact (abs_of_nonneg (abs_nonneg (Real.cos t))).symm
    exact (rotationBudget_eq_of_abs θ t (Real.arcsin |Real.sin t|) h1 h2).symm

theorem rotationOptimumPhase_mem_quarter (θ : ℝ)
    (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    rotationOptimumPhase θ ∈ Set.Icc 0 (Real.pi / 2) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  have h1 : 0 ≤ rotationOptimumPhase θ := by
    unfold rotationOptimumPhase
    exact (Real.arctan_nonneg).mpr (le_of_lt hsin)
  have h2 : rotationOptimumPhase θ ≤ Real.pi / 2 := by
    unfold rotationOptimumPhase
    exact (Real.arctan_lt_pi_div_two _).le
  exact ⟨h1, h2⟩

theorem phaseRy_linearRotation_zero_iff (θ t : ℝ) (hθ : 0 < θ)
    (hθ' : θ < Real.pi / 2) :
    phaseRy (frameCoefficients (1 : Ten2) (linearRotation θ) 1) t = 0
      ↔ Real.cos t = 0 := by
  rw [frameCoefficients_linearRotation, phaseRy_linearRotation]
  constructor
  · intro h
    have hne : -Real.sin θ ≠ 0 := by
      rw [neg_ne_zero]
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith))
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 hne
    · exact h2
  · intro h
    simp [h]

theorem nbAdmissible_linearRotation (θ t : ℝ) (hθ : 0 < θ)
    (hθ' : θ < Real.pi / 2) :
    nbAdmissible (frameCoefficients (1 : Ten2) (linearRotation θ) 1) t
      ↔ Real.cos t = 0 := by
  simp only [nbAdmissible]
  exact phaseRy_linearRotation_zero_iff θ t hθ hθ'

theorem rotationBudget_eq_two_of_cos_zero (θ t : ℝ) (ht : Real.cos t = 0) :
    rotationBudget θ t = 2 := by
  have hsin1 : |Real.sin t| = 1 := by
    have h2 : Real.sin t ^ 2 = 1 := by
      have h := Real.sin_sq_add_cos_sq t
      rw [ht] at h
      nlinarith [h]
    have habs : |Real.sin t| ^ 2 = 1 := by rw [sq_abs, h2]
    have hnonneg : 0 ≤ |Real.sin t| := abs_nonneg _
    nlinarith
  unfold rotationBudget
  rw [hsin1, ht, abs_zero]
  simp only [mul_zero, add_zero]
  rw [max_eq_left (by norm_num)]
  norm_num

theorem one_mem_unitary : (1 : Ten2) ∈ unitary Ten2 := by
  simp

theorem phaseMinimum_le_optimum (cfg : Config) (θ : ℝ)
    (hω : cfg.omega = 1) (hη : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1)
    (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    ∀ t, phaseMinimum cfg (frameCoefficients (1 : Ten2) (linearRotation θ) 1)
      (rotationOptimumPhase θ)
      ≤ phaseMinimum cfg (frameCoefficients (1 : Ten2) (linearRotation θ) 1) t := by
  intro t
  rw [phaseMinimum_linearRotation_freeSpace cfg θ _ hω hη heps hmu hc0 hθ hθ',
    phaseMinimum_linearRotation_freeSpace cfg θ _ hω hη heps hmu hc0 hθ hθ']
  rw [rotationBudget_eq_optimum θ hθ hθ']
  exact rotationBudget_le θ t hθ hθ'

theorem biMinimum_linearRotation (cfg : Config) (θ : ℝ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hω : cfg.omega = 1) (hη : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1)
    (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    minimumBudget cfg .BI (column (1 : Ten2) 0) (column (1 : Ten2) 1)
      (column (linearRotation θ) 0) (column (linearRotation θ) 1) (1,1)
      = (2 * Real.sin θ / (Real.sqrt (1 + (Real.sin θ)^2) + Real.cos θ) : WithTop ℝ)
    ∧ ∃ p : BIParams,
        assign p ∈ classMaterials cfg .BI (column (1 : Ten2) 0)
          (column (1 : Ten2) 1) (column (linearRotation θ) 0)
          (column (linearRotation θ) 1) (1,1)
        ∧ spectralTotalBudget cfg (assign p)
          = 2 * Real.sin θ / (Real.sqrt (1 + (Real.sin θ)^2) + Real.cos θ) := by
  have hval : phaseMinimum cfg (frameCoefficients (1 : Ten2) (linearRotation θ) 1)
      (rotationOptimumPhase θ)
      = 2 * Real.sin θ / (Real.sqrt (1 + (Real.sin θ)^2) + Real.cos θ) := by
    rw [phaseMinimum_linearRotation_freeSpace cfg θ _ hω hη heps hmu hc0 hθ hθ']
    exact rotationBudget_eq_optimum θ hθ hθ'
  obtain ⟨hb, hp⟩ := JonesFrameSpectralMinimum.bi_minimum_eq cfg (1 : Ten2)
    (linearRotation θ) 1 hk heq one_mem_unitary (linearRotation_unitary θ) (by simp)
    (by rw [base_linearRotation]; exact linearRotation_det θ)
    (rotationOptimumPhase θ)
    (phaseMinimum_le_optimum cfg θ hω hη heps hmu hc0 hθ hθ')
  rw [hval] at hb
  obtain ⟨p, hp1, hp2⟩ := hp
  rw [hval] at hp2
  exact ⟨hb, p, hp1, hp2⟩

theorem nbMinimum_linearRotation (cfg : Config) (θ : ℝ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hω : cfg.omega = 1) (hη : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1)
    (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    minimumBudget cfg .NB (column (1 : Ten2) 0) (column (1 : Ten2) 1)
      (column (linearRotation θ) 0) (column (linearRotation θ) 1) (1,1)
      = (2 : WithTop ℝ)
    ∧ ∃ p : BIParams,
        NoCoupling p ∧
        assign p ∈ classMaterials cfg .NB (column (1 : Ten2) 0)
          (column (1 : Ten2) 1) (column (linearRotation θ) 0)
          (column (linearRotation θ) 1) (1,1)
        ∧ spectralTotalBudget cfg (assign p) = 2 := by
  have hval : phaseMinimum cfg (frameCoefficients (1 : Ten2) (linearRotation θ) 1)
      (Real.pi / 2) = 2 := by
    rw [phaseMinimum_linearRotation_freeSpace cfg θ _ hω hη heps hmu hc0 hθ hθ']
    exact rotationBudget_eq_two_of_cos_zero θ (Real.pi / 2) (by rw [Real.cos_pi_div_two])
  obtain ⟨hb, hp⟩ := JonesFrameSpectralMinimum.nb_minimum_eq cfg (1 : Ten2)
    (linearRotation θ) 1 hk heq one_mem_unitary (linearRotation_unitary θ) (by simp)
    (by rw [base_linearRotation]; exact linearRotation_det θ)
    (Real.pi / 2)
    ((nbAdmissible_linearRotation θ (Real.pi / 2) hθ hθ').mpr (by rw [Real.cos_pi_div_two]))
    (fun t ht => by
      rw [phaseMinimum_linearRotation_freeSpace cfg θ _ hω hη heps hmu hc0 hθ hθ',
        phaseMinimum_linearRotation_freeSpace cfg θ _ hω hη heps hmu hc0 hθ hθ']
      have hcos : Real.cos t = 0 := (nbAdmissible_linearRotation θ t hθ hθ').mp ht
      rw [rotationBudget_eq_two_of_cos_zero θ (Real.pi / 2) (by rw [Real.cos_pi_div_two]),
        rotationBudget_eq_two_of_cos_zero θ t hcos])
  rw [hval] at hb
  obtain ⟨p, hp1, hp2⟩ := hp
  rw [hval] at hp2
  have hnc : NoCoupling p := by
    have hcls := (mem_classMaterials_iff cfg .NB (column (1 : Ten2) 0)
      (column (1 : Ten2) 1) (column (linearRotation θ) 0)
      (column (linearRotation θ) 1) (1,1) (assign p)).mp hp1
    rw [parameters_assign] at hcls
    exact hcls.2
  exact ⟨hb, p, hnc, hp1, hp2⟩

theorem biMinimum_linearRotation_thirty (cfg : Config)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hω : cfg.omega = 1) (hη : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1) :
    minimumBudget cfg .BI (column (1 : Ten2) 0) (column (1 : Ten2) 1)
      (column (linearRotation (Real.pi / 6)) 0)
      (column (linearRotation (Real.pi / 6)) 1) (1,1)
      = ((2 : ℝ) / (Real.sqrt 5 + Real.sqrt 3) : WithTop ℝ) := by
  obtain ⟨hb, _⟩ := biMinimum_linearRotation cfg (Real.pi / 6) hk heq
    hω hη heps hmu hc0
    (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 6))
    (by rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 6)]; linarith [Real.pi_pos])
  have hreal : 2 * Real.sin (Real.pi / 6) /
      (Real.sqrt (1 + (Real.sin (Real.pi / 6))^2) + Real.cos (Real.pi / 6))
      = (2 : ℝ) / (Real.sqrt 5 + Real.sqrt 3) := by
    rw [Real.sin_pi_div_six, Real.cos_pi_div_six]
    have h5 : Real.sqrt (1 + (1 / 2)^2) = Real.sqrt 5 / 2 := by
      have hpos : 0 ≤ Real.sqrt 5 / 2 := by positivity
      have heq : 1 + (1 / 2)^2 = (Real.sqrt 5 / 2)^2 := by
        rw [show (1 / 2 : ℝ)^2 = (1 : ℝ) / 4 by norm_num, div_pow,
          Real.sq_sqrt (by norm_num)]
        field_simp
        ring
      rw [heq, Real.sqrt_sq_eq_abs, abs_of_nonneg hpos]
    rw [h5]
    have hne1 : Real.sqrt 5 / 2 + Real.sqrt 3 / 2 ≠ 0 := by positivity
    have hne2 : Real.sqrt 5 + Real.sqrt 3 ≠ 0 := by positivity
    field_simp [hne1, hne2]
  rw [hb, hreal]

end GSTC.Scattering.LinearRotationSpectralMinimum
