/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.

Licensed under the MIT License.

Part of the GSTC formalization of the manuscript
`rshegde/paper-gstc_arbpol_bounds`, Section 3B.1.
-/
module

public import GSTC.Scattering.OrthogonalSpectralBridge

public section
set_option autoImplicit false

namespace GSTC.Scattering
namespace OrthogonalSpectralOptimum

open scoped Matrix
open BIUnitaryTransmission
open BIRankOneCompletion
open OrthogonalSpectralBridge
open BIFeasibility
open ClassFeasibility
open SusceptibilityBudget
open MaterialSpace
open BIPolynomials

theorem abs_cos_add_le (q α : ℝ) : |Real.cos α + q| ≤ 1 + |q| := by
  have h1 : |Real.cos α + q| ≤ |Real.cos α| + |q| := by
    rw [abs_le]
    constructor
    · have h2 := neg_abs_le (Real.cos α)
      have h3 := neg_abs_le q
      linarith
    · have h2 := le_abs_self (Real.cos α)
      have h3 := le_abs_self q
      linarith
  have h2 := Real.abs_cos_le_one α
  linarith

theorem phaseCayleyScale_zero (c : PhaseCoefficients) (t : ℝ) :
    phaseCayleyScale c t 0 = 1 + phaseQ c t := by
  simp [phaseCayleyScale, Real.cos_zero]

theorem phaseCayleyScale_pi (c : PhaseCoefficients) (t : ℝ) :
    phaseCayleyScale c t Real.pi = phaseQ c t - 1 := by
  simp [phaseCayleyScale, Real.cos_pi]
  ring

theorem budget_core (K M₀ M₁ D Q : ℝ)
    (hK : 0 ≤ K) (hD : D ≤ Q) (hDpos : 0 < D) (hQpos : 0 < Q)
    (hM : M₀ ≤ M₁) (hM₁ : 0 ≤ M₁) :
    K * M₀ / Q ≤ K / D * M₁ := by
  have hKM : K * M₀ ≤ K * M₁ := mul_le_mul_of_nonneg_left hM hK
  have hcore : (K * M₀) * D ≤ (K * M₁) * Q := by
    calc (K * M₀) * D ≤ (K * M₁) * D := mul_le_mul_of_nonneg_right hKM hDpos.le
      _ ≤ (K * M₁) * Q := mul_le_mul_of_nonneg_left hD (mul_nonneg hK hM₁)
  have hdiv : (K * M₀) / Q ≤ (K * M₁) / D :=
    (div_le_div_iff₀ hQpos hDpos).mpr hcore
  simpa only [div_mul_eq_mul_div] using hdiv

theorem phaseBudget_lower_bound (cfg : Config) (c : PhaseCoefficients) (t α : ℝ)
    (hα : phaseCayleyScale c t α ≠ 0) :
    phaseMinimum cfg c t
      ≤ freeSpaceK0 cfg * 2 / |phaseCayleyScale c t α| *
          max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
                * (Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) + |Real.sin α|))
            (spectralChiralScale cfg * |phaseRy c t|) := by
  have hω : 0 < cfg.omega := cfg.omega_pos
  have hη : 0 < cfg.upper.eta := cfg.upper.eta_pos
  have heps : 0 < cfg.vac.eps0 := cfg.vac.eps0_pos
  have hmu : 0 < cfg.vac.mu0 := cfg.vac.mu0_pos
  have hc0 : 0 < cfg.vac.c0 := cfg.vac.c0_pos
  have hE : 0 ≤ spectralElectricScale cfg := by
    unfold spectralElectricScale
    positivity
  have hM : 0 ≤ spectralMagneticScale cfg := by
    unfold spectralMagneticScale
    positivity
  have hG : 0 ≤ spectralChiralScale cfg := by
    unfold spectralChiralScale
    positivity
  have hK : 0 ≤ freeSpaceK0 cfg := freeSpaceK0_nonneg cfg
  have hsin : 0 ≤ |Real.sin α| := abs_nonneg _
  have hS : 0 ≤ Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) := Real.sqrt_nonneg _
  have hA : 0 ≤ max (spectralElectricScale cfg) (spectralMagneticScale cfg) :=
    le_max_iff.mpr (Or.inl hE)
  have hGc : 0 ≤ spectralChiralScale cfg * |phaseRy c t| :=
    mul_nonneg hG (abs_nonneg _)
  have hM1 : 0 ≤ max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
      * (Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) + |Real.sin α|))
      (spectralChiralScale cfg * |phaseRy c t|) :=
    le_max_iff.mpr (Or.inl (mul_nonneg hA (le_trans hS (le_add_of_nonneg_right hsin))))
  have hmax : max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
      * Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2))
      (spectralChiralScale cfg * |phaseRy c t|)
      ≤ max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
          * (Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) + |Real.sin α|))
        (spectralChiralScale cfg * |phaseRy c t|) := by
    refine max_le_iff.mpr ⟨le_max_iff.mpr (Or.inl ?_), le_max_iff.mpr (Or.inr le_rfl)⟩
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hsin) hA
  have hDle : |phaseCayleyScale c t α| ≤ 1 + |phaseQ c t| :=
    abs_cos_add_le (phaseQ c t) α
  have hDpos : 0 < |phaseCayleyScale c t α| := abs_pos.mpr hα
  have hQpos : 0 < 1 + |phaseQ c t| := by positivity
  have hcore := budget_core (freeSpaceK0 cfg * 2)
    (max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
        * Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2))
      (spectralChiralScale cfg * |phaseRy c t|))
    (max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
        * (Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) + |Real.sin α|))
      (spectralChiralScale cfg * |phaseRy c t|))
    |phaseCayleyScale c t α| (1 + |phaseQ c t|)
    (by positivity) hDle hDpos hQpos hmax hM1
  unfold phaseMinimum
  have hstep : (freeSpaceK0 cfg * 2
      * max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
          * Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2))
        (spectralChiralScale cfg * |phaseRy c t|)) / (1 + |phaseQ c t|)
      ≤ freeSpaceK0 cfg * 2 / |phaseCayleyScale c t α| *
          max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
                * (Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) + |Real.sin α|))
            (spectralChiralScale cfg * |phaseRy c t|) := by
    simpa only [div_mul_eq_mul_div] using hcore
  exact hstep

theorem phaseBudget_attained_zero (cfg : Config) (c : PhaseCoefficients) (t : ℝ)
    (hq : 0 ≤ phaseQ c t) :
    spectralTotalBudget cfg (assign (phaseSheet cfg c t 0)) = phaseMinimum cfg c t := by
  have hα : phaseCayleyScale c t 0 ≠ 0 := by
    rw [phaseCayleyScale_zero]
    have : (0 : ℝ) < 1 + phaseQ c t := by linarith
    exact ne_of_gt this
  have h := phaseSheetBudget cfg c t 0 hα
  rw [h, phaseCayleyScale_zero]
  have habs : |(1 : ℝ) + phaseQ c t| = 1 + |phaseQ c t| := by
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hq]
  rw [habs]
  unfold phaseMinimum
  simp only [Real.sin_zero, abs_zero, add_zero]
  ring

theorem phaseBudget_attained_pi (cfg : Config) (c : PhaseCoefficients) (t : ℝ)
    (hq : phaseQ c t < 0) :
    spectralTotalBudget cfg (assign (phaseSheet cfg c t Real.pi))
      = phaseMinimum cfg c t := by
  have hα : phaseCayleyScale c t Real.pi ≠ 0 := by
    rw [phaseCayleyScale_pi]
    have : (phaseQ c t - 1 : ℝ) < 0 := by linarith
    exact ne_of_lt this
  have h := phaseSheetBudget cfg c t Real.pi hα
  rw [h, phaseCayleyScale_pi]
  have habs : |phaseQ c t - 1| = 1 + |phaseQ c t| := by
    rw [abs_of_neg (by linarith), abs_of_neg hq]
    ring
  rw [habs]
  unfold phaseMinimum
  simp only [Real.sin_pi, abs_zero, add_zero]
  ring

theorem fixedPhase_spectral_optimum (cfg : Config) (c : PhaseCoefficients) (t α : ℝ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1)
    (hα : phaseCayleyScale c t α ≠ 0)
    (p : BIParams) (hp : biForwardT cfg p = phaseTransmission c t α) :
    phaseMinimum cfg c t ≤ spectralTotalBudget cfg (assign p) := by
  have hb := budget_of_prescribed_phaseTransmission cfg c t α p hk heq hsphere hα hp
  rw [hb]
  exact phaseBudget_lower_bound cfg c t α hα

theorem fixedPhase_spectral_optimum_attained_zero (cfg : Config)
    (c : PhaseCoefficients) (t : ℝ)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1)
    (hq : 0 ≤ phaseQ c t) :
    ∃ p : BIParams, biForwardT cfg p = phaseTransmission c t 0 ∧
      spectralTotalBudget cfg (assign p) = phaseMinimum cfg c t := by
  have hα : phaseCayleyScale c t 0 ≠ 0 := by
    rw [phaseCayleyScale_zero]
    have : (0 : ℝ) < 1 + phaseQ c t := by linarith
    exact ne_of_gt this
  exact ⟨phaseSheet cfg c t 0, phaseSheet_forward cfg c t 0 hsphere hα,
    phaseBudget_attained_zero cfg c t hq⟩

theorem fixedPhase_spectral_optimum_attained_pi (cfg : Config)
    (c : PhaseCoefficients) (t : ℝ)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1)
    (hq : phaseQ c t < 0) :
    ∃ p : BIParams, biForwardT cfg p = phaseTransmission c t Real.pi ∧
      spectralTotalBudget cfg (assign p) = phaseMinimum cfg c t := by
  have hα : phaseCayleyScale c t Real.pi ≠ 0 := by
    rw [phaseCayleyScale_pi]
    have : (phaseQ c t - 1 : ℝ) < 0 := by linarith
    exact ne_of_lt this
  exact ⟨phaseSheet cfg c t Real.pi, phaseSheet_forward cfg c t Real.pi hsphere hα,
    phaseBudget_attained_pi cfg c t hq⟩

end OrthogonalSpectralOptimum
end GSTC.Scattering
