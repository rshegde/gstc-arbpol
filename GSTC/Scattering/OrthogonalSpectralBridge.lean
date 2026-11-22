/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIUnitaryTransmission
public import GSTC.Scattering.OrthogonalSpectralMinimum

public section
set_option autoImplicit false
namespace GSTC.Scattering.OrthogonalSpectralBridge
open Matrix BIInverse BIFeasibility BIPolynomials MaterialSpace SusceptibilityBudget
open BIUnitaryTransmission BIRankOneCompletion ClassFeasibility
open scoped Matrix

theorem phaseMatrix_unitary (c : PhaseCoefficients) (t : ℝ)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1) :
    (phaseMatrix c t).conjTranspose * phaseMatrix c t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [phaseMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.mul_re, Complex.mul_im] <;> nlinarith only [hsphere]

theorem phaseTransmission_unitary (c : PhaseCoefficients) (t α : ℝ)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1) :
    (phaseTransmission c t α).conjTranspose * phaseTransmission c t α = 1 := by
  have hz : star ((Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ)) *
      ((Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ)) = 1 := by
    have hcircle := Real.sin_sq_add_cos_sq α
    generalize hcos : Real.cos α = ca at hcircle ⊢
    generalize hsin : Real.sin α = sa at hcircle ⊢
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> nlinarith only [hcircle]
  rw [phaseTransmission_eq, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, phaseMatrix_unitary c t hsphere, smul_smul, hz, one_smul]

theorem phaseSheet_response (cfg : Config) (c : PhaseCoefficients) (t α : ℝ)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1)
    (hα : phaseCayleyScale c t α ≠ 0) :
    biPowerResponse4 cfg (phaseSheet cfg c t α) = completion (phaseTransmission c t α) 0 0 := by
  unfold phaseSheet spectralLocusSheet
  apply recovered_locus_response
  rw [phaseTransmission_eq]
  have hd : Real.cos α + phaseQ c t ≠ 0 := hα
  have hc := congrArg (fun x : ℝ => x * Real.cos α) hsphere
  have hs := congrArg (fun x : ℝ => x * Real.sin α) hsphere
  have hcircle := Real.sin_sq_add_cos_sq α
  have hq := congrArg (fun x : ℝ => x * phaseQ c t) hcircle
  have hx := congrArg (fun x : ℝ => x * phaseRx c t) hcircle
  have hy := congrArg (fun x : ℝ => x * phaseRy c t) hcircle
  have hz := congrArg (fun x : ℝ => x * phaseRz c t) hcircle
  simp only [phaseMatrix, phaseCayleyScale]
  generalize hq0 : phaseQ c t = q at *
  generalize hx0 : phaseRx c t = x at *
  generalize hy0 : phaseRy c t = y at *
  generalize hz0 : phaseRz c t = z at *
  generalize hcos0 : Real.cos α = ca at *
  generalize hsin0 : Real.sin α = sa at *
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, two_smul,
      Complex.mul_re, Complex.mul_im] <;>
    simp only [← Complex.ofReal_add, Complex.div_ofReal_re, Complex.div_ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, add_zero, zero_div] <;>
    field_simp [hd] <;> nlinarith only [hc, hs, hq, hx, hy, hz]

theorem phaseSheet_forward (cfg : Config) (c : PhaseCoefficients) (t α : ℝ)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1)
    (hα : phaseCayleyScale c t α ≠ 0) :
    biForwardT cfg (phaseSheet cfg c t α) = phaseTransmission c t α := by
  change (BICompletionMinimum.asScattering (biPowerResponse4 cfg (phaseSheet cfg c t α))).t21 = _
  rw [phaseSheet_response cfg c t α hsphere hα]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem phaseSheet_unique (cfg : Config) (c : PhaseCoefficients) (t α : ℝ) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1)
    (hα : phaseCayleyScale c t α ≠ 0)
    (hp : biForwardT cfg p = phaseTransmission c t α) : p = phaseSheet cfg c t α := by
  apply eq_of_same_unitary_forward cfg (phaseSheet cfg c t α) p hk heq
  · rw [phaseSheet_forward cfg c t α hsphere hα]
    exact phaseTransmission_unitary c t α hsphere
  · exact hp.trans (phaseSheet_forward cfg c t α hsphere hα).symm

theorem budget_of_prescribed_phaseTransmission (cfg : Config) (c : PhaseCoefficients)
    (t α : ℝ) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1)
    (hα : phaseCayleyScale c t α ≠ 0)
    (hp : biForwardT cfg p = phaseTransmission c t α) :
    spectralTotalBudget cfg (assign p) = freeSpaceK0 cfg * 2 / |phaseCayleyScale c t α| *
      max (max (spectralElectricScale cfg) (spectralMagneticScale cfg) *
        (Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) + |Real.sin α|))
        (spectralChiralScale cfg * |phaseRy c t|) := by
  rw [phaseSheet_unique cfg c t α p hk heq hsphere hα hp]
  exact phaseSheetBudget cfg c t α hα

end GSTC.Scattering.OrthogonalSpectralBridge
