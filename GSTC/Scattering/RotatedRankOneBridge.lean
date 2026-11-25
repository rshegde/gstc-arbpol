/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module
public import GSTC.Scattering.RotatedRankOnePole
public import GSTC.Scattering.RotatedRankOnePhysicalBlocks
public import GSTC.Scattering.OrthogonalSpectralMinimum

public section
set_option autoImplicit false
namespace GSTC.Scattering.RotatedRankOneRecovery
open scoped Matrix Matrix.Norms.L2Operator
open Matrix BIInverse RotatedRankOneResources SpectralMatrixSupport
open SusceptibilityBudget MaterialSpace BIPolynomials

@[expose] def electricRecovery (K : Matrix (Fin 4) (Fin 4) ℂ) : Mat :=
  !![-(K 0 0).re-(K 0 2).re, -(K 0 1).re-(K 0 3).re;
     -(K 0 1).re-(K 0 3).re, -(K 1 1).re-(K 1 3).re]

@[expose] def magneticRecovery (K : Matrix (Fin 4) (Fin 4) ℂ) : Mat :=
  !![-(K 1 1).re+(K 1 3).re, (K 0 1).re-(K 0 3).re;
     (K 0 1).re-(K 0 3).re, -(K 0 0).re+(K 0 2).re]

@[expose] def couplingRecovery (K : Matrix (Fin 4) (Fin 4) ℂ) : Mat :=
  !![-(K 0 1).im+(K 0 3).im, -(K 0 2).im;
     (K 1 3).im, -(K 0 1).im-(K 0 3).im]

theorem recovered_electricBlock (cfg : Config) (K : Matrix (Fin 4) (Fin 4) ℂ) :
    electricBlock (assign (recoverParameters cfg K)) = spectralElectricScale cfg • electricRecovery K := by
  have hη := Real.sq_sqrt cfg.upper.eta_pos.le
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [electricBlock, assign, recoverParameters, spectralElectricScale, electricRecovery,
      Matrix.smul_apply, hη] <;> ring

theorem recovered_magneticBlock (cfg : Config) (K : Matrix (Fin 4) (Fin 4) ℂ) :
    magneticBlock (assign (recoverParameters cfg K)) = spectralMagneticScale cfg • magneticRecovery K := by
  have hη := Real.sq_sqrt cfg.upper.eta_pos.le
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [magneticBlock, assign, recoverParameters, spectralMagneticScale, magneticRecovery,
      Matrix.smul_apply, hη] <;> ring

theorem recovered_couplingBlock (cfg : Config) (K : Matrix (Fin 4) (Fin 4) ℂ) :
    couplingBlock (assign (recoverParameters cfg K)) = spectralChiralScale cfg • couplingRecovery K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [couplingBlock, assign, recoverParameters, spectralChiralScale, couplingRecovery,
      Matrix.smul_apply] <;> ring

theorem electricRecovery_numerator (s r c j x y h k : ℝ)
    (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hf : rotF s c x y ≠ 0) :
    electricRecovery (((rotF s c x y : ℂ)⁻¹) • recoveryNumerator s r c j x y h k) =
      physicalElectric (rotScalars s r c j x y) c j (k*x-h*y) (h*x+k*y) := by
  ext i j'
  fin_cases i <;> fin_cases j'
  · simp [electricRecovery, recoveryNumerator, locusMatrix, physicalElectric,
      rotScalars, rotP0, rotP1, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (((2 * k * r) + (-2 * k * r * (y) ^ 2) + (-2 * h * r * x * y))) * hc + (((-2 * k * r) + (2 * k * r * (c) ^ 2))) * hx
  · simp [electricRecovery, recoveryNumerator, locusMatrix, physicalElectric,
      rotScalars, rotP0, rotP1, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (1/2 : ℝ) * (((2 * c * j * k * r)) * hx)
  · simp [electricRecovery, recoveryNumerator, locusMatrix, physicalElectric,
      rotScalars, rotP0, rotP1, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (1/2 : ℝ) * (((2 * c * j * k * r)) * hx)
  · simp [electricRecovery, recoveryNumerator, locusMatrix, physicalElectric,
      rotScalars, rotP0, rotP1, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (((-2 * k * r) + (2 * k * r * (y) ^ 2) + (2 * h * r * x * y))) * hc + (((2 * k * r) + (-2 * k * r * (c) ^ 2))) * hx

theorem magneticRecovery_numerator (s r c j x y h k : ℝ)
    (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hf : rotF s c x y ≠ 0) :
    magneticRecovery (((rotF s c x y : ℂ)⁻¹) • recoveryNumerator s r c j x y h k) =
      physicalMagnetic (rotScalars s r c j x y) c j (k*x-h*y) (h*x+k*y) := by
  ext i j'
  fin_cases i <;> fin_cases j'
  · simp [magneticRecovery, recoveryNumerator, locusMatrix, physicalMagnetic,
      rotScalars, rotP0, rotP1, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (((2 * k * r) + (-2 * k * r * (y) ^ 2) + (-2 * h * r * x * y))) * hc + (((-2 * k * r) + (2 * k * r * (c) ^ 2))) * hx
  · simp [magneticRecovery, recoveryNumerator, locusMatrix, physicalMagnetic,
      rotScalars, rotP0, rotP1, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (1/2 : ℝ) * (((2 * c * j * k * r)) * hx)
  · simp [magneticRecovery, recoveryNumerator, locusMatrix, physicalMagnetic,
      rotScalars, rotP0, rotP1, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (1/2 : ℝ) * (((2 * c * j * k * r)) * hx)
  · simp [magneticRecovery, recoveryNumerator, locusMatrix, physicalMagnetic,
      rotScalars, rotP0, rotP1, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (((-2 * k * r) + (2 * k * r * (y) ^ 2) + (2 * h * r * x * y))) * hc + (((2 * k * r) + (-2 * k * r * (c) ^ 2))) * hx

theorem couplingRecovery_numerator (s r c j x y h k : ℝ)
    (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hf : rotF s c x y ≠ 0) :
    couplingRecovery (((rotF s c x y : ℂ)⁻¹) • recoveryNumerator s r c j x y h k) =
      physicalCoupling (rotScalars s r c j x y) c j (k*x-h*y) (h*x+k*y) := by
  ext i j'
  fin_cases i <;> fin_cases j'
  · simp [couplingRecovery, recoveryNumerator, locusMatrix, physicalCoupling,
      rotScalars, rotQ, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (1/2 : ℝ) * (((-2 * c * h * j * r)) * hx)
  · simp [couplingRecovery, recoveryNumerator, locusMatrix, physicalCoupling,
      rotScalars, rotQ, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (1/2 : ℝ) * ((((2 * h * r) + (-2 * h * r * (y) ^ 2) + (2 * k * r * x * y))) * hc + (((-2 * h * r) + (2 * h * r * (c) ^ 2))) * hx)
  · simp [couplingRecovery, recoveryNumerator, locusMatrix, physicalCoupling,
      rotScalars, rotQ, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (1/2 : ℝ) * ((((2 * h * r) + (-2 * h * r * (y) ^ 2) + (2 * k * r * x * y))) * hc + (((-2 * h * r) + (2 * h * r * (c) ^ 2))) * hx)
  · simp [couplingRecovery, recoveryNumerator, locusMatrix, physicalCoupling,
      rotScalars, rotQ, rotT, rotU, rotW, ← Complex.ofReal_inv, -Complex.ofReal_pow, Matrix.smul_apply]
    field_simp [hf]
    linear_combination (1/2 : ℝ) * (((2 * c * h * j * r)) * hx)

theorem relativePhase_circle (x y h k : ℝ) (hx : y^2+x^2=1) (hb : k^2+h^2=1) :
    (k*x-h*y)^2+(h*x+k*y)^2=1 := by
  linear_combination (h^2+k^2)*hx + hb

theorem rotScalars_relation (s r c j x y : ℝ)
    (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hf : rotF s c x y ≠ 0) :
    (rotScalars s r c j x y).u^2 =
      (rotScalars s r c j x y).t^2 + (rotScalars s r c j x y).w^2 := by
  dsimp [rotScalars, rotU, rotT, rotW]
  field_simp [hf]
  linear_combination r^2*(x^2-1)*hc - r^2*j^2*hx

theorem real_smul_locus (t a d : ℝ) (b g h e : ℂ) :
    (t : ℂ) • locusMatrix a d b g h e =
      locusMatrix (t*a) (t*d) ((t : ℂ)*b) ((t : ℂ)*g) ((t : ℂ)*h) ((t : ℂ)*e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [locusMatrix, Matrix.smul_apply, star_mul] <;> ring

theorem recovery_constitutive (cfg : Config) (s r c j x y h k : ℝ) :
    biConstitutiveK cfg (recoverParameters cfg
      (((rotF s c x y : ℂ)⁻¹) • recoveryNumerator s r c j x y h k)) =
      ((rotF s c x y : ℂ)⁻¹) • recoveryNumerator s r c j x y h k := by
  dsimp only [recoveryNumerator]
  rw [← Complex.ofReal_inv, real_smul_locus]
  exact recover_canonical cfg _ _ _ _ _ _

@[expose] noncomputable def familyResponse (s r c j x y h k : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Theta * rotatedC s r c j x y h k

theorem theta_familyResponse (s r c j x y h k : ℝ) :
    Theta * familyResponse s r c j x y h k = rotatedC s r c j x y h k := by
  rw [familyResponse, ← Matrix.mul_assoc, parityExchange_sq, Matrix.one_mul]

theorem familyResponse_recovered (cfg : Config) (s r c j x y h k : ℝ)
    (hr : r^2+s^2=1) (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hb : k^2+h^2=1)
    (hf : rotF s c x y ≠ 0) :
    biPowerResponse4 cfg (parametersForResponse cfg (familyResponse s r c j x y h k)) =
      familyResponse s r c j x y h k := by
  apply biPowerResponse4_of_constitutiveK
  · rw [parametersForResponse, theta_familyResponse,
      cayleyPreimage_rotatedC s r c j x y h k hr hc hx hb hf]
    exact recovery_constitutive cfg s r c j x y h k
  · rw [theta_familyResponse]
    exact (rotatedC_pole_iff s r c j x y h k hr hc hx hb).mpr hf

theorem familyResponse_sheet_unique (cfg : Config) (p : BIParams) (s r c j x y h k : ℝ)
    (hr : r^2+s^2=1) (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hb : k^2+h^2=1)
    (hf : rotF s c x y ≠ 0) (hp : biPowerResponse4 cfg p=familyResponse s r c j x y h k) :
    p = parametersForResponse cfg (familyResponse s r c j x y h k) := by
  have hpol : IsUnit ((1+Theta*familyResponse s r c j x y h k).det) := by
    rw [theta_familyResponse]
    exact (rotatedC_pole_iff s r c j x y h k hr hc hx hb).mpr hf
  apply constitutiveK_injective cfg
  exact (constitutiveK_of_response cfg p _ hpol hp).trans
    (constitutiveK_of_response cfg _ _ hpol
      (familyResponse_recovered cfg s r c j x y h k hr hc hx hb hf)).symm

end GSTC.Scattering.RotatedRankOneRecovery
