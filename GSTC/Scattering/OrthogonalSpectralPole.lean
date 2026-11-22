/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.

Licensed under the MIT License.

Part of the GSTC formalization of the manuscript
`rshegde/paper-gstc_arbpol_bounds`, Section 3B.1.
-/
module

public import GSTC.Scattering.OrthogonalSpectralOptimum

public section
set_option autoImplicit false

namespace GSTC.Scattering
namespace OrthogonalSpectralPole

open scoped Matrix
open BIUnitaryTransmission
open BIRankOneCompletion
open BIFeasibility
open ClassFeasibility
open SusceptibilityBudget
open BIPolynomials
open MaterialSpace
open OrthogonalSpectralBridge
open OrthogonalSpectralOptimum

def bl11 (M : Matrix (Fin 4) (Fin 4) ℂ) : Ten2 := !![M 0 0, M 0 1; M 1 0, M 1 1]

def bl12 (M : Matrix (Fin 4) (Fin 4) ℂ) : Ten2 := !![M 0 2, M 0 3; M 1 2, M 1 3]

def bl21 (M : Matrix (Fin 4) (Fin 4) ℂ) : Ten2 := !![M 2 0, M 2 1; M 3 0, M 3 1]

def bl22 (M : Matrix (Fin 4) (Fin 4) ℂ) : Ten2 := !![M 2 2, M 2 3; M 3 2, M 3 3]

theorem blocks_eq (M : Matrix (Fin 4) (Fin 4) ℂ) :
    block (bl11 M) (bl12 M) (bl21 M) (bl22 M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, scatteringMatrix4, bl11, bl12, bl21, bl22,
      Matrix.cons_val_zero, Matrix.cons_val_one]

theorem denominator_blocks (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • M
      = block ((2 : ℂ) • (1 : Ten2) - Complex.I • bl11 M) (-Complex.I • bl12 M)
          (-Complex.I • bl21 M) ((2 : ℂ) • (1 : Ten2) - Complex.I • bl22 M) := by
  rw [← blocks_eq M]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, scatteringMatrix4, bl11, bl12, bl21, bl22,
      Matrix.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]

theorem numerator_blocks (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Complex.I • M
      = block ((2 : ℂ) • (1 : Ten2) + Complex.I • bl11 M) (Complex.I • bl12 M)
          (Complex.I • bl21 M) ((2 : ℂ) • (1 : Ten2) + Complex.I • bl22 M) := by
  rw [← blocks_eq M]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, scatteringMatrix4, bl11, bl12, bl21, bl22,
      Matrix.add_apply, Matrix.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]

theorem parity_mul_completion (T : Ten2) :
    parityExchange * (completion T 0 0) = block T 0 0 T.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parityExchange, completion, block, scatteringMatrix4,
      Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one]

theorem cayley_block_equation (K : Matrix (Fin 4) (Fin 4) ℂ) (T : Ten2)
    (h : ((2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • K)
        * (parityExchange * (completion T 0 0))
        = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Complex.I • K) :
    (2 • (1 : Ten2) - Complex.I • bl11 K) * T
      = 2 • (1 : Ten2) + Complex.I • bl11 K := by
  rw [denominator_blocks K, parity_mul_completion T, numerator_blocks K, block_mul] at h
  have h1 := (block_eq_iff _ _ _ _ _ _ _ _).mp h
  rw [Matrix.mul_zero, add_zero] at h1
  simpa only [two_smul] using h1.1

theorem det_one_add_forwardT_ne_zero (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hu : (biForwardT cfg p).conjTranspose * biForwardT cfg p = 1) :
    ((1 : Ten2) + biForwardT cfg p).det ≠ 0 := by
  set T := biForwardT cfg p with hT
  have hresp : biPowerResponse4 cfg p = completion T 0 0 := by
    rw [hT]
    exact response_eq_reflectionless cfg p hk heq hu
  have hcay : cayley4 (biConstitutiveK cfg p) = parityExchange * (completion T 0 0) := by
    calc cayley4 (biConstitutiveK cfg p)
        = parityExchange * (parityExchange * cayley4 (biConstitutiveK cfg p)) := by
          rw [← Matrix.mul_assoc, parityExchange_sq, Matrix.one_mul]
      _ = parityExchange * biPowerResponse4 cfg p := by rw [biPowerResponse4]
      _ = parityExchange * (completion T 0 0) := by rw [hresp]
  have hden := biDenominator_mul_cayley cfg p
  rw [hcay] at hden
  have h2 := cayley_block_equation (biConstitutiveK cfg p) T
    (by simpa only [biDenominator, biNumerator4, two_smul] using hden)
  have h3 : (2 • (1 : Ten2) - Complex.I • bl11 (biConstitutiveK cfg p)) * ((1 : Ten2) + T)
      = (4 : ℂ) • (1 : Ten2) := by
    calc (2 • (1 : Ten2) - Complex.I • bl11 (biConstitutiveK cfg p)) * ((1 : Ten2) + T)
        = (2 • (1 : Ten2) - Complex.I • bl11 (biConstitutiveK cfg p)) * (1 : Ten2)
            + (2 • (1 : Ten2) - Complex.I • bl11 (biConstitutiveK cfg p)) * T := by
          rw [Matrix.mul_add]
      _ = (2 • (1 : Ten2) - Complex.I • bl11 (biConstitutiveK cfg p))
            + (2 • (1 : Ten2) + Complex.I • bl11 (biConstitutiveK cfg p)) := by
          rw [Matrix.mul_one, h2]
      _ = (4 : ℂ) • (1 : Ten2) := by module
  have hdet : (2 • (1 : Ten2) - Complex.I • bl11 (biConstitutiveK cfg p)).det
      * ((1 : Ten2) + T).det = ((4 : ℂ) • (1 : Ten2)).det := by
    rw [← Matrix.det_mul, h3]
  have h16 : ((4 : ℂ) • (1 : Ten2)).det = 16 := by
    rw [Matrix.det_fin_two]
    simp [Matrix.smul_apply]
    ring
  intro hzero
  rw [hzero, mul_zero, h16] at hdet
  norm_num at hdet

theorem det_one_add_smul_entries (a b c d z : ℂ) :
    ((1 : Ten2) + z • !![a, b; c, d]).det
      = 1 + z * (a + d) + z ^ 2 * (a * d - b * c) := by
  rw [Matrix.det_fin_two]
  simp [Matrix.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem det_one_add_phaseTransmission (c : PhaseCoefficients) (t α : ℝ)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1) :
    ((1 : Ten2) + phaseTransmission c t α).det
      = 1 + 2 * (phaseQ c t : ℂ) * ((Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ))
        + ((Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ)) ^ 2 := by
  have hζ : phaseTransmission c t α
      = ((Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ)) • phaseMatrix c t :=
    phaseTransmission_eq c t α
  rw [hζ]
  simp only [phaseMatrix]
  rw [det_one_add_smul_entries]
  have htr : (phaseQ c t : ℂ) + Complex.I * (phaseRz c t : ℂ)
      + ((phaseQ c t : ℂ) - Complex.I * (phaseRz c t : ℂ))
      = 2 * (phaseQ c t : ℂ) := by ring
  have hdet : ((phaseQ c t : ℂ) + Complex.I * (phaseRz c t : ℂ))
      * ((phaseQ c t : ℂ) - Complex.I * (phaseRz c t : ℂ))
      - ((phaseRy c t : ℂ) + Complex.I * (phaseRx c t : ℂ))
        * (-(phaseRy c t : ℂ) + Complex.I * (phaseRx c t : ℂ))
      = ((phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [htr, hdet, hsphere]
  push_cast
  ring

theorem det_one_add_phaseTransmission_eq_zero (c : PhaseCoefficients) (t α : ℝ)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1)
    (hpole : Real.cos α + phaseQ c t = 0) :
    ((1 : Ten2) + phaseTransmission c t α).det = 0 := by
  rw [det_one_add_phaseTransmission c t α hsphere]
  have hq : (phaseQ c t : ℂ) = -((Real.cos α : ℂ)) := by
    have h : phaseQ c t = -Real.cos α := by linarith [hpole]
    rw [← Complex.ofReal_neg]
    exact_mod_cast h
  rw [hq]
  have hzero : (1 : ℂ) - 2 * ((Real.cos α : ℂ))
      * ((Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ))
      + ((Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ)) ^ 2 = 0 := by
    have hcircle := Real.cos_sq_add_sin_sq α
    generalize hcos : Real.cos α = ca at hcircle ⊢
    generalize hsin : Real.sin α = sa at hcircle ⊢
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, pow_two] <;> nlinarith only [hcircle]
  convert hzero using 1; ring

theorem phaseCayleyScale_ne_of_forward (cfg : Config) (c : PhaseCoefficients) (t α : ℝ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1)
    (p : BIParams) (hp : biForwardT cfg p = phaseTransmission c t α) :
    phaseCayleyScale c t α ≠ 0 := by
  have hu : (biForwardT cfg p).conjTranspose * biForwardT cfg p = 1 := by
    rw [hp]
    exact phaseTransmission_unitary c t α hsphere
  have hne := det_one_add_forwardT_ne_zero cfg p hk heq hu
  by_contra hcon
  have hpole : Real.cos α + phaseQ c t = 0 := by
    have hcs : phaseCayleyScale c t α = Real.cos α + phaseQ c t := rfl
    rw [hcs] at hcon
    exact hcon
  have hz : ((1 : Ten2) + biForwardT cfg p).det = 0 := by
    rw [hp]
    exact det_one_add_phaseTransmission_eq_zero c t α hsphere hpole
  exact hne hz

theorem fixedPhase_spectral_optimum_all (cfg : Config) (c : PhaseCoefficients)
    (t α : ℝ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1)
    (p : BIParams) (hp : biForwardT cfg p = phaseTransmission c t α) :
    phaseMinimum cfg c t ≤ spectralTotalBudget cfg (assign p) := by
  have hα := phaseCayleyScale_ne_of_forward cfg c t α hk heq hsphere p hp
  exact fixedPhase_spectral_optimum cfg c t α hk heq hsphere hα p hp

end OrthogonalSpectralPole
end GSTC.Scattering
