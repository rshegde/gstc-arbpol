/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIFrontierCompletion

public section
set_option autoImplicit false
namespace GSTC.Scattering.BIUnitaryTransmission
open Matrix BIInverse BICompletionMinimum BIFrontierCompletion
open BIRankOneCompletion BIRankOneTheorem BIRankOneEndpoint
open BIFeasibility BIPolynomials MaterialSpace SusceptibilityBudget
open scoped Matrix

theorem response_eq_of_cayley_equation (cfg : Config) (p : BIParams)
    (S : Matrix (Fin 4) (Fin 4) ℂ)
    (h : (2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • biConstitutiveK cfg p) *
      (Theta * S) = 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
        Complex.I • biConstitutiveK cfg p) :
    biPowerResponse4 cfg p = S := by
  have hc := (cayley4_eq (biConstitutiveK cfg p)
    (biConstitutiveK_den_isUnit cfg p) (Theta * S)).mp h
  rw [biPowerResponse4, ← hc, ← Matrix.mul_assoc, parityExchange_sq, Matrix.one_mul]

theorem cayley_equation_right_of_left (K T : Ten2)
    (h : (2 • (1 : Ten2) - Complex.I • K) * T = 2 • (1 : Ten2) + Complex.I • K) :
    T * (2 • (1 : Ten2) - Complex.I • K) = 2 • (1 : Ten2) + Complex.I • K := by
  let D := 2 • (1 : Ten2) - Complex.I • K
  let N := 2 • (1 : Ten2) + Complex.I • K
  have hN : N = (4 : ℂ) • (1 : Ten2) - D := by dsimp [N, D]; module
  have he : D * (T + 1) = (4 : ℂ) • (1 : Ten2) := by
    rw [Matrix.mul_add, Matrix.mul_one]
    change (2 • (1 : Ten2) - Complex.I • K) * T + D = _
    rw [h]
    dsimp [D]
    module
  have hi : D * ((1 / 4 : ℂ) • (T + 1)) = 1 := by
    rw [Matrix.mul_smul, he, smul_smul]
    norm_num
  have hi' := (mul_eq_one_comm).mp hi
  have hx := congrArg (fun M : Ten2 => (4 : ℂ) • M) hi'
  simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, smul_smul] at hx
  norm_num at hx
  change T * D = N
  rw [hN]
  calc T * D = (T * D + D) - D := by abel
       _ = (4 : ℂ) • (1 : Ten2) - D := by rw [hx]

theorem recovered_locus_response (cfg : Config) (a d : ℝ) (b : ℂ) (T : Ten2)
    (h : (2 • (1 : Ten2) - Complex.I • !![(a : ℂ), b; star b, d]) * T =
      2 • (1 : Ten2) + Complex.I • !![(a : ℂ), b; star b, d]) :
    biPowerResponse4 cfg (recoverParameters cfg (locusMatrix a d b 0 0 0)) =
      completion T 0 0 := by
  let K : Ten2 := !![(a : ℂ), b; star b, d]
  have hlocus : locusMatrix a d b 0 0 0 = block K 0 0 K.transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [locusMatrix, block, scatteringMatrix4, K]
  have htheta : Theta * completion T 0 0 = block T 0 0 T.transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Theta, parityExchange, completion, block, scatteringMatrix4,
        Matrix.mul_apply, Fin.sum_univ_four]
  have hleft : (2 • (1 : Ten2) - Complex.I • K) * T =
      2 • (1 : Ten2) + Complex.I • K := h
  have hr := cayley_equation_right_of_left K T hleft
  have ht : (2 • (1 : Ten2) - Complex.I • K.transpose) * T.transpose =
      2 • (1 : Ten2) + Complex.I • K.transpose := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_add,
      Matrix.transpose_smul, Matrix.transpose_one] using congrArg Matrix.transpose hr
  apply response_eq_of_cayley_equation
  rw [recover_canonical, hlocus, htheta]
  have hd : 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • block K 0 0 K.transpose =
      block (2 • (1 : Ten2) - Complex.I • K) 0 0
        (2 • (1 : Ten2) - Complex.I • K.transpose) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [block, scatteringMatrix4, Matrix.sub_apply, Matrix.smul_apply, two_smul]
  have hn : 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Complex.I • block K 0 0 K.transpose =
      block (2 • (1 : Ten2) + Complex.I • K) 0 0
        (2 • (1 : Ten2) + Complex.I • K.transpose) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [block, scatteringMatrix4, Matrix.add_apply, Matrix.smul_apply, two_smul]
  rw [hd, hn, block_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hleft, ht]

theorem response_eq_reflectionless (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hu : (biForwardT cfg p).conjTranspose * biForwardT cfg p = 1) :
    biPowerResponse4 cfg p = completion (biForwardT cfg p) 0 0 := by
  let X := biForwardT cfg p
  let S := biPowerResponse4 cfg p
  have hX : X.det ≠ 0 := by
    intro hz
    have hd := congrArg Matrix.det hu
    change (X.conjTranspose * X).det = (1 : Ten2).det at hd
    rw [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at hd
    exact zero_ne_one hd
  obtain ⟨hs, hunit⟩ := response_symmetric_unitary cfg p hk heq
  have hblocks : S = completion X (asScattering S).r1 (asScattering S).r2 :=
    symmetric_eq_completion S X hs rfl
  have hs' : (completion X (asScattering S).r1 (asScattering S).r2).transpose =
      completion X (asScattering S).r1 (asScattering S).r2 := by
    rw [← hblocks]
    exact hs
  have hu' : (completion X (asScattering S).r1 (asScattering S).r2).conjTranspose *
      completion X (asScattering S).r1 (asScattering S).r2 = 1 := by
    rw [← hblocks]
    exact hunit
  have hdefect : X.transpose * X.map star = 1 :=
    (transpose_mul_conj_eq_one_iff X).mpr hu
  obtain ⟨hZ, hY⟩ := endpoint_zero X (asScattering S).r1 (asScattering S).r2
    hX hdefect hs' hu'
  simpa only [hZ, hY] using hblocks

theorem parameters_eq_recovery (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hu : (biForwardT cfg p).conjTranspose * biForwardT cfg p = 1) :
    p = parametersForResponse cfg (completion (biForwardT cfg p) 0 0) := by
  rw [← response_eq_reflectionless cfg p hk heq hu, recover_response]

theorem eq_of_same_unitary_forward (cfg : Config) (p q : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hu : (biForwardT cfg p).conjTranspose * biForwardT cfg p = 1)
    (ht : biForwardT cfg q = biForwardT cfg p) : q = p := by
  have hqu : (biForwardT cfg q).conjTranspose * biForwardT cfg q = 1 := by
    rw [ht]
    exact hu
  rw [parameters_eq_recovery cfg q hk heq hqu, ht]
  exact (parameters_eq_recovery cfg p hk heq hu).symm

end GSTC.Scattering.BIUnitaryTransmission
