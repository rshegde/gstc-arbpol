/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module
public import GSTC.Scattering.RotatedRankOneImage

public section
set_option autoImplicit false
namespace GSTC.Scattering.RotatedRankOneRecovery
open scoped Matrix
open Matrix BIInverse BIRankOneCompletion BIRankOneTheorem BIFrontierCompletion
open RotatedRankOneResources SusceptibilityBudget MaterialSpace BIPolynomials ClassFeasibility
open BICompletionMinimum Operator

@[expose] noncomputable def familyTransmission (s c j x y : ℝ) : Ten2 :=
  let z : ℂ := (x : ℂ)+Complex.I*(y : ℂ)
  !![z*c*s, -z*j; z*j*s, z*c]

@[expose] noncomputable def familyReflection (r h k : ℝ) : Ten2 :=
  !![(r : ℂ)*((h : ℂ)+Complex.I*(k : ℂ)),0;0,0]

@[expose] noncomputable def familyOtherReflection (r c j x y h k : ℝ) : Ten2 :=
  let a : ℂ := -(r : ℂ)*((x : ℂ)+Complex.I*(y : ℂ))^2*((h : ℂ)-Complex.I*(k : ℂ))
  !![a*c^2,a*c*j; a*c*j,a*j^2]

theorem familyResponse_eq_completion (s r c j x y h k : ℝ) :
    familyResponse s r c j x y h k = completion (familyTransmission s c j x y)
      (familyReflection r h k) (familyOtherReflection r c j x y h k) := by
  ext i j'
  fin_cases i <;> fin_cases j' <;>
    simp [familyResponse, rotatedC, familyTransmission, familyReflection,
      familyOtherReflection, completion, block, scatteringMatrix4, Theta, parityExchange,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply]

theorem familyTransmission_det (s c j x y : ℝ) (hc : j^2+c^2=1) :
    (familyTransmission s c j x y).det =
      ((x : ℂ)+Complex.I*(y : ℂ))^2*(s : ℂ) := by
  have hc' : (j : ℂ)^2+(c : ℂ)^2=1 := by exact_mod_cast hc
  simp [familyTransmission, Matrix.det_fin_two]
  linear_combination (((x : ℂ)+Complex.I*(y : ℂ))^2*(s : ℂ))*hc'

theorem familyTransmission_nonsingular (s c j x y : ℝ) (hs : s ≠ 0)
    (hc : j^2+c^2=1) (hx : y^2+x^2=1) : (familyTransmission s c j x y).det ≠ 0 := by
  rw [familyTransmission_det s c j x y hc]
  have hz : (x : ℂ)+Complex.I*(y : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp at hre him
    nlinarith
  exact mul_ne_zero (pow_ne_zero _ hz) (Complex.ofReal_ne_zero.mpr hs)

theorem familyTransmission_defect (s r c j x y : ℝ)
    (hr : r^2+s^2=1) (hc : j^2+c^2=1) (hx : y^2+x^2=1) :
    1-(familyTransmission s c j x y).transpose*(familyTransmission s c j x y).map star =
      (r^2 : ℂ) • projection (![1,0] : Vec2) := by
  ext i j'
  fin_cases i <;> fin_cases j' <;> apply Complex.ext <;>
    simp [familyTransmission, projection, Matrix.vecMulVec, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      Complex.mul_re, Complex.mul_im, pow_two]
  all_goals solve | ring |
    linear_combination -(s^2*(x^2+y^2))*hc-s^2*hx-hr |
    linear_combination -(x^2+y^2)*hc-hx

theorem family_mixed (s r c j x y h k : ℝ)
    (hc : j^2+c^2=1) (hx : y^2+x^2=1) :
    (familyTransmission s c j x y).conjTranspose * familyOtherReflection r c j x y h k +
      (familyReflection r h k).conjTranspose * (familyTransmission s c j x y).transpose=0 := by
  ext i j'
  fin_cases i <;> fin_cases j'
  · apply Complex.ext
    · simp [familyTransmission, familyReflection, familyOtherReflection,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, Complex.mul_re, Complex.mul_im, pow_two]
      linear_combination (((-1 * c * h * r * s * (x) ^ 3) + (-1 * c * k * r * s * (y) ^ 3) + (-1 * c * h * r * s * x * (y) ^ 2) + (-1 * c * k * r * s * y * (x) ^ 2))) * hc + (((-1 * c * h * r * s * x) + (-1 * c * k * r * s * y))) * hx
    · simp [familyTransmission, familyReflection, familyOtherReflection,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, Complex.mul_re, Complex.mul_im, pow_two]
      linear_combination (((c * k * r * s * (x) ^ 3) + (-1 * c * h * r * s * (y) ^ 3) + (c * k * r * s * x * (y) ^ 2) + (-1 * c * h * r * s * y * (x) ^ 2))) * hc + (((c * k * r * s * x) + (-1 * c * h * r * s * y))) * hx
  · apply Complex.ext
    · simp [familyTransmission, familyReflection, familyOtherReflection,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, Complex.mul_re, Complex.mul_im, pow_two]
      linear_combination (((-1 * h * j * r * s * (x) ^ 3) + (-1 * j * k * r * s * (y) ^ 3) + (-1 * h * j * r * s * x * (y) ^ 2) + (-1 * j * k * r * s * y * (x) ^ 2))) * hc + (((-1 * h * j * r * s * x) + (-1 * j * k * r * s * y))) * hx
    · simp [familyTransmission, familyReflection, familyOtherReflection,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, Complex.mul_re, Complex.mul_im, pow_two]
      linear_combination (((j * k * r * s * (x) ^ 3) + (-1 * h * j * r * s * (y) ^ 3) + (j * k * r * s * x * (y) ^ 2) + (-1 * h * j * r * s * y * (x) ^ 2))) * hc + (((j * k * r * s * x) + (-1 * h * j * r * s * y))) * hx
  · apply Complex.ext
    · simp [familyTransmission, familyReflection, familyOtherReflection,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, Complex.mul_re, Complex.mul_im, pow_two]
      ring
    · simp [familyTransmission, familyReflection, familyOtherReflection,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, Complex.mul_re, Complex.mul_im, pow_two]
      ring
  · apply Complex.ext
    · simp [familyTransmission, familyReflection, familyOtherReflection,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, Complex.mul_re, Complex.mul_im, pow_two]
      ring
    · simp [familyTransmission, familyReflection, familyOtherReflection,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, Complex.mul_re, Complex.mul_im, pow_two]
      ring

theorem familyOtherReflection_forced (s r c j x y h k : ℝ) (hs : s ≠ 0)
    (hc : j^2+c^2=1) (hx : y^2+x^2=1) :
    familyOtherReflection r c j x y h k =
      forcedY (familyTransmission s c j x y) (familyReflection r h k) :=
  (mixed_equation_iff _ _ _ (familyTransmission_nonsingular s c j x y hs hc hx)).mp
    (family_mixed s r c j x y h k hc hx)

theorem admissible_completion_in_family (S : Matrix (Fin 4) (Fin 4) ℂ)
    (s r c j x y : ℝ) (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hs : s ≠ 0) (hr0 : 0 ≤ r) (hr : r^2+s^2=1)
    (hc : j^2+c^2=1) (hx : y^2+x^2=1)
    (ht : (asScattering S).t21=familyTransmission s c j x y)
    (hS : admissible u₁ u₂ v₁ v₂ η S) :
    ∃ β : ℝ, S=familyResponse s r c j x y (Real.cos β) (Real.sin β) := by
  have hn : star (![1,0] : Vec2) ⬝ᵥ (![1,0] : Vec2)=1 := by
    norm_num [dotProduct,Fin.sum_univ_two]
  obtain ⟨β,Z,hZ,hfull⟩ := admissible_has_rankOne S (familyTransmission s c j x y)
    (![1,0] : Vec2) (r^2) u₁ u₂ v₁ v₂ η
    (familyTransmission_nonsingular s c j x y hs hc hx) hn (sq_nonneg r)
    (by simpa only [Complex.ofReal_pow] using familyTransmission_defect s r c j x y hr hc hx) ht hS
  have hz : Z=familyReflection r (Real.cos β) (Real.sin β) := by
    rw [hZ,Real.sqrt_sq hr0,Complex.exp_ofReal_mul_I]
    ext i j'
    fin_cases i <;> fin_cases j' <;>
      simp [familyReflection,symmetricOuter,Matrix.vecMulVec,Matrix.smul_apply,mul_comm]
  refine ⟨β,?_⟩
  rw [hfull,hz,← familyOtherReflection_forced s r c j x y (Real.cos β) (Real.sin β) hs hc hx,
    ← familyResponse_eq_completion]

theorem complete_family_physical_resources (cfg : Config) (p : BIParams)
    (S : Matrix (Fin 4) (Fin 4) ℂ) (s r c j x y : ℝ)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hs : s ≠ 0) (hr0 : 0 ≤ r) (hr : r^2+s^2=1)
    (hc : j^2+c^2=1) (hx : y^2+x^2=1)
    (heta : cfg.upper.eta=cfg.vac.eta0)
    (ht : (asScattering S).t21=familyTransmission s c j x y)
    (hS : admissible u₁ u₂ v₁ v₂ η S) (hp : biPowerResponse4 cfg p=S) :
    ∃ β : ℝ, S=familyResponse s r c j x y (Real.cos β) (Real.sin β) ∧
      rotDomain s c x |Real.sin β*x-Real.cos β*y| ∧
      spectralDirectBudget cfg (assign p)=
        rotDirect (rotReducedScalars s r c j x) |Real.sin β*x-Real.cos β*y| ∧
      spectralCouplingBudget cfg (assign p)=
        rotCoupling (rotReducedScalars s r c j x) |Real.sin β*x-Real.cos β*y| := by
  obtain ⟨β,hβ⟩ := admissible_completion_in_family S s r c j x y u₁ u₂ v₁ v₂ η
    hs hr0 hr hc hx ht hS
  have hpol := hS.2.2.1
  rw [hβ,theta_familyResponse] at hpol
  have hf := (rotatedC_pole_iff s r c j x y (Real.cos β) (Real.sin β)
    hr hc hx (Real.sin_sq_add_cos_sq β)).mp hpol
  have hb := every_completion_reduced_budgets cfg p s r c j x y
    (Real.cos β) (Real.sin β) hr hc hx (Real.sin_sq_add_cos_sq β) hf heta (hp.trans hβ)
  exact ⟨β,hβ,hb⟩

theorem supplement_parameters (a b : ℝ) (hb : 0 < b) (hba : b < a) (ha : a < 1) :
    0 < rotS a b ∧ rotS a b < 1 ∧
      0 ≤ rotR (rotS a b) ∧ (rotR (rotS a b))^2+(rotS a b)^2=1 := by
  have ha0 : 0 < a := lt_trans hb hba
  have hb1 : b < 1 := lt_trans hba ha
  have hd : 0 < (1+a)*(1-b) := mul_pos (by linarith) (by linarith)
  have hn : 0 < (1-a)*(1+b) := mul_pos (by linarith) (by linarith)
  have hq : (1-a)*(1+b)/((1+a)*(1-b)) < 1 := by
    rw [div_lt_one hd]
    nlinarith
  have hs0 : 0 < rotS a b := Real.sqrt_pos.mpr (div_pos hn hd)
  have hs1 : rotS a b < 1 := (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr (by simpa using hq)
  refine ⟨hs0,hs1,Real.sqrt_nonneg _,?_⟩
  dsimp [rotR]
  rw [Real.sq_sqrt (by nlinarith)]
  ring

end GSTC.Scattering.RotatedRankOneRecovery
