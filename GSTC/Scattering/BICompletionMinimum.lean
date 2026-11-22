/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.FeasibilityRotation
public import GSTC.Scattering.NBPeakEfficiency

public section
set_option autoImplicit false

namespace GSTC.Scattering.BICompletionMinimum
open BIFeasibility  BIPolynomials  SusceptibilityBudget
open MaterialSpace ClassFeasibility ClassPeakEfficiency
open ClassMinimumBudget FeasibilityRotation BIInverse
open Operator OrthogonalClasses
open scoped Matrix
open Classical

@[expose] def asScattering (S : Mat4) : ScatteringMatrix where
  r1 := !![S 0 0,S 0 1;S 1 0,S 1 1]
  t12 := !![S 0 2,S 0 3;S 1 2,S 1 3]
  t21 := !![S 2 0,S 2 1;S 3 0,S 3 1]
  r2 := !![S 2 2,S 2 3;S 3 2,S 3 3]

theorem scatteringMatrix4_asScattering (S : Mat4) : scatteringMatrix4 (asScattering S) = S := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem normalized_asScattering (cfg : Config) (S : Mat4)
    (heq : cfg.lower.eta = cfg.upper.eta) : scatteringMatrix4_p cfg (asScattering S) = S := by
  have he : (Real.sqrt cfg.upper.eta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr cfg.upper.eta_pos))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scatteringMatrix4_p, asScattering, ScatteringMatrix.t12_norm,
      ScatteringMatrix.t21_norm, heq, he]

theorem rawResponse_eq_power (cfg : Config) (p : BIParams)
    (heq : cfg.lower.eta = cfg.upper.eta) : biRawResponse4 cfg p = biPowerResponse4 cfg p := by
  have hc : portScale4 cfg * biPowerResponse4 cfg p = biPowerResponse4 cfg p * portScale4 cfg := by
    rw [portScale4_eq_scalar cfg heq]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [biRawResponse4, hc, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (portScale4_det_ne_zero cfg)), Matrix.mul_one]

theorem response_conservative (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) :
    (asScattering (biPowerResponse4 cfg p)).Conservative cfg (encode p) := by
  intro a₁ a₂
  have hg := (bi_gstc_iff_raw_response cfg p hk heq (pack a₁ a₂)
    (biPowerResponse4 cfg p *ᵥ pack a₁ a₂)).mpr (by rw [rawResponse_eq_power cfg p heq])
  rw [← scatteringMatrix4_asScattering (biPowerResponse4 cfg p), scatteringMatrix4_mulVec] at hg
  simpa only [Operator.readR_pack, Operator.readT_pack] using hg

theorem response_symmetric_unitary (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) :
    (biPowerResponse4 cfg p).transpose = biPowerResponse4 cfg p ∧
      (biPowerResponse4 cfg p).conjTranspose * biPowerResponse4 cfg p = 1 := by
  have hc := response_conservative cfg p hk heq
  have hs := scatteringMatrix4_p_reciprocity_of_conservative cfg (encode p)
    (asScattering (biPowerResponse4 cfg p)) hk (encode_reciprocal p) hc
    (bi_boundary_det_ne_zero cfg p hk heq)
  have hu := scatteringMatrix4_p_unitarity cfg (encode p)
    (asScattering (biPowerResponse4 cfg p)) hk (encode_lossless p) hc
  simpa only [normalized_asScattering cfg _ heq] using And.intro hs hu

theorem response_poleFree (cfg : Config) (p : BIParams) :
    IsUnit ((1 + Theta * biPowerResponse4 cfg p).det) := by
  let D := 2 • (1 : Mat4) - Complex.I • biConstitutiveK cfg p
  have he := (cayley4_eq _ (biConstitutiveK_den_isUnit cfg p) _).mpr rfl
  have hsum : D * (1 + cayley4 (biConstitutiveK cfg p)) = (4 : ℂ) • (1 : Mat4) := by
    rw [Matrix.mul_add, Matrix.mul_one, he]
    dsimp [D]
    simp only [two_smul]
    module
  have hd := congrArg Matrix.det hsum
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have htheta : Theta * biPowerResponse4 cfg p = cayley4 (biConstitutiveK cfg p) := by
    rw [biPowerResponse4, ← Matrix.mul_assoc, parityExchange_sq, Matrix.one_mul]
  rw [htheta] at hz
  rw [Matrix.det_mul, hz, mul_zero] at hd
  rw [Matrix.det_smul, Matrix.det_one] at hd
  norm_num at hd

theorem recover_response (cfg : Config) (p : BIParams) :
    parametersForResponse cfg (biPowerResponse4 cfg p) = p := by
  rw [parametersForResponse, ← constitutiveK_of_response cfg p _ (response_poleFree cfg p) rfl,
    recover_forward]

@[expose] def admissible (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) (S : Mat4) : Prop :=
  S.transpose = S ∧ S.conjTranspose*S = 1 ∧ IsUnit ((1+Theta*S).det) ∧
  cross v₁ (readT (S *ᵥ pack u₁ 0)) = 0 ∧ cross v₂ (readT (S *ᵥ pack u₂ 0)) = 0 ∧
  jonesNormSqR (readT (S *ᵥ pack u₁ 0)) = η.1 ∧
  jonesNormSqR (readT (S *ᵥ pack u₂ 0)) = η.2

@[expose] noncomputable def completionCost (cfg : Config) (S : Mat4) : ℝ :=
  spectralTotalBudget cfg (assign (parametersForResponse cfg S))

@[expose] noncomputable def completionValues (cfg : Config)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) : Set ℝ :=
  completionCost cfg '' {S | admissible u₁ u₂ v₁ v₂ η S}

@[expose] noncomputable def extendedInf (values : Set ℝ) : WithTop ℝ :=
  if values.Nonempty then (sInf values : ℝ) else ⊤

@[expose] noncomputable def completionMinimum (cfg : Config)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) : WithTop ℝ :=
  extendedInf (completionValues cfg u₁ u₂ v₁ v₂ η)

theorem materialMinimum_eq_extendedInf (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    minimumBudget cfg c u₁ u₂ v₁ v₂ η = extendedInf (budgetValues cfg c u₁ u₂ v₁ v₂ η) := by
  unfold minimumBudget extendedInf finiteMinimumBudget budgetValues
  simp only [Set.image_nonempty]

theorem sheet_admissible (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hp : assign p ∈ classMaterials cfg .BI u₁ u₂ v₁ v₂ η) :
    admissible u₁ u₂ v₁ v₂ η (biPowerResponse4 cfg p) := by
  have hf := (conversionMaterials_iff_response cfg p u₁ u₂ v₁ v₂ η).mp hp.1
  exact ⟨(response_symmetric_unitary cfg p hk heq).1,
    (response_symmetric_unitary cfg p hk heq).2, response_poleFree cfg p,
    by simpa only [readT_biPowerResponse4_pack] using hf⟩

theorem recovered_feasible (cfg : Config) (S : Mat4)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) (hS : admissible u₁ u₂ v₁ v₂ η S) :
    assign (parametersForResponse cfg S) ∈ classMaterials cfg .BI u₁ u₂ v₁ v₂ η := by
  refine ⟨(conversionMaterials_iff_response cfg _ u₁ u₂ v₁ v₂ η).mpr ?_,trivial⟩
  have hr := parametersForResponse_response cfg S hS.1 hS.2.1 hS.2.2.1
  simpa only [← readT_biPowerResponse4_pack, hr] using hS.2.2.2

theorem completionCost_sheet (cfg : Config) (p : BIParams) :
    completionCost cfg (biPowerResponse4 cfg p) = spectralTotalBudget cfg (assign p) := by
  rw [completionCost, recover_response]

theorem completionValues_eq (cfg : Config) (hk : cfg.kPar = 0)
    (heq : cfg.lower.eta = cfg.upper.eta) (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    completionValues cfg u₁ u₂ v₁ v₂ η = budgetValues cfg .BI u₁ u₂ v₁ v₂ η := by
  ext b
  constructor
  · rintro ⟨S,hS,rfl⟩
    exact ⟨assign (parametersForResponse cfg S),recovered_feasible cfg S u₁ u₂ v₁ v₂ η hS,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨biPowerResponse4 cfg (parameters x),?_,?_⟩
    · apply sheet_admissible cfg _ hk heq u₁ u₂ v₁ v₂ η
      simpa only [assign_parameters] using hx
    · simp only [completionCost_sheet, assign_parameters]

theorem minimum_eq_completionMinimum (cfg : Config) (hk : cfg.kPar = 0)
    (heq : cfg.lower.eta = cfg.upper.eta) (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    minimumBudget cfg .BI u₁ u₂ v₁ v₂ η = completionMinimum cfg u₁ u₂ v₁ v₂ η := by
  rw [completionMinimum, completionValues_eq cfg hk heq, materialMinimum_eq_extendedInf]

theorem completion_minimum_attained (cfg : Config) (hk : cfg.kPar = 0)
    (heq : cfg.lower.eta = cfg.upper.eta) (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hne : (classMaterials cfg .BI u₁ u₂ v₁ v₂ η).Nonempty) :
    ∃ S : Mat4, admissible u₁ u₂ v₁ v₂ η S ∧
      completionMinimum cfg u₁ u₂ v₁ v₂ η = (completionCost cfg S : WithTop ℝ) ∧
      ∀ S', admissible u₁ u₂ v₁ v₂ η S' → completionCost cfg S ≤ completionCost cfg S' := by
  obtain ⟨x,hx,hm,hmin⟩ := minimumBudget_attained cfg .BI u₁ u₂ v₁ v₂ η hne
  refine ⟨biPowerResponse4 cfg (parameters x),?_,?_,?_⟩
  · apply sheet_admissible cfg _ hk heq u₁ u₂ v₁ v₂ η
    simpa only [assign_parameters] using hx
  · rw [← minimum_eq_completionMinimum cfg hk heq, completionCost_sheet, assign_parameters]
    exact hm
  · intro S' hS'
    rw [completionCost_sheet, assign_parameters]
    exact hmin (assign (parametersForResponse cfg S')) (recovered_feasible cfg S' u₁ u₂ v₁ v₂ η hS')

theorem minimum_at_class_peak (cfg : Config) (hk : cfg.kPar=0)
    (heq : cfg.lower.eta=cfg.upper.eta) (u₁ u₂ v₁ v₂ : Vec2) :
    let η := classPeakEqualEfficiency cfg .BI u₁ u₂ v₁ v₂
    minimumBudget cfg .BI u₁ u₂ v₁ v₂ (η,η) = completionMinimum cfg u₁ u₂ v₁ v₂ (η,η) :=
  minimum_eq_completionMinimum cfg hk heq u₁ u₂ v₁ v₂ _

theorem admissible_frame_transmission (cfg : Config) (S : Mat4)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ) (hη : 0 < η)
    (hu : (JonesOperatorClassification.jonesColMatrix u₁ u₂).det ≠ 0)
    (hv : (JonesOperatorClassification.jonesColMatrix v₁ v₂).det ≠ 0)
    (hn₁ : BIPhysicalFeasibility.isNormalizedJones v₁)
    (hn₂ : BIPhysicalFeasibility.isNormalizedJones v₂)
    (hS : admissible u₁ u₂ v₁ v₂ (η,η) S) :
    ∃ α β : ℂ, efficiency α=η ∧ efficiency β=η ∧
      (asScattering S).t21 = JonesOperatorClassification.jonesColMatrix v₁ v₂ *
        diag2 α β * (JonesOperatorClassification.jonesColMatrix u₁ u₂)⁻¹ ∧
      (asScattering S).t21.det ≠ 0 := by
  let p := parametersForResponse cfg S
  have hr := parametersForResponse_response cfg S hS.1 hS.2.1 hS.2.2.1
  have ht : (asScattering S).t21 = biForwardT cfg p := by rw [← hr]; rfl
  have hf := recovered_feasible cfg S u₁ u₂ v₁ v₂ (η,η) hS
  obtain ⟨⟨α,h₁,he₁⟩,⟨β,h₂,he₂⟩⟩ :=
    (conversionMaterials_iff_conversions cfg u₁ u₂ v₁ v₂ (η,η) (assign p) hn₁ hn₂).mp hf.1
  simp only [parameters_assign] at h₁ h₂
  have hc : biForwardT cfg p * JonesOperatorClassification.jonesColMatrix u₁ u₂ =
      JonesOperatorClassification.jonesColMatrix v₁ v₂ * diag2 α β := by
    rw [NBPeakEfficiency.mul_columns, h₁, h₂]
    ext i j
    fin_cases j <;> simp [JonesOperatorClassification.jonesColMatrix_apply_zero,
      JonesOperatorClassification.jonesColMatrix_apply_one, diag2, Matrix.mul_apply,
      Fin.sum_univ_two, mul_comm]
  have hm := congrArg (fun M : Ten2 => M * (JonesOperatorClassification.jonesColMatrix u₁ u₂)⁻¹) hc
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.mpr hu)] at hm
  have ha : α ≠ 0 := by intro h; simp [h,efficiency] at he₁; linarith
  have hb : β ≠ 0 := by intro h; simp [h,efficiency] at he₂; linarith
  refine ⟨α,β,he₁,he₂,ht.trans hm,?_⟩
  rw [ht,hm]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv]
  rw [Ring.inverse_eq_inv]
  apply mul_ne_zero (mul_ne_zero hv ?_) (inv_ne_zero hu)
  simp [Matrix.det_fin_two, diag2, ha,hb]

theorem minimum_at_nonsingular_class_peak (cfg : Config) (hk : cfg.kPar=0)
    (heq : cfg.lower.eta=cfg.upper.eta) (u₁ u₂ v₁ v₂ : Vec2)
    (hu : (JonesOperatorClassification.jonesColMatrix u₁ u₂).det ≠ 0)
    (hv : (JonesOperatorClassification.jonesColMatrix v₁ v₂).det ≠ 0)
    (hn₁ : BIPhysicalFeasibility.isNormalizedJones v₁)
    (hn₂ : BIPhysicalFeasibility.isNormalizedJones v₂)
    (hη : 0 < classPeakEqualEfficiency cfg .BI u₁ u₂ v₁ v₂) :
    let η := classPeakEqualEfficiency cfg .BI u₁ u₂ v₁ v₂
    minimumBudget cfg .BI u₁ u₂ v₁ v₂ (η,η) = completionMinimum cfg u₁ u₂ v₁ v₂ (η,η) ∧
      ∀ S, admissible u₁ u₂ v₁ v₂ (η,η) S → ∃ α β : ℂ,
        efficiency α=η ∧ efficiency β=η ∧
        (asScattering S).t21 = JonesOperatorClassification.jonesColMatrix v₁ v₂ *
          diag2 α β * (JonesOperatorClassification.jonesColMatrix u₁ u₂)⁻¹ ∧
        (asScattering S).t21.det ≠ 0 := by
  exact ⟨minimum_at_class_peak cfg hk heq u₁ u₂ v₁ v₂,
    fun S hS => admissible_frame_transmission cfg S u₁ u₂ v₁ v₂ _ hη hu hv hn₁ hn₂ hS⟩

end GSTC.Scattering.BICompletionMinimum
