/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.ClassMinimumBudget
public import GSTC.Scattering.JonesOperatorClassification

public section
set_option autoImplicit false

namespace GSTC.Scattering.FeasibilityRotation
open BIFeasibility BIPolynomials   SusceptibilityBudget
open MaterialSpace ClassFeasibility ClassPeakEfficiency
open ClassMinimumBudget
open scoped Matrix

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ

@[expose] def blocks4 (A B C D : Ten2) : Mat4 :=
  !![A 0 0, A 0 1, B 0 0, B 0 1;
     A 1 0, A 1 1, B 1 0, B 1 1;
     C 0 0, C 0 1, D 0 0, D 0 1;
     C 1 0, C 1 1, D 1 0, D 1 1]

@[expose] def portLift (Q : Ten2) : Mat4 := blocks4 Q 0 0 Q

theorem portLift_mul (Q P : Ten2) : portLift (Q*P) = portLift Q * portLift P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [portLift, blocks4, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem portLift_one : portLift 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem portLift_transpose (Q : Ten2) : portLift Q.transpose = (portLift Q).transpose := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem blocks4_conjugation (Q A B C D : Ten2) :
    blocks4 (Q.transpose*A*Q) (Q.transpose*B*Q) (Q.transpose*C*Q) (Q.transpose*D*Q) =
      (portLift Q).transpose * blocks4 A B C D * portLift Q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blocks4, portLift, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem constitutiveH_blocks (cfg : Config) (p : BIParams) :
    biConstitutiveH cfg p = blocks4
      ((cfg.vac.eps0 : ℂ) • p.eeBlock)
      ((Complex.I / (cfg.vac.c0 : ℂ)) • BIRotation.gBlock p)
      ((-Complex.I / (cfg.vac.c0 : ℂ)) • (BIRotation.gBlock p).transpose)
      ((cfg.vac.mu0 : ℂ) • p.mmBlock) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [biConstitutiveH, blocks4, BIParams.eeBlock, BIParams.mmBlock,
      BIRotation.gBlock, div_eq_mul_inv] <;> ring

theorem constitutiveH_rotate (cfg : Config) (γ : ℝ) (p : BIParams) :
    biConstitutiveH cfg (BIRotation.rotateParams γ p) =
      (portLift (TransverseRotation.rotation γ)).transpose * biConstitutiveH cfg p *
        portLift (TransverseRotation.rotation γ) := by
  rw [constitutiveH_blocks, constitutiveH_blocks,
    BIRotation.rotateParams_eeBlock, BIRotation.rotateParams_mmBlock,
    BIRotation.rotateParams_gBlock]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] using
    blocks4_conjugation (TransverseRotation.rotation γ)
      ((cfg.vac.eps0 : ℂ) • p.eeBlock)
      ((Complex.I / (cfg.vac.c0 : ℂ)) • BIRotation.gBlock p)
      ((-Complex.I / (cfg.vac.c0 : ℂ)) • (BIRotation.gBlock p).transpose)
      ((cfg.vac.mu0 : ℂ) • p.mmBlock)

theorem rotation_orthogonal (γ : ℝ) :
    (TransverseRotation.rotation γ).transpose * TransverseRotation.rotation γ = 1 ∧
    TransverseRotation.rotation γ * (TransverseRotation.rotation γ).transpose = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [TransverseRotation.rotation, Matrix.mul_apply, Fin.sum_univ_two,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    norm_cast <;> nlinarith [Real.sin_sq_add_cos_sq γ]

theorem portRotation_orthogonal (γ : ℝ) :
    (portLift (TransverseRotation.rotation γ)).transpose * portLift (TransverseRotation.rotation γ) = 1 ∧
    portLift (TransverseRotation.rotation γ) * (portLift (TransverseRotation.rotation γ)).transpose = 1 := by
  constructor
  · rw [← portLift_transpose, ← portLift_mul, (rotation_orthogonal γ).1, portLift_one]
  · rw [← portLift_transpose, ← portLift_mul, (rotation_orthogonal γ).2, portLift_one]

theorem portRotation_star (γ : ℝ) :
    (portLift (TransverseRotation.rotation γ)).conjTranspose =
      (portLift (TransverseRotation.rotation γ)).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [portLift, blocks4, TransverseRotation.rotation, Matrix.conjTranspose_apply,
      -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem midpointMap_commutes (cfg : Config) (γ : ℝ) :
    biMidpointMap4 cfg * portLift (TransverseRotation.rotation γ) =
      portLift (TransverseRotation.rotation γ) * biMidpointMap4 cfg := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [biMidpointMap4, portLift, blocks4, TransverseRotation.rotation,
      Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem constitutiveK_rotate (cfg : Config) (γ : ℝ) (p : BIParams) :
    biConstitutiveK cfg (BIRotation.rotateParams γ p) =
      (portLift (TransverseRotation.rotation γ)).transpose * biConstitutiveK cfg p *
        portLift (TransverseRotation.rotation γ) := by
  let L := portLift (TransverseRotation.rotation γ)
  let F := biMidpointMap4 cfg
  have hf : F * L = L * F := midpointMap_commutes cfg γ
  have hs : F.conjTranspose * L.transpose = L.transpose * F.conjTranspose := by
    have hh := congrArg Matrix.conjTranspose hf
    simpa only [Matrix.conjTranspose_mul, L, portRotation_star] using hh.symm
  have he : F.conjTranspose * (L.transpose * biConstitutiveH cfg p * L) * F =
      L.transpose * (F.conjTranspose * biConstitutiveH cfg p * F) * L := by
    calc _ = (F.conjTranspose * L.transpose) * biConstitutiveH cfg p * (L*F) := by
           simp only [Matrix.mul_assoc]
         _ = (L.transpose * F.conjTranspose) * biConstitutiveH cfg p * (F*L) := by rw [hs,hf]
         _ = _ := by simp only [Matrix.mul_assoc]
  unfold biConstitutiveK
  rw [constitutiveH_rotate]
  change (-2 * (cfg.omega : ℂ)) • _ = _
  rw [he]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rfl

theorem inverse_conjugation (Q M : Mat4) (hl : Q.transpose*Q=1) (hr : Q*Q.transpose=1) :
    (Q.transpose * M * Q)⁻¹ = Q.transpose * M⁻¹ * Q := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.inv_eq_left_inv hl, Matrix.inv_eq_left_inv hr, Matrix.mul_assoc]

theorem cayley4_conjugation (Q K : Mat4) (hl : Q.transpose*Q=1) (hr : Q*Q.transpose=1) :
    cayley4 (Q.transpose*K*Q) = Q.transpose * cayley4 K * Q := by
  have hd : 2 • (1 : Mat4) - Complex.I • (Q.transpose*K*Q) =
      Q.transpose * (2 • (1 : Mat4) - Complex.I • K) * Q := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hl]
  have hn : 2 • (1 : Mat4) + Complex.I • (Q.transpose*K*Q) =
      Q.transpose * (2 • (1 : Mat4) + Complex.I • K) * Q := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hl]
  unfold cayley4
  rw [hd,hn,inverse_conjugation Q _ hl hr]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q Q.transpose, hr, Matrix.one_mul]

theorem parityExchange_commutes (Q : Ten2) :
    parityExchange * portLift Q = portLift Q * parityExchange := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parityExchange, portLift, blocks4, Matrix.mul_apply, Fin.sum_univ_four]

theorem powerResponse_rotate (cfg : Config) (γ : ℝ) (p : BIParams) :
    biPowerResponse4 cfg (BIRotation.rotateParams γ p) =
      (portLift (TransverseRotation.rotation γ)).transpose * biPowerResponse4 cfg p *
        portLift (TransverseRotation.rotation γ) := by
  unfold biPowerResponse4
  rw [constitutiveK_rotate, cayley4_conjugation _ _
    (portRotation_orthogonal γ).1 (portRotation_orthogonal γ).2]
  have hp : parityExchange * (portLift (TransverseRotation.rotation γ)).transpose =
      (portLift (TransverseRotation.rotation γ)).transpose * parityExchange := by
    simpa only [portLift_transpose] using parityExchange_commutes (TransverseRotation.rotation γ).transpose
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc parityExchange, hp]
  simp only [Matrix.mul_assoc]

theorem forwardTransmission_rotate (cfg : Config) (γ : ℝ) (p : BIParams) :
    biForwardT cfg (BIRotation.rotateParams γ p) =
      (TransverseRotation.rotation γ).transpose * biForwardT cfg p * TransverseRotation.rotation γ := by
  have h := powerResponse_rotate cfg γ p
  unfold biForwardT
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [portLift, blocks4, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

@[expose] noncomputable def rotateJones (γ : ℝ) (u : Vec2) : Vec2 :=
  (TransverseRotation.rotation γ).transpose *ᵥ u

@[expose] noncomputable def rotateCoordinates (γ : ℝ) (x : MaterialCoordinates) : MaterialCoordinates :=
  assign (BIRotation.rotateParams γ (parameters x))

theorem forward_action_rotate (cfg : Config) (γ : ℝ) (p : BIParams) (u : Vec2) :
    biForwardT cfg (BIRotation.rotateParams γ p) *ᵥ rotateJones γ u =
      rotateJones γ (biForwardT cfg p *ᵥ u) := by
  rw [forwardTransmission_rotate]
  simp only [rotateJones, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec u
    (TransverseRotation.rotation γ) (TransverseRotation.rotation γ).transpose,
    (rotation_orthogonal γ).2, Matrix.one_mulVec]

theorem rotation_star (γ : ℝ) : (TransverseRotation.rotation γ).conjTranspose =
    (TransverseRotation.rotation γ).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TransverseRotation.rotation, Matrix.conjTranspose_apply,
      -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem rotateJones_normSq (γ : ℝ) (u : Vec2) :
    jonesNormSqR (rotateJones γ u) = jonesNormSqR u := by
  have hu : (TransverseRotation.rotation γ).transpose ∈ unitary Ten2 := by
    apply Unitary.mem_iff.mpr
    constructor
    · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
        rotation_star, Matrix.transpose_transpose] using (rotation_orthogonal γ).2
    · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
        rotation_star, Matrix.transpose_transpose] using (rotation_orthogonal γ).1
  exact congrArg Complex.re (JonesOperatorClassification.jonesInner_of_jonesUnitary
    ((JonesOperatorClassification.jonesUnitary_iff_mem_unitary _).mpr hu) u u)

@[expose] def cross (v w : Vec2) : ℂ := v 0*w 1-v 1*w 0

theorem cross_mulVec (Q : Ten2) (v w : Vec2) :
    cross (Q *ᵥ v) (Q *ᵥ w) = Q.det * cross v w := by
  simp [cross, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem rotateJones_cross_zero_iff (γ : ℝ) (v w : Vec2) :
    cross (rotateJones γ v) (rotateJones γ w) = 0 ↔ cross v w = 0 := by
  rw [rotateJones, rotateJones, cross_mulVec, Matrix.det_transpose, mul_eq_zero]
  simp [Matrix.det_ne_zero_of_left_inverse (rotation_orthogonal γ).1]

open BIAmplitudeFree

theorem stateEfficiency_eq_norm (cfg : Config) (p : BIParams) (u : Vec2) :
    stateEfficiency cfg u (assign p) = jonesNormSqR (biForwardT cfg p *ᵥ u) := by
  unfold stateEfficiency
  rw [effPoly_eval, denominatorPower_eval, zero_mul, sub_zero,
    ← biDet_mul_forwardT, Matrix.smul_mulVec, jonesNormSqR_smul]
  exact mul_div_cancel_left₀ _ (fun h => biDet_ne_zero cfg p (Complex.normSq_eq_zero.mp h))

theorem collinearCoordinates_iff_cross (cfg : Config) (p : BIParams) (u v : Vec2) :
    assign p ∈ collinearCoordinates cfg u v ↔ cross v (biForwardT cfg p *ᵥ u) = 0 := by
  change ((collinearityPoly cfg u v).re.eval (assign p) = 0 ∧
    (collinearityPoly cfg u v).im.eval (assign p) = 0) ↔ _
  rw [← collinearityPoly_eq_zero_iff, collinearityPoly_eval,
    ← biDet_mul_forwardT, Matrix.smul_mulVec]
  have he (d : ℂ) (w : Vec2) : v 0*(d • w) 1-v 1*(d • w) 0 = d*cross v w := by
    simp [cross]; ring
  rw [he, mul_eq_zero]
  simp [biDet_ne_zero cfg p]

theorem conversionMaterials_iff_response (cfg : Config) (p : BIParams)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    assign p ∈ conversionMaterials cfg u₁ u₂ v₁ v₂ η ↔
      cross v₁ (biForwardT cfg p *ᵥ u₁) = 0 ∧
      cross v₂ (biForwardT cfg p *ᵥ u₂) = 0 ∧
      jonesNormSqR (biForwardT cfg p *ᵥ u₁) = η.1 ∧
      jonesNormSqR (biForwardT cfg p *ᵥ u₂) = η.2 := by
  rcases η with ⟨η₁,η₂⟩
  simp only [conversionMaterials, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    collinearCoordinates_iff_cross, efficiencyPair, Prod.mk.injEq, stateEfficiency_eq_norm]
  tauto

theorem conversionMaterials_rotate_iff (cfg : Config) (γ : ℝ) (p : BIParams)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    assign (BIRotation.rotateParams γ p) ∈ conversionMaterials cfg
        (rotateJones γ u₁) (rotateJones γ u₂) (rotateJones γ v₁) (rotateJones γ v₂) η ↔
      assign p ∈ conversionMaterials cfg u₁ u₂ v₁ v₂ η := by
  rw [conversionMaterials_iff_response, conversionMaterials_iff_response]
  simp only [forward_action_rotate, rotateJones_cross_zero_iff, rotateJones_normSq]

theorem couplingBlock_zero_iff (x : MaterialCoordinates) :
    couplingBlock x = 0 ↔ x .g00 = 0 ∧ x .g01 = 0 ∧ x .g10 = 0 ∧ x .g11 = 0 := by
  constructor
  · intro h
    exact ⟨congrArg (fun M : SpectralMatrixSupport.Mat => M 0 0) h,
      congrArg (fun M : SpectralMatrixSupport.Mat => M 0 1) h,
      congrArg (fun M : SpectralMatrixSupport.Mat => M 1 0) h,
      congrArg (fun M : SpectralMatrixSupport.Mat => M 1 1) h⟩
  · rintro ⟨h0,h1,h2,h3⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [couplingBlock,h0,h1,h2,h3]

theorem magneticBlock_zero_iff (x : MaterialCoordinates) :
    magneticBlock x = 0 ↔ x .mm00 = 0 ∧ x .mm01 = 0 ∧ x .mm11 = 0 := by
  constructor
  · intro h
    exact ⟨congrArg (fun M : SpectralMatrixSupport.Mat => M 0 0) h,
      congrArg (fun M : SpectralMatrixSupport.Mat => M 0 1) h,
      congrArg (fun M : SpectralMatrixSupport.Mat => M 1 1) h⟩
  · rintro ⟨h0,h1,h2⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [magneticBlock,h0,h1,h2]

theorem inClass_iff_blocks (c : SheetClass) (x : MaterialCoordinates) :
    InClass c (parameters x) ↔ match c with
      | .E => magneticBlock x = 0 ∧ couplingBlock x = 0
      | .NB => couplingBlock x = 0
      | .BI => True := by
  cases c <;>
    simp [InClass, ElectricOnly, NoCoupling, parameters, couplingBlock_zero_iff,
      magneticBlock_zero_iff, and_assoc]

theorem conjugate_zero_iff (Q M : SpectralMatrixSupport.Mat) (hQ : Q.transpose*Q=1) :
    Q*M*Q.transpose = 0 ↔ M = 0 := by
  rw [← SpectralMatrixSupport.opNorm_eq_zero_iff,
    SpectralMatrixSupport.opNorm_orthogonal_conjugation M Q hQ,
    SpectralMatrixSupport.opNorm_eq_zero_iff]

theorem inClass_conjugate_iff (c : SheetClass) (Q : SpectralMatrixSupport.Mat)
    (hQ : Q.transpose*Q=1) (x : MaterialCoordinates) :
    InClass c (parameters (conjugateCoordinates Q x)) ↔ InClass c (parameters x) := by
  rw [inClass_iff_blocks, inClass_iff_blocks]
  have hh := blocks_conjugateCoordinates Q x
  cases c <;> simp only [hh.2.1, hh.2.2, conjugate_zero_iff Q _ hQ]

theorem inClass_rotate_iff (c : SheetClass) (γ : ℝ) (p : BIParams) :
    InClass c (BIRotation.rotateParams γ p) ↔ InClass c p := by
  have hh := inClass_conjugate_iff c (realRotation γ).transpose
    (by simpa using (realRotation_orthogonal γ).2) (assign p)
  rw [← rotateParams_eq_conjugate, parameters_assign, parameters_assign] at hh
  exact hh

theorem classMaterials_rotate_iff (cfg : Config) (c : SheetClass) (γ : ℝ) (p : BIParams)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    assign (BIRotation.rotateParams γ p) ∈ classMaterials cfg c
        (rotateJones γ u₁) (rotateJones γ u₂) (rotateJones γ v₁) (rotateJones γ v₂) η ↔
      assign p ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η := by
  simp only [mem_classMaterials_iff, parameters_assign,
    conversionMaterials_rotate_iff, inClass_rotate_iff]

theorem realRotation_neg (γ : ℝ) : realRotation (-γ) = (realRotation γ).transpose := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [realRotation]

theorem rotation_neg (γ : ℝ) : TransverseRotation.rotation (-γ) = (TransverseRotation.rotation γ).transpose := by
  rw [← complexify_realRotation, realRotation_neg, complexify_transpose, complexify_realRotation]

theorem rotateJones_inverse (γ : ℝ) (u : Vec2) : rotateJones (-γ) (rotateJones γ u) = u := by
  simp only [rotateJones, rotation_neg, Matrix.transpose_transpose,
    Matrix.mulVec_mulVec, (rotation_orthogonal γ).2, Matrix.one_mulVec]

theorem classMaterials_rotateCoordinates_iff (cfg : Config) (c : SheetClass) (γ : ℝ)
    (x : MaterialCoordinates) (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    rotateCoordinates γ x ∈ classMaterials cfg c
        (rotateJones γ u₁) (rotateJones γ u₂) (rotateJones γ v₁) (rotateJones γ v₂) η ↔
      x ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η := by
  simpa only [rotateCoordinates, assign_parameters] using
    classMaterials_rotate_iff cfg c γ (parameters x) u₁ u₂ v₁ v₂ η

theorem spectralBudget_rotateCoordinates (cfg : Config) (γ : ℝ) (x : MaterialCoordinates) :
    spectralTotalBudget cfg (rotateCoordinates γ x) = spectralTotalBudget cfg x := by
  simpa only [rotateCoordinates, assign_parameters] using
    (spectralBudgets_rotateParams cfg γ (parameters x)).2.2

theorem budgetValues_rotate (cfg : Config) (c : SheetClass) (γ : ℝ)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    budgetValues cfg c (rotateJones γ u₁) (rotateJones γ u₂)
      (rotateJones γ v₁) (rotateJones γ v₂) η = budgetValues cfg c u₁ u₂ v₁ v₂ η := by
  ext b
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨rotateCoordinates (-γ) x,?_,spectralBudget_rotateCoordinates cfg (-γ) x⟩
    have hh := (classMaterials_rotateCoordinates_iff cfg c (-γ) x
      (rotateJones γ u₁) (rotateJones γ u₂) (rotateJones γ v₁) (rotateJones γ v₂) η).mpr hx
    simpa only [rotateJones_inverse] using hh
  · rintro ⟨x,hx,rfl⟩
    exact ⟨rotateCoordinates γ x,
      (classMaterials_rotateCoordinates_iff cfg c γ x u₁ u₂ v₁ v₂ η).mpr hx,
      spectralBudget_rotateCoordinates cfg γ x⟩

theorem classMaterials_nonempty_rotate_iff (cfg : Config) (c : SheetClass) (γ : ℝ)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    (classMaterials cfg c (rotateJones γ u₁) (rotateJones γ u₂)
      (rotateJones γ v₁) (rotateJones γ v₂) η).Nonempty ↔
      (classMaterials cfg c u₁ u₂ v₁ v₂ η).Nonempty := by
  have himage (S : Set MaterialCoordinates) :
      (spectralTotalBudget cfg '' S).Nonempty ↔ S.Nonempty := Set.image_nonempty
  rw [← himage, ← himage]
  change (budgetValues cfg c _ _ _ _ η).Nonempty ↔ (budgetValues cfg c _ _ _ _ η).Nonempty
  rw [budgetValues_rotate]

theorem minimumBudget_rotate (cfg : Config) (c : SheetClass) (γ : ℝ)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    minimumBudget cfg c (rotateJones γ u₁) (rotateJones γ u₂)
      (rotateJones γ v₁) (rotateJones γ v₂) η = minimumBudget cfg c u₁ u₂ v₁ v₂ η := by
  unfold minimumBudget
  rw [propext (classMaterials_nonempty_rotate_iff cfg c γ u₁ u₂ v₁ v₂ η)]
  simp only [finiteMinimumBudget, budgetValues_rotate]

end GSTC.Scattering.FeasibilityRotation
