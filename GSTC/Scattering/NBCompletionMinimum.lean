/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BICompletionMinimum

public section
set_option autoImplicit false

namespace GSTC.Scattering.NBCompletionMinimum
open BIFeasibility BIPolynomials BIPhysicalFeasibility
open MaterialSpace ClassFeasibility ClassPeakEfficiency
open SusceptibilityBudget ClassMinimumBudget FeasibilityRotation
open MaterialSpace ClassFeasibility ClassPeakEfficiency
open OrthogonalClasses
open scoped Matrix

@[expose] def validParity (P : Ten2 × Ten2) : Prop :=
  P.1.transpose=P.1 ∧ P.2.transpose=P.2 ∧ P.1 ∈ unitary Ten2 ∧ P.2 ∈ unitary Ten2 ∧
  (1+P.1).det ≠ 0 ∧ (1+P.2).det ≠ 0

@[expose] noncomputable def midpoint (P : Ten2 × Ten2) : Ten2 := (1/2 : ℂ) • (P.1+P.2)

@[expose] def admissible (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) (P : Ten2 × Ten2) : Prop :=
  validParity P ∧ cross v₁ (midpoint P *ᵥ u₁)=0 ∧ cross v₂ (midpoint P *ᵥ u₂)=0 ∧
    jonesNormSqR (midpoint P *ᵥ u₁)=η.1 ∧ jonesNormSqR (midpoint P *ᵥ u₂)=η.2

@[expose] noncomputable def recovered (cfg : Config) (P : Ten2 × Ten2) : BIParams :=
  decode (nbSynthesizeParity cfg .above P.1 P.2)

@[expose] noncomputable def completionCost (cfg : Config) (P : Ten2 × Ten2) : ℝ :=
  freeSpaceK0 cfg * max
    (SpectralMatrixSupport.opNorm (electricBlock (assign (recovered cfg P))))
    (SpectralMatrixSupport.opNorm (magneticBlock (assign (recovered cfg P))))

@[expose] noncomputable def completionValues (cfg : Config)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) : Set ℝ :=
  completionCost cfg '' {P | admissible u₁ u₂ v₁ v₂ η P}

@[expose] noncomputable def completionMinimum (cfg : Config)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) : WithTop ℝ :=
  BICompletionMinimum.extendedInf (completionValues cfg u₁ u₂ v₁ v₂ η)

theorem recovered_noCoupling (cfg : Config) (P : Ten2 × Ten2) : NoCoupling (recovered cfg P) := by
  simp [recovered, NoCoupling, decode, nbSynthesizeParity, nbParitySheet, nbSheet, chiTT]

theorem completionCost_eq_spectralTotalBudget (cfg : Config) (P : Ten2 × Ten2) :
    completionCost cfg P = spectralTotalBudget cfg (assign (recovered cfg P)) := by
  have hg : couplingBlock (assign (recovered cfg P)) = 0 := by
    apply (inClass_iff_blocks .NB _).mp
    change NoCoupling (parameters (assign (recovered cfg P)))
    rw [parameters_assign]
    exact recovered_noCoupling cfg P
  have hc : spectralCouplingCost (assign (recovered cfg P)) = 0 :=
    (SpectralMatrixSupport.opNorm_eq_zero_iff _).mpr hg
  rw [spectralTotalBudget, spectralCouplingBudget, hc, mul_zero,
    max_eq_left (spectralDirectBudget_nonneg cfg _)]
  rfl

theorem recovered_forward (cfg : Config) (P : Ten2 × Ten2)
    (hk : cfg.kPar=0) (heq : cfg.lower.eta=cfg.upper.eta) (hp : validParity P) :
    biForwardT cfg (recovered cfg P) = midpoint P := by
  have hmed : identicalMedia cfg .above := by simp [identicalMedia, Wave.medium, heq]
  have hs := nb_synthesis_from_parity cfg .above P.1 P.2 hk hmed
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2
  exact (NBPeakEfficiency.decode_realizer_forward cfg _ _ _ hk heq hs.1 hs.2.1 hs.2.2.1
    (NBPeakEfficiency.paritySheet_tangential cfg .above P.1 P.2) hs.2.2.2.1).2

theorem recovered_feasible (cfg : Config) (P : Ten2 × Ten2)
    (hk : cfg.kPar=0) (heq : cfg.lower.eta=cfg.upper.eta)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) (hp : admissible u₁ u₂ v₁ v₂ η P) :
    assign (recovered cfg P) ∈ classMaterials cfg .NB u₁ u₂ v₁ v₂ η := by
  refine ⟨(conversionMaterials_iff_response cfg _ u₁ u₂ v₁ v₂ η).mpr ?_,?_⟩
  · simpa only [recovered_forward cfg P hk heq hp.1] using hp.2
  · change NoCoupling (parameters (assign (recovered cfg P)))
    rw [parameters_assign]
    exact recovered_noCoupling cfg P

@[expose] noncomputable def electricResponse (cfg : Config) (p : BIParams) : Ten2 :=
  eoResponseScale cfg cfg.upper.eta • p.eeBlock
@[expose] noncomputable def magneticResponse (cfg : Config) (p : BIParams) : Ten2 :=
  moResponseScale cfg cfg.upper.eta • (ncross * (p.mmBlock * ncross))
@[expose] noncomputable def canonicalParity (cfg : Config) (p : BIParams) : Ten2 × Ten2 :=
  (nbCayley (electricResponse cfg p), nbCayley (magneticResponse cfg p))

theorem responses_skew_symmetric (cfg : Config) (p : BIParams) :
    (electricResponse cfg p).conjTranspose = -electricResponse cfg p ∧
    (magneticResponse cfg p).conjTranspose = -magneticResponse cfg p ∧
    (electricResponse cfg p).transpose = electricResponse cfg p ∧
    (magneticResponse cfg p).transpose = magneticResponse cfg p := by
  have hH := (encode_lossless p).chiTT_hermitian
  rw [encode_chiTT_ee, encode_chiTT_mm] at hH
  have hS := nb_reciprocal_TT_symmetric (encode p) (encode_reciprocal p)
  rw [encode_chiTT_ee, encode_chiTT_mm] at hS
  refine ⟨nb_scaled_hermitian_skew _ _ (eoResponseScale_star cfg _) hH.1,
    nb_scaled_hermitian_skew _ _ (moResponseScale_star cfg _) (ncross_mul_hermitian _ hH.2.1),?_,?_⟩
  · simp only [electricResponse, Matrix.transpose_smul, hS.1]
  · ext i j
    change moResponseScale cfg cfg.upper.eta * (ncross * (p.mmBlock * ncross)) j i = _
    rw [ncross_mul_ncross_symmetric _ (fun i j => (congrArg (fun M : Ten2 => M i j) hS.2).symm) j i]
    rfl

theorem canonicalParity_valid (cfg : Config) (p : BIParams) : validParity (canonicalParity cfg p) := by
  have hh := responses_skew_symmetric cfg p
  exact ⟨nbCayley_symmetric _ hh.2.2.1 (nb_one_add_skew_det_ne_zero _ hh.1),
    nbCayley_symmetric _ hh.2.2.2 (nb_one_add_skew_det_ne_zero _ hh.2.1),
    nbCayley_unitary _ hh.1, nbCayley_unitary _ hh.2.1,
    nbCayley_pole_free _ hh.1, nbCayley_pole_free _ hh.2.1⟩

theorem recovered_canonicalParity (cfg : Config) (p : BIParams) (hp : NoCoupling p) :
    recovered cfg (canonicalParity cfg p) = p := by
  have hh := responses_skew_symmetric cfg p
  have he : (cfg.upper.eta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt cfg.upper.eta_pos)
  have hJJ : ncross * ((ncross * (p.mmBlock * ncross)) * ncross) = p.mmBlock := by
    simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_inj] using ncross_mul_neg_ncross_mul p.mmBlock
  have hs : nbSynthesizeParity cfg .above (canonicalParity cfg p).1 (canonicalParity cfg p).2 =
      nbSheet p.eeBlock p.mmBlock := by
    change nbParitySheet cfg cfg.upper.eta
      (nbInvCayley (nbCayley (electricResponse cfg p)))
      (nbInvCayley (nbCayley (magneticResponse cfg p))) = _
    rw [nbInvCayley_nbCayley _ hh.1, nbInvCayley_nbCayley _ hh.2.1]
    simp only [nbParitySheet, electricResponse, magneticResponse, Matrix.mul_smul, Matrix.smul_mul, hJJ,
      smul_smul, inv_mul_cancel₀ (eoResponseScale_ne_zero cfg _ he),
      inv_mul_cancel₀ (moResponseScale_ne_zero cfg _ he), one_smul]
  have henc : nbSheet p.eeBlock p.mmBlock = encode p := by
    rcases hp with ⟨h0,h1,h2,h3⟩
    simp [nbSheet, encode, BIParams.emBlock, BIParams.meBlock, h0,h1,h2,h3]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [recovered, hs, henc, encode_decode]

theorem canonicalParity_admissible (cfg : Config) (p : BIParams)
    (hk : cfg.kPar=0) (heq : cfg.lower.eta=cfg.upper.eta)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hp : assign p ∈ classMaterials cfg .NB u₁ u₂ v₁ v₂ η) :
    admissible u₁ u₂ v₁ v₂ η (canonicalParity cfg p) := by
  have hnc : NoCoupling p := by
    have hh : InClass .NB (parameters (assign p)) := hp.2
    rw [parameters_assign] at hh
    exact hh
  have hf := recovered_forward cfg (canonicalParity cfg p) hk heq (canonicalParity_valid cfg p)
  rw [recovered_canonicalParity cfg p hnc] at hf
  exact ⟨canonicalParity_valid cfg p,
    by simpa only [← hf] using (conversionMaterials_iff_response cfg p u₁ u₂ v₁ v₂ η).mp hp.1⟩

theorem completionValues_eq (cfg : Config) (hk : cfg.kPar=0) (heq : cfg.lower.eta=cfg.upper.eta)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    completionValues cfg u₁ u₂ v₁ v₂ η = budgetValues cfg .NB u₁ u₂ v₁ v₂ η := by
  ext b
  constructor
  · rintro ⟨P,hP,rfl⟩
    exact ⟨assign (recovered cfg P),recovered_feasible cfg P hk heq u₁ u₂ v₁ v₂ η hP,
      (completionCost_eq_spectralTotalBudget cfg P).symm⟩
  · rintro ⟨x,hx,rfl⟩
    have hp : NoCoupling (parameters x) := hx.2
    refine ⟨canonicalParity cfg (parameters x),?_,?_⟩
    · apply canonicalParity_admissible cfg _ hk heq u₁ u₂ v₁ v₂ η
      simpa only [assign_parameters] using hx
    · rw [completionCost_eq_spectralTotalBudget, recovered_canonicalParity cfg _ hp, assign_parameters]

theorem minimum_eq_completionMinimum (cfg : Config) (hk : cfg.kPar=0) (heq : cfg.lower.eta=cfg.upper.eta)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    minimumBudget cfg .NB u₁ u₂ v₁ v₂ η = completionMinimum cfg u₁ u₂ v₁ v₂ η := by
  rw [completionMinimum, completionValues_eq cfg hk heq,
    BICompletionMinimum.materialMinimum_eq_extendedInf]

theorem completion_minimum_attained (cfg : Config) (hk : cfg.kPar=0) (heq : cfg.lower.eta=cfg.upper.eta)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hne : (classMaterials cfg .NB u₁ u₂ v₁ v₂ η).Nonempty) :
    ∃ P : Ten2 × Ten2, admissible u₁ u₂ v₁ v₂ η P ∧
      completionMinimum cfg u₁ u₂ v₁ v₂ η = (completionCost cfg P : WithTop ℝ) ∧
      ∀ P', admissible u₁ u₂ v₁ v₂ η P' → completionCost cfg P ≤ completionCost cfg P' := by
  obtain ⟨x,hx,hm,hmin⟩ := minimumBudget_attained cfg .NB u₁ u₂ v₁ v₂ η hne
  have hp : NoCoupling (parameters x) := hx.2
  have hc : completionCost cfg (canonicalParity cfg (parameters x)) = spectralTotalBudget cfg x := by
    rw [completionCost_eq_spectralTotalBudget, recovered_canonicalParity cfg _ hp, assign_parameters]
  refine ⟨canonicalParity cfg (parameters x),?_,?_,?_⟩
  · apply canonicalParity_admissible cfg _ hk heq u₁ u₂ v₁ v₂ η
    simpa only [assign_parameters] using hx
  · rw [← minimum_eq_completionMinimum cfg hk heq, hc]
    exact hm
  · intro P' hP'
    rw [hc, completionCost_eq_spectralTotalBudget]
    exact hmin _ (recovered_feasible cfg P' hk heq u₁ u₂ v₁ v₂ η hP')

theorem minimum_at_forced_phase_peak (cfg : Config) (hk : cfg.kPar=0)
    (heq : cfg.lower.eta=cfg.upper.eta) (u₁ u₂ v₁ v₂ : Vec2)
    (hn : isNormalizedJones u₁ ∧ isNormalizedJones u₂ ∧ isNormalizedJones v₁ ∧ isNormalizedJones v₂)
    (hu : (JonesOperatorClassification.jonesColMatrix u₁ u₂).det ≠ 0)
    (hs : NBPhaseConstraints.bilinear u₁ v₂ ≠ 0)
    (hcross : ‖NBPhaseConstraints.bilinear u₂ v₁‖ = ‖NBPhaseConstraints.bilinear u₁ v₂‖) :
    let η := (NBPeakEfficiency.spectralNorm (NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂)^2)⁻¹
    minimumBudget cfg .NB u₁ u₂ v₁ v₂ (η,η) = completionMinimum cfg u₁ u₂ v₁ v₂ (η,η) ∧
      ∃ P : Ten2 × Ten2, admissible u₁ u₂ v₁ v₂ (η,η) P ∧
        completionMinimum cfg u₁ u₂ v₁ v₂ (η,η) = (completionCost cfg P : WithTop ℝ) ∧
        ∀ P', admissible u₁ u₂ v₁ v₂ (η,η) P' → completionCost cfg P ≤ completionCost cfg P' := by
  have hp := NBPeakEfficiency.eq25_nb_peak cfg u₁ u₂ v₁ v₂ hk heq hn hu hs hcross
  have hr := hp.2
  unfold classPeakAttained at hr
  rw [hp.1] at hr
  have hne := (classRealizes_iff cfg .NB u₁ u₂ v₁ v₂ _ _ hn.2.2.1 hn.2.2.2).mp hr
  exact ⟨minimum_eq_completionMinimum cfg hk heq u₁ u₂ v₁ v₂ _,
    completion_minimum_attained cfg hk heq u₁ u₂ v₁ v₂ _ hne⟩

@[expose] noncomputable def scaleParity (z : ℂ) (P : Ten2 × Ten2) : Ten2 × Ten2 :=
  (z • P.1,z • P.2)

theorem midpoint_scale (z : ℂ) (P : Ten2 × Ten2) : midpoint (scaleParity z P) = z • midpoint P :=
  NBPhaseConstraints.nb_phase_midpoint P.1 P.2 z

theorem scaleParity_cancel (z : ℂ) (hz : z ≠ 0) (P : Ten2 × Ten2) :
    scaleParity z (scaleParity z⁻¹ P) = P := by
  apply Prod.ext <;> simp only [scaleParity, smul_smul, mul_inv_cancel₀ hz, one_smul]

@[expose] noncomputable def phaseCompletionValues (cfg : Config) (T : Ten2)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) : Set ℝ :=
  {b | ∃ z : ℂ, ∃ P : Ten2 × Ten2, ‖z‖=1 ∧ midpoint P=T ∧
    admissible u₁ u₂ v₁ v₂ η (scaleParity z P) ∧ completionCost cfg (scaleParity z P)=b}

@[expose] noncomputable def phaseCompletionMinimum (cfg : Config) (T : Ten2)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) : WithTop ℝ :=
  BICompletionMinimum.extendedInf (phaseCompletionValues cfg T u₁ u₂ v₁ v₂ η)

open scoped Matrix.Norms.L2Operator in
theorem feasible_forced_peak_phase (cfg : Config) (hk : cfg.kPar=0)
    (heq : cfg.lower.eta=cfg.upper.eta) (u₁ u₂ v₁ v₂ : Vec2)
    (hn : isNormalizedJones u₁ ∧ isNormalizedJones u₂ ∧ isNormalizedJones v₁ ∧ isNormalizedJones v₂)
    (hu : (JonesOperatorClassification.jonesColMatrix u₁ u₂).det ≠ 0)
    (hs : NBPhaseConstraints.bilinear u₁ v₂ ≠ 0)
    (p : BIParams)
    (hp : assign p ∈ classMaterials cfg .NB u₁ u₂ v₁ v₂
      ((NBPeakEfficiency.spectralNorm (NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂)^2)⁻¹,
       (NBPeakEfficiency.spectralNorm (NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂)^2)⁻¹)) :
    ∃ z : ℂ, ‖z‖=1 ∧ biForwardT cfg p = z •
      ((NBPeakEfficiency.spectralNorm (NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂) : ℂ)⁻¹ •
        NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂) := by
  let T₀ := NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂
  let n := NBPeakEfficiency.spectralNorm T₀
  have hnc : NoCoupling p := by
    have hh : InClass .NB (parameters (assign p)) := hp.2
    rwa [parameters_assign] at hh
  obtain ⟨⟨α,h₁,he₁⟩,⟨β,h₂,_⟩⟩ :=
    (conversionMaterials_iff_conversions cfg u₁ u₂ v₁ v₂ _ (assign p) hn.2.2.1 hn.2.2.2).mp hp.1
  simp only [parameters_assign] at h₁ h₂
  have hT := NBPeakEfficiency.forced_operator _ u₁ u₂ v₁ v₂ α β hu hs
    (NBPeakEfficiency.forward_symmetric cfg p hk heq hnc) h₁ h₂
  have hnz : n ≠ 0 := by
    intro hz
    have hm : T₀=0 := norm_eq_zero.mp hz
    have hv : v₁=0 := by
      rw [← (NBPeakEfficiency.forcedTransmission_maps u₁ u₂ v₁ v₂ hu).1]
      change T₀ *ᵥ u₁=0
      rw [hm]; simp
    have hnorm := jonesNormSqR_eq_one_of_normalized hn.2.2.1
    simp [hv,jonesNormSqR_eq] at hnorm
  have hncplx : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnz
  have hzsq : ‖α * (n : ℂ)‖^2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, show Complex.normSq α=(n^2)⁻¹ from he₁,
      Complex.normSq_ofReal]
    field_simp [hnz]
  have hz : ‖α * (n : ℂ)‖=1 := by nlinarith [norm_nonneg (α * (n : ℂ))]
  refine ⟨α * (n : ℂ),hz,?_⟩
  rw [hT]
  change α • T₀ = (α * (n : ℂ)) • ((n : ℂ)⁻¹ • T₀)
  simp only [smul_smul, mul_assoc, mul_inv_cancel₀ hncplx, mul_one]

theorem phaseCompletionValues_at_forced_peak (cfg : Config) (hk : cfg.kPar=0)
    (heq : cfg.lower.eta=cfg.upper.eta) (u₁ u₂ v₁ v₂ : Vec2)
    (hn : isNormalizedJones u₁ ∧ isNormalizedJones u₂ ∧ isNormalizedJones v₁ ∧ isNormalizedJones v₂)
    (hu : (JonesOperatorClassification.jonesColMatrix u₁ u₂).det ≠ 0)
    (hs : NBPhaseConstraints.bilinear u₁ v₂ ≠ 0) :
    let T₀ := NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂
    let n := NBPeakEfficiency.spectralNorm T₀
    let η := (n^2)⁻¹
    phaseCompletionValues cfg ((n : ℂ)⁻¹ • T₀) u₁ u₂ v₁ v₂ (η,η) =
      completionValues cfg u₁ u₂ v₁ v₂ (η,η) := by
  dsimp only
  ext b
  constructor
  · rintro ⟨z,P,_,_,hP,hc⟩
    exact ⟨scaleParity z P,hP,hc⟩
  · rintro ⟨P,hP,rfl⟩
    have hf := recovered_feasible cfg P hk heq u₁ u₂ v₁ v₂ _ hP
    obtain ⟨z,hz,hT⟩ := feasible_forced_peak_phase cfg hk heq u₁ u₂ v₁ v₂ hn hu hs _ hf
    have hnz : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
    refine ⟨z,scaleParity z⁻¹ P,hz,?_,?_,?_⟩
    · rw [midpoint_scale, ← recovered_forward cfg P hk heq hP.1, hT,
        smul_smul, inv_mul_cancel₀ hnz, one_smul]
    · rw [scaleParity_cancel z hnz P]
      exact hP
    · rw [scaleParity_cancel z hnz P]

theorem minimum_eq_phaseCompletionMinimum_at_peak (cfg : Config) (hk : cfg.kPar=0)
    (heq : cfg.lower.eta=cfg.upper.eta) (u₁ u₂ v₁ v₂ : Vec2)
    (hn : isNormalizedJones u₁ ∧ isNormalizedJones u₂ ∧ isNormalizedJones v₁ ∧ isNormalizedJones v₂)
    (hu : (JonesOperatorClassification.jonesColMatrix u₁ u₂).det ≠ 0)
    (hs : NBPhaseConstraints.bilinear u₁ v₂ ≠ 0)
    (hcross : ‖NBPhaseConstraints.bilinear u₂ v₁‖ = ‖NBPhaseConstraints.bilinear u₁ v₂‖) :
    let T₀ := NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂
    let n := NBPeakEfficiency.spectralNorm T₀
    let η := (n^2)⁻¹
    classPeakEqualEfficiency cfg .NB u₁ u₂ v₁ v₂ = η ∧
    minimumBudget cfg .NB u₁ u₂ v₁ v₂ (η,η) =
      phaseCompletionMinimum cfg ((n : ℂ)⁻¹ • T₀) u₁ u₂ v₁ v₂ (η,η) := by
  dsimp only
  refine ⟨(NBPeakEfficiency.eq25_nb_peak cfg u₁ u₂ v₁ v₂ hk heq hn hu hs hcross).1,?_⟩
  rw [phaseCompletionMinimum, phaseCompletionValues_at_forced_peak cfg hk heq u₁ u₂ v₁ v₂ hn hu hs]
  exact minimum_eq_completionMinimum cfg hk heq u₁ u₂ v₁ v₂ _

theorem phaseCompletion_minimum_attained_at_peak (cfg : Config) (hk : cfg.kPar=0)
    (heq : cfg.lower.eta=cfg.upper.eta) (u₁ u₂ v₁ v₂ : Vec2)
    (hn : isNormalizedJones u₁ ∧ isNormalizedJones u₂ ∧ isNormalizedJones v₁ ∧ isNormalizedJones v₂)
    (hu : (JonesOperatorClassification.jonesColMatrix u₁ u₂).det ≠ 0)
    (hs : NBPhaseConstraints.bilinear u₁ v₂ ≠ 0)
    (hcross : ‖NBPhaseConstraints.bilinear u₂ v₁‖ = ‖NBPhaseConstraints.bilinear u₁ v₂‖) :
    let T₀ := NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂
    let n := NBPeakEfficiency.spectralNorm T₀
    let Tstar := (n : ℂ)⁻¹ • T₀
    let η := (n^2)⁻¹
    ∃ z : ℂ, ∃ P : Ten2 × Ten2, ‖z‖=1 ∧ midpoint P=Tstar ∧
      admissible u₁ u₂ v₁ v₂ (η,η) (scaleParity z P) ∧
      phaseCompletionMinimum cfg Tstar u₁ u₂ v₁ v₂ (η,η) =
        (completionCost cfg (scaleParity z P) : WithTop ℝ) ∧
      ∀ Q, admissible u₁ u₂ v₁ v₂ (η,η) Q →
        completionCost cfg (scaleParity z P) ≤ completionCost cfg Q := by
  dsimp only
  let η := (NBPeakEfficiency.spectralNorm (NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂)^2)⁻¹
  obtain ⟨Q,hQ,hm,hmin⟩ := (minimum_at_forced_phase_peak cfg hk heq u₁ u₂ v₁ v₂ hn hu hs hcross).2
  have hv : completionCost cfg Q ∈ phaseCompletionValues cfg
      ((NBPeakEfficiency.spectralNorm (NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂) : ℂ)⁻¹ •
        NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂) u₁ u₂ v₁ v₂ (η,η) := by
    rw [phaseCompletionValues_at_forced_peak cfg hk heq u₁ u₂ v₁ v₂ hn hu hs]
    exact ⟨Q,hQ,rfl⟩
  obtain ⟨z,P,hz,hmid,hP,hc⟩ := hv
  refine ⟨z,P,hz,hmid,hP,?_,?_⟩
  · rw [phaseCompletionMinimum, phaseCompletionValues_at_forced_peak cfg hk heq u₁ u₂ v₁ v₂ hn hu hs]
    change completionMinimum cfg u₁ u₂ v₁ v₂ (η,η) = _
    rw [hm,hc]
  · intro Q' hQ'
    rw [hc]
    exact hmin Q' hQ'

theorem forcedTransmission_nonsingular (u₁ u₂ v₁ v₂ : Vec2)
    (hu : (JonesOperatorClassification.jonesColMatrix u₁ u₂).det ≠ 0)
    (hv : (JonesOperatorClassification.jonesColMatrix v₁ v₂).det ≠ 0)
    (hs : NBPhaseConstraints.bilinear u₁ v₂ ≠ 0)
    (hcross : ‖NBPhaseConstraints.bilinear u₂ v₁‖ = ‖NBPhaseConstraints.bilinear u₁ v₂‖) :
    (NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂).det ≠ 0 := by
  have hr : NBPhaseConstraints.bilinear u₂ v₁ ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at hcross
    exact (norm_ne_zero_iff.mpr hs) hcross.symm
  rw [NBPeakEfficiency.forcedTransmission_paper, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  apply mul_ne_zero (mul_ne_zero hv ?_) (inv_ne_zero hu)
  simp [diag2, Matrix.det_fin_two, div_ne_zero hr hs]

theorem minimum_at_nonsingular_forced_peak (cfg : Config) (hk : cfg.kPar=0)
    (heq : cfg.lower.eta=cfg.upper.eta) (u₁ u₂ v₁ v₂ : Vec2)
    (hn : isNormalizedJones u₁ ∧ isNormalizedJones u₂ ∧ isNormalizedJones v₁ ∧ isNormalizedJones v₂)
    (hu : (JonesOperatorClassification.jonesColMatrix u₁ u₂).det ≠ 0)
    (hv : (JonesOperatorClassification.jonesColMatrix v₁ v₂).det ≠ 0)
    (hs : NBPhaseConstraints.bilinear u₁ v₂ ≠ 0)
    (hcross : ‖NBPhaseConstraints.bilinear u₂ v₁‖ = ‖NBPhaseConstraints.bilinear u₁ v₂‖) :
    let T₀ := NBPeakEfficiency.forcedTransmission u₁ u₂ v₁ v₂
    let n := NBPeakEfficiency.spectralNorm T₀
    let η := (n^2)⁻¹
    T₀.det ≠ 0 ∧ classPeakEqualEfficiency cfg .NB u₁ u₂ v₁ v₂ = η ∧
      minimumBudget cfg .NB u₁ u₂ v₁ v₂ (η,η) =
        phaseCompletionMinimum cfg ((n : ℂ)⁻¹ • T₀) u₁ u₂ v₁ v₂ (η,η) := by
  exact ⟨forcedTransmission_nonsingular u₁ u₂ v₁ v₂ hu hv hs hcross,
    minimum_eq_phaseCompletionMinimum_at_peak cfg hk heq u₁ u₂ v₁ v₂ hn hu hs hcross⟩

end GSTC.Scattering.NBCompletionMinimum
