/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.ClassPeakEfficiency
public import GSTC.Scattering.JonesOperatorClassification
public import GSTC.Scattering.NBTakagiExistence

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Algebra.Polynomial.Roots

public section

set_option autoImplicit false

namespace GSTC.Scattering.NBPeakEfficiency

open scoped Matrix
open BIFeasibility OrthogonalClasses

theorem forward_eq_of_encoded_gstc (cfg : Config) (p : BIParams) (T R : Ten2)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hc : nbClass (encode p))
    (hT : ∀ a, gstcSatisfied cfg .above (encode p) a (R *ᵥ a) (T *ᵥ a)) :
    biForwardT cfg p = T := by
  have hmed : identicalMedia cfg .above := by simp [identicalMedia, Wave.medium, heq]
  have hz : (Real.sqrt cfg.upper.eta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 cfg.upper.eta_pos))
  apply Matrix.ext_iff_mulVec.mpr
  intro a
  have hh := lossless_outgoing_unique cfg .above (encode p)
    ((Real.sqrt cfg.upper.eta : ℂ) • a)
    ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardR cfg p *ᵥ a))
    ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardT cfg p *ᵥ a))
    (R *ᵥ ((Real.sqrt cfg.upper.eta : ℂ) • a))
    (T *ᵥ ((Real.sqrt cfg.upper.eta : ℂ) • a))
    hk (encode_lossless p) hc.1 hc.2 hmed
    (gstc_above_of_forward cfg p hk heq a) (hT _)
  have ht := hh.2
  rw [Matrix.mulVec_smul] at ht
  funext i
  exact mul_left_cancel₀ hz (congrFun ht i)

theorem encoded_realizes_forward (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hc : nbClass (encode p)) :
    NBRealizes cfg .above (biForwardT cfg p) := by
  have hz : (Real.sqrt cfg.upper.eta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 cfg.upper.eta_pos))
  refine ⟨encode p, hc, encode_lossless p, encode_reciprocal p, biForwardR cfg p, ?_⟩
  intro a
  have hh := gstc_above_of_forward cfg p hk heq
    ((Real.sqrt cfg.upper.eta : ℂ)⁻¹ • a)
  simpa only [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hz, one_smul] using hh

theorem nbClass_encode_of_noCoupling (p : BIParams) (hp : NoCoupling p) :
    nbClass (encode p) := by
  rcases hp with ⟨h00,h01,h10,h11⟩
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [encode, chiTT, ten3OfTT, BIParams.emBlock, BIParams.meBlock,
      h00,h01,h10,h11]

theorem forward_symmetric (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hp : NoCoupling p) :
    (biForwardT cfg p).transpose = biForwardT cfg p := by
  apply nb_realizes_symmetric cfg .above _ hk
    (by simp [identicalMedia, Wave.medium, heq])
  exact encoded_realizes_forward cfg p hk heq (nbClass_encode_of_noCoupling p hp)

theorem decode_realizer_forward (cfg : Config) (sus : Susceptibilities) (T R : Ten2)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hc : nbClass sus) (hl : sus.Lossless) (hr : sus.Reciprocal)
    (ht : Tangential sus)
    (hg : ∀ a, gstcSatisfied cfg .above sus a (R *ᵥ a) (T *ᵥ a)) :
    NoCoupling (decode sus) ∧ biForwardT cfg (decode sus) = T := by
  have he : encode (decode sus) = sus := decode_encode sus hr hl ht
  constructor
  · simp [NoCoupling, decode, hc.1]
  · apply forward_eq_of_encoded_gstc cfg (decode sus) T R hk heq
    · rwa [he]
    · rwa [he]

theorem paritySheet_tangential (cfg : Config) (side : Side) (X Y : Ten2) :
    Tangential (nbSynthesizeParity cfg side X Y) := by
  simp [Tangential, nbSynthesizeParity, nbParitySheet, nbSheet,
    chiTT, ten3OfTT]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem parity_synthesis_material (cfg : Config) (X Y : Ten2)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hxs : X.transpose = X) (hys : Y.transpose = Y)
    (hx : X ∈ unitary Ten2) (hy : Y ∈ unitary Ten2)
    (hpx : (1+X).det ≠ 0) (hpy : (1+Y).det ≠ 0) :
    ∃ p : BIParams, NoCoupling p ∧
      biForwardT cfg p = (1/2 : ℂ) • (X+Y) := by
  have hmed : identicalMedia cfg .above := by simp [identicalMedia, Wave.medium, heq]
  have hs := nb_synthesis_from_parity cfg .above X Y hk hmed hxs hys hx hy hpx hpy
  exact ⟨decode (nbSynthesizeParity cfg .above X Y),
    decode_realizer_forward cfg _ _ _ hk heq hs.1 hs.2.1 hs.2.2.1
      (paritySheet_tangential cfg .above X Y) hs.2.2.2.1⟩

section SpectralNorm
open scoped Matrix.Norms.L2Operator

@[expose] noncomputable def spectralNorm (T : Ten2) : ℝ := ‖T‖

theorem spectralNorm_smul (c : ℂ) (T : Ten2) :
    spectralNorm (c • T) = ‖c‖ * spectralNorm T := norm_smul c T

theorem spectralNorm_takagi {T : Ten2} (C : Takagi2 T) :
    spectralNorm T = C.s1 := by
  have hqt : C.Q.transpose ∈ unitary Ten2 := by
    apply Unitary.mem_iff.mpr
    constructor
    · simpa only [Matrix.star_eq_conjTranspose, Matrix.transpose_conjTranspose]
        using unitary_conj_transpose C.Q C.hQ
    · simpa only [Matrix.star_eq_conjTranspose, Matrix.transpose_conjTranspose]
        using unitary_transpose_conj C.Q C.hQ
  change ‖T‖ = C.s1
  conv_lhs => rw [C.hT]
  rw [CStarRing.norm_mul_mem_unitary _ hqt,
    CStarRing.norm_mem_unitary_mul _ C.hQ]
  have hd : diagR C.s1 C.s2 = Matrix.diagonal ![(C.s1 : ℂ),(C.s2 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagR, Matrix.diagonal]
  rw [hd, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg C.hs1).mpr
    intro i
    fin_cases i
    · simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg C.hs1]
    · simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg C.hs2] using C.hs2le
  · have h := norm_le_pi_norm (![(C.s1 : ℂ),(C.s2 : ℂ)]) 0
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg C.hs1] using h

theorem midpoint_of_takagi {T : Ten2} (C : Takagi2 T) (hs : C.s1 ≤ 1) :
    ∃ X Y : Ten2, X.transpose = X ∧ Y.transpose = Y ∧
      X ∈ unitary Ten2 ∧ Y ∈ unitary Ten2 ∧ (1/2 : ℂ) • (X+Y) = T := by
  let S := diagR C.s1 C.s2
  let Z := diag2 (Complex.I * Real.sqrt (1-C.s1^2)) (Complex.I * Real.sqrt (1-C.s2^2))
  have hr : C.s1^2 + Real.sqrt (1-C.s1^2)^2 = 1 := by
    rw [Real.sq_sqrt (by nlinarith [C.hs1])]
    ring
  have hq : C.s2^2 + Real.sqrt (1-C.s2^2)^2 = 1 := by
    rw [Real.sq_sqrt (by nlinarith [C.hs2, C.hs2le])]
    ring
  have hz : SymmetricMidpointDefect S Z :=
    nb_imaginary_diagonal_defect C.s1 C.s2 _ _ hr hq
  have hu := midpoint_defect_unitary S Z (diagR_star C.s1 C.s2) hz.2.1 hz.2.2.2
  have hps : (S+Z).transpose = S+Z := by
    simp only [Matrix.transpose_add, S, diagR_transpose, hz.1]
  have hms : (S-Z).transpose = S-Z := by
    simp only [Matrix.transpose_sub, S, diagR_transpose, hz.1]
  have hx := unitary_congruence C.hQ hps (Unitary.mem_iff.mp hu.1).1
  have hy := unitary_congruence C.hQ hms (Unitary.mem_iff.mp hu.2).1
  refine ⟨C.Q*(S+Z)*C.Q.transpose, C.Q*(S-Z)*C.Q.transpose,
    hx.2, hy.2, hx.1, hy.1, ?_⟩
  conv_rhs => rw [C.hT]
  dsimp [S]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul]
  module

theorem symmetric_contraction_midpoint (T : Ten2) (ht : T.transpose = T)
    (hn : spectralNorm T ≤ 1) :
    ∃ X Y : Ten2, X.transpose = X ∧ Y.transpose = Y ∧
      X ∈ unitary Ten2 ∧ Y ∈ unitary Ten2 ∧ (1/2 : ℂ) • (X+Y) = T := by
  obtain ⟨C⟩ := nb_takagi_exists T ht
  exact midpoint_of_takagi C (by rwa [← spectralNorm_takagi C])

end SpectralNorm

section PhaseAvoidance
open Polynomial

@[expose] noncomputable def polePolynomial (A : Ten2) : Polynomial ℂ :=
  1 + C (A 0 0 + A 1 1) * X + C A.det * X^2

theorem polePolynomial_eval (A : Ten2) (z : ℂ) :
    (polePolynomial A).eval z = (1 + z • A).det := by
  simp [polePolynomial, Matrix.det_fin_two, Matrix.add_apply,
    Matrix.smul_apply]
  ring

theorem phase_avoids_both (A B : Ten2) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (1+z • A).det ≠ 0 ∧ (1+z • B).det ≠ 0 := by
  classical
  let F : Finset ℂ := {1, -1, Complex.I, -Complex.I, (3+4*Complex.I)/5}
  let p := polePolynomial A * polePolynomial B
  have hp : p ≠ 0 := by
    intro h
    have hh := congrArg (fun q : Polynomial ℂ => q.eval 0) h
    simp [p, polePolynomial] at hh
  have hdA : (polePolynomial A).natDegree ≤ 2 := by
    unfold polePolynomial
    compute_degree
  have hdB : (polePolynomial B).natDegree ≤ 2 := by
    unfold polePolynomial
    compute_degree
  have hd : p.natDegree ≤ 4 :=
    (Polynomial.natDegree_mul_le).trans (by omega)
  have hcard : F.card = 5 := by
    norm_num [F, Finset.card_insert_of_notMem, Complex.ext_iff,
      Complex.div_re, Complex.div_im, Complex.normSq]
  have hex : ∃ z ∈ F, p.eval z ≠ 0 := by
    by_contra! h
    have hc := Polynomial.card_le_degree_of_subset_roots
      (p := p) (Z := F) (fun z hz => (Polynomial.mem_roots hp).mpr (h z hz))
    omega
  obtain ⟨z,hz,hv⟩ := hex
  refine ⟨z, ?_, ?_, ?_⟩
  · have hn : Complex.normSq z = 1 := by
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;>
        norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.normSq]
    have hn' := Complex.normSq_eq_norm_sq z
    nlinarith [norm_nonneg z]
  · intro h
    apply hv
    simp [p, polePolynomial_eval, h]
  · intro h
    apply hv
    simp [p, polePolynomial_eval, h]

end PhaseAvoidance

theorem nb_contraction_attained (cfg : Config) (T : Ten2)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (ht : T.transpose = T) (hn : spectralNorm T ≤ 1) :
    ∃ z : ℂ, ∃ p : BIParams, ‖z‖ = 1 ∧ NoCoupling p ∧
      biForwardT cfg p = z • T := by
  obtain ⟨X,Y,hxs,hys,hx,hy,hm⟩ := symmetric_contraction_midpoint T ht hn
  obtain ⟨z,hz,hpx,hpy⟩ := phase_avoids_both X Y
  have hX := NBPhaseConstraints.nb_phase_preserves_symmetric_unitary hxs hx z hz
  have hY := NBPhaseConstraints.nb_phase_preserves_symmetric_unitary hys hy z hz
  obtain ⟨p,hp,hT⟩ := parity_synthesis_material cfg (z • X) (z • Y)
    hk heq hX.1 hY.1 hX.2 hY.2 hpx hpy
  refine ⟨z,p,hz,hp,?_⟩
  rw [hT, NBPhaseConstraints.nb_phase_midpoint, hm]

section NormBounds
open scoped Matrix.Norms.L2Operator

theorem euclidean_sq (a : Vec2) :
    ‖WithLp.toLp 2 a‖^2 = jonesNormSqR a := by
  rw [EuclideanSpace.norm_sq_eq, jonesNormSqR_eq]
  simp [Fin.sum_univ_two, Complex.normSq_eq_norm_sq]

theorem spectralNorm_le_one_iff (T : Ten2) :
    spectralNorm T ≤ 1 ↔ ∀ a, jonesNormSqR (T *ᵥ a) ≤ jonesNormSqR a := by
  constructor
  · intro hn a
    have hh := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) T).le_opNorm (WithLp.toLp 2 a)
    rw [Matrix.toEuclideanCLM_toLp] at hh
    have he : ‖WithLp.toLp 2 (T *ᵥ a)‖ ≤ ‖WithLp.toLp 2 a‖ :=
      hh.trans (by simpa [spectralNorm, Matrix.l2_opNorm_toEuclideanCLM]
        using mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    rw [← euclidean_sq, ← euclidean_sq]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr he
  · intro hn
    change ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) T‖ ≤ 1
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [one_mul]
    have hh := hn (WithLp.ofLp x)
    rw [← euclidean_sq, ← euclidean_sq] at hh
    simpa only [WithLp.toLp_ofLp, ← Matrix.toEuclideanCLM_toLp] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh

theorem bi_forward_spectralNorm_le_one (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) :
    spectralNorm (biForwardT cfg p) ≤ 1 :=
  (spectralNorm_le_one_iff _).mpr (biForwardT_contractive cfg p hk heq)

theorem nb_normalized_attained (cfg : Config) (T₀ : Ten2)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (ht : T₀.transpose = T₀) (hn : spectralNorm T₀ ≠ 0) :
    ∃ z : ℂ, ∃ p : BIParams, ‖z‖ = 1 ∧ NoCoupling p ∧
      biForwardT cfg p = z • ((spectralNorm T₀ : ℂ)⁻¹ • T₀) := by
  apply nb_contraction_attained cfg _ hk heq
  · rw [Matrix.transpose_smul, ht]
  · rw [spectralNorm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ spectralNorm T₀ from norm_nonneg T₀), inv_mul_cancel₀ hn]

theorem efficiency_upper_bound (cfg : Config) (p : BIParams) (T₀ : Ten2) (γ : ℂ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hn : spectralNorm T₀ ≠ 0) (hT : biForwardT cfg p = γ • T₀) :
    Complex.normSq γ ≤ (spectralNorm T₀ ^ 2)⁻¹ := by
  have hh := bi_forward_spectralNorm_le_one cfg p hk heq
  rw [hT, spectralNorm_smul] at hh
  have hs : 0 < spectralNorm T₀ := lt_of_le_of_ne (norm_nonneg T₀) (Ne.symm hn)
  have hc : ‖γ‖ ≤ (spectralNorm T₀)⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hs).mpr hh
  rw [Complex.normSq_eq_norm_sq, ← inv_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (le_of_lt (inv_pos.mpr hs))).mpr hc

end NormBounds

section ForcedPhase
open JonesOperatorClassification NBPhaseConstraints ClassPeakEfficiency BIPhysicalFeasibility
open MaterialSpace ClassFeasibility ClassPeakEfficiency
open scoped Matrix.Norms.L2Operator
attribute [local simp] jonesColMatrix_apply_zero jonesColMatrix_apply_one

@[expose] noncomputable def forcedTransmission (u₁ u₂ v₁ v₂ : Vec2) : Ten2 :=
  jonesColMatrix v₁ ((bilinear u₂ v₁ / bilinear u₁ v₂) • v₂) *
    (jonesColMatrix u₁ u₂)⁻¹

theorem mul_columns (T : Ten2) (u₁ u₂ : Vec2) :
    T * jonesColMatrix u₁ u₂ = jonesColMatrix (T *ᵥ u₁) (T *ᵥ u₂) := by
  ext i j
  fin_cases j <;> simp [Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

theorem forcedTransmission_paper (u₁ u₂ v₁ v₂ : Vec2) :
    forcedTransmission u₁ u₂ v₁ v₂ =
      jonesColMatrix v₁ v₂ * diag2 1 (bilinear u₂ v₁ / bilinear u₁ v₂) *
        (jonesColMatrix u₁ u₂)⁻¹ := by
  unfold forcedTransmission
  congr 1
  ext i j
  fin_cases j <;> simp [diag2, Matrix.mul_apply,
    Fin.sum_univ_two, mul_comm]

theorem forcedTransmission_maps (u₁ u₂ v₁ v₂ : Vec2)
    (hu : (jonesColMatrix u₁ u₂).det ≠ 0) :
    forcedTransmission u₁ u₂ v₁ v₂ *ᵥ u₁ = v₁ ∧
    forcedTransmission u₁ u₂ v₁ v₂ *ᵥ u₂ =
      (bilinear u₂ v₁ / bilinear u₁ v₂) • v₂ := by
  have hh := Matrix.nonsing_inv_mul_cancel_right (jonesColMatrix u₁ u₂)
    (jonesColMatrix v₁ ((bilinear u₂ v₁ / bilinear u₁ v₂) • v₂)) (isUnit_iff_ne_zero.mpr hu)
  change forcedTransmission u₁ u₂ v₁ v₂ * jonesColMatrix u₁ u₂ = _ at hh
  rw [mul_columns] at hh
  constructor
  · exact congrArg (fun M => fun i => M i 0) hh
  · exact congrArg (fun M => fun i => M i 1) hh

theorem symmetric_of_cross (T : Ten2) (u₁ u₂ : Vec2)
    (hu : (jonesColMatrix u₁ u₂).det ≠ 0)
    (hc : bilinear u₂ (T *ᵥ u₁) = bilinear u₁ (T *ᵥ u₂)) :
    T.transpose = T := by
  have hh : (T 0 1 - T 1 0) * (jonesColMatrix u₁ u₂).det = 0 := by
    calc _ = bilinear u₁ (T *ᵥ u₂) - bilinear u₂ (T *ᵥ u₁) := by
           simp [bilinear, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
             Matrix.det_fin_two]
           ring
         _ = 0 := sub_eq_zero.mpr hc.symm
  have hz := (mul_eq_zero.mp hh).resolve_right hu
  have he := sub_eq_zero.mp hz
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, he]

theorem forcedTransmission_symmetric (u₁ u₂ v₁ v₂ : Vec2)
    (hu : (jonesColMatrix u₁ u₂).det ≠ 0) (hs : bilinear u₁ v₂ ≠ 0) :
    (forcedTransmission u₁ u₂ v₁ v₂).transpose = forcedTransmission u₁ u₂ v₁ v₂ := by
  apply symmetric_of_cross _ u₁ u₂ hu
  rw [(forcedTransmission_maps u₁ u₂ v₁ v₂ hu).1,
      (forcedTransmission_maps u₁ u₂ v₁ v₂ hu).2, bilinear_smul_right]
  field_simp

theorem forced_operator (T : Ten2) (u₁ u₂ v₁ v₂ : Vec2) (α β : ℂ)
    (hu : (jonesColMatrix u₁ u₂).det ≠ 0) (hs : bilinear u₁ v₂ ≠ 0)
    (ht : T.transpose = T) (h₁ : T *ᵥ u₁ = α • v₁) (h₂ : T *ᵥ u₂ = β • v₂) :
    T = α • forcedTransmission u₁ u₂ v₁ v₂ := by
  have hc := nb_two_state_phase_forced ht h₁ h₂
  have hb : β = α * (bilinear u₂ v₁ / bilinear u₁ v₂) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff hs).mpr
    simpa [mul_div_assoc] using hc.symm
  have hcols : T * jonesColMatrix u₁ u₂ =
      α • jonesColMatrix v₁ ((bilinear u₂ v₁ / bilinear u₁ v₂) • v₂) := by
    rw [mul_columns, h₁, h₂, hb]
    ext i j
    fin_cases j <;> simp [mul_assoc]
  have hh := congrArg (fun M => M * (jonesColMatrix u₁ u₂)⁻¹) hcols
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.mpr hu)] at hh
  simpa [forcedTransmission, Matrix.smul_mul] using hh

theorem eq25_nb_peak (cfg : Config) (u₁ u₂ v₁ v₂ : Vec2)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hnorm : isNormalizedJones u₁ ∧ isNormalizedJones u₂ ∧
      isNormalizedJones v₁ ∧ isNormalizedJones v₂)
    (hu : (jonesColMatrix u₁ u₂).det ≠ 0)
    (hs : bilinear u₁ v₂ ≠ 0)
    (hcross : ‖bilinear u₂ v₁‖ = ‖bilinear u₁ v₂‖) :
    classPeakEqualEfficiency cfg .NB u₁ u₂ v₁ v₂ =
        (spectralNorm (forcedTransmission u₁ u₂ v₁ v₂)^2)⁻¹ ∧
      classPeakAttained cfg .NB u₁ u₂ v₁ v₂ := by
  let T₀ := forcedTransmission u₁ u₂ v₁ v₂
  let n := spectralNorm T₀
  let Λ := bilinear u₂ v₁ / bilinear u₁ v₂
  have ht := forcedTransmission_symmetric u₁ u₂ v₁ v₂ hu hs
  have hm := forcedTransmission_maps u₁ u₂ v₁ v₂ hu
  have hn : n ≠ 0 := by
    intro hz
    have hzero : T₀ = 0 := norm_eq_zero.mp hz
    have hv : v₁ = 0 := by
      rw [← hm.1]
      change T₀ *ᵥ u₁ = 0
      rw [hzero]
      simp
    have hvn := jonesNormSqR_eq_one_of_normalized hnorm.2.2.1
    simp [hv, jonesNormSqR_eq] at hvn
  have hl : ‖Λ‖ = 1 := by
    dsimp [Λ]
    rw [norm_div, hcross, div_self (norm_ne_zero_iff.mpr hs)]
  have upper : ∀ η ∈ classEqualEfficiencies cfg .NB u₁ u₂ v₁ v₂, η ≤ (n^2)⁻¹ := by
    rintro η ⟨p,hp,α,β,h₁,h₂,he₁,_⟩
    have hh := forced_operator _ u₁ u₂ v₁ v₂ α β hu hs
      (forward_symmetric cfg p hk heq hp) h₁ h₂
    rw [← he₁]
    exact efficiency_upper_bound cfg p T₀ α hk heq hn hh
  obtain ⟨z,p,hz,hp,hT⟩ := nb_normalized_attained cfg T₀ hk heq ht hn
  have he : efficiency (z * (n : ℂ)⁻¹) = (n^2)⁻¹ := by
    simp [efficiency, Complex.normSq_eq_norm_sq, hz, sq,
      abs_of_nonneg (show 0 ≤ n from norm_nonneg T₀)]
  have hel : efficiency ((z * (n : ℂ)⁻¹) * Λ) = (n^2)⁻¹ := by
    simpa [efficiency, Complex.normSq_mul, Complex.normSq_eq_norm_sq, hl] using he
  have hatt : classRealizes cfg .NB u₁ u₂ v₁ v₂ ((n^2)⁻¹) ((n^2)⁻¹) := by
    refine ⟨p,hp,z * (n : ℂ)⁻¹,(z * (n : ℂ)⁻¹) * Λ,?_,?_,he,hel⟩
    · rw [hT, Matrix.smul_mulVec, Matrix.smul_mulVec, hm.1, smul_smul]
    · rw [hT, Matrix.smul_mulVec, Matrix.smul_mulVec, hm.2, smul_smul, smul_smul]
  have hpeak : classPeakEqualEfficiency cfg .NB u₁ u₂ v₁ v₂ = (n^2)⁻¹ := by
    apply le_antisymm
    · exact csSup_le ⟨_,hatt⟩ upper
    · exact le_csSup ⟨_,upper⟩ hatt
  refine ⟨hpeak,?_⟩
  unfold classPeakAttained
  rwa [hpeak]

end ForcedPhase

end GSTC.Scattering.NBPeakEfficiency
