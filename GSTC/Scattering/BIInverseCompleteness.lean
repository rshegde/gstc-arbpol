/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIScattering

public section

namespace GSTC.Scattering
namespace BIInverse

open Matrix
open scoped Matrix

abbrev Theta : Matrix (Fin 4) (Fin 4) ℂ := parityExchange

theorem theta_transpose : (Theta : Matrix (Fin 4) (Fin 4) ℂ).transpose = Theta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Theta, parityExchange, Matrix.transpose_apply]

theorem commute_nonsing_inv {X Y : Matrix (Fin 4) (Fin 4) ℂ} (h : X * Y = Y * X)
    (hy : IsUnit Y.det) : X * Y⁻¹ = Y⁻¹ * X := by
  have hne : Y.det ≠ 0 := (isUnit_iff_ne_zero).mp hy
  have h1 : Y⁻¹ * (X * Y) = X := by
    calc Y⁻¹ * (X * Y) = Y⁻¹ * (Y * X) := by rw [h]
      _ = X := by
        have hh := Matrix.nonsing_inv_mul Y (isUnit_iff_ne_zero.mpr hne)
        simp only [← Matrix.mul_assoc, hh, Matrix.one_mul]
  have h2 : (Y⁻¹ * X) * Y = (X * Y⁻¹) * Y := by
    calc (Y⁻¹ * X) * Y = Y⁻¹ * (X * Y) := by rw [Matrix.mul_assoc]
      _ = X := h1
      _ = (X * Y⁻¹) * Y := by
        have hx : (X * Y⁻¹) * Y = X * (Y⁻¹ * Y) := by rw [← Matrix.mul_assoc]
        rw [hx, Matrix.nonsing_inv_mul Y (isUnit_iff_ne_zero.mpr hne), Matrix.mul_one]
  have h3 : Y⁻¹ * X = X * Y⁻¹ := mat4_mul_cancel_right Y _ _ hne h2
  exact h3.symm

variable {C : Matrix (Fin 4) (Fin 4) ℂ}

@[expose] noncomputable def cayleyPreimage (C : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  cayleyOperator C

theorem cayleyPreimage_eq_explicit
    (h : IsUnit ((1 + C : Matrix (Fin 4) (Fin 4) ℂ).det)) :
    cayleyPreimage C = (2 * Complex.I) • ((1 + C)⁻¹ * (1 - C)) := by
  have hne : (1 + C : Matrix (Fin 4) (Fin 4) ℂ).det ≠ 0 := (isUnit_iff_ne_zero).mp h
  have hcomm : (1 - C) * (1 + C) = (1 + C) * (1 - C) := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hcomm2 : (1 - C) * (1 + C)⁻¹ = (1 + C)⁻¹ * (1 - C) := by
    have hh := commute_nonsing_inv (X := 1 - C) (Y := 1 + C) hcomm
      (isUnit_iff_ne_zero.mpr hne)
    simpa using hh
  unfold cayleyPreimage cayleyOperator
  rw [show (Complex.I + Complex.I : ℂ) = 2 * Complex.I by ring]
  simp only [cayleyResponse, hcomm2]

theorem cayleyPreimage_hermitian (hC : C.conjTranspose * C = 1)
    (h : IsUnit ((1 + C : Matrix (Fin 4) (Fin 4) ℂ).det)) :
    (cayleyPreimage C).conjTranspose = cayleyPreimage C := by
  exact cayleyOperator_hermitian C hC h

theorem cayleyPreimage_equation (h : IsUnit ((1 + C : Matrix (Fin 4) (Fin 4) ℂ).det)) :
    2 • (C - 1) = Complex.I • (cayleyPreimage C * (C + 1)) := by
  have hR := cayleyResponse_equation C h

  have hRC : cayleyResponse C * (C + 1) = 1 - C := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) hR
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.one_apply] at hh ⊢
    fin_cases i <;> fin_cases j <;> simp_all <;> linear_combination hh
  have hK : cayleyPreimage C = (2 * Complex.I) • cayleyResponse C := by
    unfold cayleyPreimage cayleyOperator
    rw [show (Complex.I + Complex.I : ℂ) = 2 * Complex.I by ring]
  have hs : Complex.I • ((2 * Complex.I) • (cayleyResponse C * (C + 1))) =
      (-2 : ℂ) • (cayleyResponse C * (C + 1)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [hK, Matrix.smul_mul]
  rw [hs, hRC]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

theorem biPowerResponse4_of_constitutiveK (cfg : Config) (p : BIParams)
    {S : Matrix (Fin 4) (Fin 4) ℂ}
    (h : biConstitutiveK cfg p = cayleyPreimage (Theta * S))
    (hpole : IsUnit ((1 + Theta * S : Matrix (Fin 4) (Fin 4) ℂ).det)) :
    biPowerResponse4 cfg p = S := by
  have hD := biConstitutiveK_den_isUnit cfg p
  have hCay : cayley4 (biConstitutiveK cfg p) = Theta * S := by
    refine (cayley4_constitutive_equation_iff (biConstitutiveK cfg p) (Theta * S) hD).mp ?_ |>.symm
    rw [h, cayleyPreimage_equation (C := Theta * S) hpole]
  simp only [biPowerResponse4, hCay]
  rw [← Matrix.mul_assoc, show (Theta : Matrix (Fin 4) (Fin 4) ℂ) * Theta = 1 from
    parityExchange_sq]
  simp only [Matrix.one_mul]

theorem theta_nonsing_inv : (Theta : Matrix (Fin 4) (Fin 4) ℂ)⁻¹ = Theta :=
  Matrix.inv_eq_right_inv parityExchange_sq

theorem theta_conjugate_inv (X : Matrix (Fin 4) (Fin 4) ℂ) :
    (Theta*X*Theta)⁻¹ = Theta*X⁻¹*Theta := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, theta_nonsing_inv]
  simp only [Matrix.mul_assoc]

theorem cayleyPreimage_transpose (C : Matrix (Fin 4) (Fin 4) ℂ) (hp : IsUnit ((1+C).det)) :
    (cayleyPreimage C).transpose = cayleyPreimage C.transpose := by
  have hpt : IsUnit ((1+C.transpose).det) := by
    rw [show (1+C.transpose) = (1+C).transpose by
      simp only [Matrix.transpose_add, Matrix.transpose_one], Matrix.det_transpose]
    exact hp
  rw [cayleyPreimage_eq_explicit hpt]
  unfold cayleyPreimage cayleyOperator cayleyResponse
  simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one]
  congr 1
  ring

theorem cayleyPreimage_theta_conjugate (C : Matrix (Fin 4) (Fin 4) ℂ) :
    cayleyPreimage (Theta*C*Theta) = Theta*cayleyPreimage C*Theta := by
  have ha : 1+Theta*C*Theta = Theta*(1+C)*Theta := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, parityExchange_sq]
  have hs : 1-Theta*C*Theta = Theta*(1-C)*Theta := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, parityExchange_sq]
  unfold cayleyPreimage cayleyOperator cayleyResponse
  rw [ha, hs, theta_conjugate_inv]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = Theta*((1-C)*(Theta*Theta)*(1+C)⁻¹)*Theta := by noncomm_ring
    _ = _ := by rw [parityExchange_sq]; noncomm_ring

theorem cayleyPreimage_thetaSymm (S : Matrix (Fin 4) (Fin 4) ℂ)
    (hS : S.transpose = S) (hp : IsUnit ((1+Theta*S).det)) :
    (cayleyPreimage (Theta*S)).transpose = Theta*cayleyPreimage (Theta*S)*Theta := by
  have hc : (Theta*S).transpose = Theta*(Theta*S)*Theta := by
    rw [Matrix.transpose_mul,theta_transpose,hS]
    rw [← Matrix.mul_assoc Theta Theta,parityExchange_sq,Matrix.one_mul]
  rw [cayleyPreimage_transpose _ hp,hc,cayleyPreimage_theta_conjugate]

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

@[expose] noncomputable def locusMatrix (a d : ℝ) (b g h e : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(a : ℂ), b, g, h; star b, (d : ℂ), h, e;
      star g, star h, (a : ℂ), star b; star h, star e, b, (d : ℂ)]

theorem locus_canonical (K : Matrix (Fin 4) (Fin 4) ℂ)
    (hH : K.conjTranspose = K) (hT : K.transpose = Theta*K*Theta) :
    K = locusMatrix (K 0 0).re (K 1 1).re (K 0 1) (K 0 2) (K 0 3) (K 1 3) := by
  have hh (i j : Fin 4) : K i j = star (K j i) :=
    (congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A i j) hH).symm
  have h00 := eq_star_iff_eq_ofReal_re (hh 0 0)
  have h11 := eq_star_iff_eq_ofReal_re (hh 1 1)
  have t00 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A 0 0) hT
  have t01 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A 0 1) hT
  have t10 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A 1 0) hT
  have t11 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A 1 1) hT
  have t21 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A 2 1) hT
  simp only [Matrix.transpose_apply,Matrix.mul_apply,Fin.sum_univ_four] at t00 t01 t10 t11 t21
  simp [Theta,parityExchange] at t00 t01 t10 t11 t21
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [locusMatrix,←t00,←t01,←t10,←t11,t21,hh 1 0,hh 2 0,hh 2 1,hh 3 0,hh 3 1] <;>
    first | exact h00 | exact h11

@[expose] noncomputable def recoverParameters (cfg : Config) (K : Matrix (Fin 4) (Fin 4) ℂ) : BIParams :=
  let a := (K 0 0).re
  let d := (K 1 1).re
  let b := K 0 1
  let g := K 0 2
  let h := K 0 3
  let e := K 1 3
  let z := Real.sqrt cfg.upper.eta
  { ee00 := (-a-g.re)/(cfg.omega*z^2*cfg.vac.eps0)
    ee01 := (-b.re-h.re)/(cfg.omega*z^2*cfg.vac.eps0)
    ee11 := (-d-e.re)/(cfg.omega*z^2*cfg.vac.eps0)
    mm00 := z^2*(-d+e.re)/(cfg.omega*cfg.vac.mu0)
    mm01 := z^2*(b.re-h.re)/(cfg.omega*cfg.vac.mu0)
    mm11 := z^2*(-a+g.re)/(cfg.omega*cfg.vac.mu0)
    g00 := cfg.vac.c0*(-b.im+h.im)/cfg.omega
    g01 := -cfg.vac.c0*g.im/cfg.omega
    g10 := cfg.vac.c0*e.im/cfg.omega
    g11 := cfg.vac.c0*(-b.im-h.im)/cfg.omega }

theorem recover_canonical (cfg : Config) (a d : ℝ) (b g h e : ℂ) :
    biConstitutiveK cfg (recoverParameters cfg (locusMatrix a d b g h e)) =
      locusMatrix a d b g h e := by
  have hz : Real.sqrt cfg.upper.eta ≠ 0 := ne_of_gt (Real.sqrt_pos.2 cfg.upper.eta_pos)
  have hw : cfg.omega ≠ 0 := ne_of_gt cfg.omega_pos
  have he : cfg.vac.eps0 ≠ 0 := ne_of_gt cfg.vac.eps0_pos
  have hm : cfg.vac.mu0 ≠ 0 := ne_of_gt cfg.vac.mu0_pos
  have hc : cfg.vac.c0 ≠ 0 := ne_of_gt cfg.vac.c0_pos
  unfold biConstitutiveK
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [biConstitutiveH,biMidpointMap4,recoverParameters,locusMatrix,
      star_div₀,star_ofReal] <;>
    apply Complex.ext <;>
    simp only [Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.normSq_apply,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      Complex.re_ofNat,Complex.im_ofNat,Complex.one_re,Complex.one_im,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.neg_re,Complex.neg_im,Complex.conj_re,Complex.conj_im,
      ← Complex.ofReal_pow, zero_mul,mul_zero,zero_add,add_zero,sub_zero] <;>
    norm_num only [Complex.inv_re,Complex.inv_im,Complex.normSq_apply,
      Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im,
      Complex.re_ofNat,Complex.im_ofNat,Complex.div_re,Complex.div_im] <;>
    field_simp [hz,hw,he,hm,hc] <;> ring

theorem recover_forward (cfg : Config) (p : BIParams) :
    recoverParameters cfg (biConstitutiveK cfg p) = p := by
  have hz : Real.sqrt cfg.upper.eta ≠ 0 := ne_of_gt (Real.sqrt_pos.2 cfg.upper.eta_pos)
  have hw : cfg.omega ≠ 0 := ne_of_gt cfg.omega_pos
  have he : cfg.vac.eps0 ≠ 0 := ne_of_gt cfg.vac.eps0_pos
  have hm : cfg.vac.mu0 ≠ 0 := ne_of_gt cfg.vac.mu0_pos
  have hc : cfg.vac.c0 ≠ 0 := ne_of_gt cfg.vac.c0_pos
  cases p
  simp only [recoverParameters]
  congr 1
  all_goals
    simp only [biConstitutiveK, Matrix.smul_apply,smul_eq_mul,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_four]
    simp [biConstitutiveH,biMidpointMap4,star_div₀,star_ofReal]
    simp only [Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.normSq_apply,
      Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,Complex.one_re,Complex.one_im,
      Complex.neg_re,Complex.neg_im,
      zero_mul,mul_zero,add_zero,sub_zero]
    field_simp [hz,hw,he,hm,hc]
    ring

theorem recoverParameters_constitutiveK (cfg : Config)
    (K : Matrix (Fin 4) (Fin 4) ℂ) (hH : K.conjTranspose = K)
    (hT : K.transpose = Theta * K * Theta) :
    biConstitutiveK cfg (recoverParameters cfg K) = K := by
  have hf := locus_canonical K hH hT
  exact (congrArg (fun L => biConstitutiveK cfg (recoverParameters cfg L)) hf).trans
    ((recover_canonical cfg _ _ _ _ _ _).trans hf.symm)

theorem constitutiveK_injective (cfg : Config) : Function.Injective (biConstitutiveK cfg) := by
  intro p q h
  have hh := congrArg (recoverParameters cfg) h
  simpa only [recover_forward] using hh

@[expose] noncomputable def parametersForResponse (cfg : Config)
    (S : Matrix (Fin 4) (Fin 4) ℂ) : BIParams :=
  recoverParameters cfg (cayleyPreimage (Theta * S))

theorem parametersForResponse_constitutiveK (cfg : Config)
    (S : Matrix (Fin 4) (Fin 4) ℂ) (hS : S.transpose = S)
    (hU : S.conjTranspose * S = 1) (hp : IsUnit ((1 + Theta * S).det)) :
    biConstitutiveK cfg (parametersForResponse cfg S) = cayleyPreimage (Theta * S) := by
  have hu : (Theta * S).conjTranspose * (Theta * S) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc _ = S.conjTranspose * (Theta.conjTranspose * Theta) * S := by noncomm_ring
         _ = 1 := by rw [show Theta.conjTranspose * Theta = 1 from parityExchange_unitary,
           Matrix.mul_one, hU]
  exact recoverParameters_constitutiveK cfg _ (cayleyPreimage_hermitian hu hp)
    (cayleyPreimage_thetaSymm S hS hp)

theorem parametersForResponse_response (cfg : Config)
    (S : Matrix (Fin 4) (Fin 4) ℂ) (hS : S.transpose = S)
    (hU : S.conjTranspose * S = 1) (hp : IsUnit ((1 + Theta * S).det)) :
    biPowerResponse4 cfg (parametersForResponse cfg S) = S :=
  biPowerResponse4_of_constitutiveK cfg _
    (parametersForResponse_constitutiveK cfg S hS hU hp) hp

theorem constitutiveK_of_response (cfg : Config) (p : BIParams)
    (S : Matrix (Fin 4) (Fin 4) ℂ) (hp : IsUnit ((1 + Theta * S).det))
    (h : biPowerResponse4 cfg p = S) :
    biConstitutiveK cfg p = cayleyPreimage (Theta * S) := by
  have hc : Theta * S = cayley4 (biConstitutiveK cfg p) := by
    rw [← h, biPowerResponse4, ← Matrix.mul_assoc, parityExchange_sq, Matrix.one_mul]
  have he := (cayley4_constitutive_equation_iff (biConstitutiveK cfg p)
    (Theta * S) (biConstitutiveK_den_isUnit cfg p)).mpr hc
  have hh : biConstitutiveK cfg p * (Theta * S + 1) =
      cayleyPreimage (Theta * S) * (Theta * S + 1) := by
    have hs := he.symm.trans (cayleyPreimage_equation hp)
    ext i j
    have hij := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A i j) hs
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    exact mul_left_cancel₀ Complex.I_ne_zero hij
  apply mat4_mul_cancel_right (Theta * S + 1) _ _ _ hh
  simpa only [add_comm] using (isUnit_iff_ne_zero.mp hp)

theorem bi_inverse_complete (cfg : Config) (S : Matrix (Fin 4) (Fin 4) ℂ)
    (hS : S.transpose = S) (hU : S.conjTranspose * S = 1)
    (hp : IsUnit ((1 + Theta * S).det)) :
    ∃! p : BIParams, biPowerResponse4 cfg p = S := by
  refine ⟨parametersForResponse cfg S, parametersForResponse_response cfg S hS hU hp, ?_⟩
  intro p h
  apply constitutiveK_injective cfg
  exact (constitutiveK_of_response cfg p S hp h).trans
    (parametersForResponse_constitutiveK cfg S hS hU hp).symm

theorem parametersForResponse_unique_gstc (cfg : Config)
    (S : Matrix (Fin 4) (Fin 4) ℂ) (hk : cfg.kPar = 0)
    (heq : cfg.lower.eta = cfg.upper.eta) (a : Operator.Vec4) :
    ∃! b : Operator.Vec4, gstcSatisfied4 cfg (encode (parametersForResponse cfg S))
      (Operator.readR a) (Operator.readR b) (Operator.readT a) (Operator.readT b) :=
  bi_unique_scattering cfg _ hk heq a

end BIInverse
end GSTC.Scattering
