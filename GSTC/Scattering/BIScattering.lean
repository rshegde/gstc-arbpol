/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Operator.Solvability
public import GSTC.Scattering.Unitarity

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Matrix.PosDef

public section

namespace GSTC.Scattering

open scoped Matrix
open GSTC.Scattering.Operator

@[expose] noncomputable def twoPortOut (cfg : Config) (sus : Susceptibilities) :
    BoundaryCoeffs where
  beI := (boundaryCoeffs cfg .above sus).beI
  beR := (boundaryCoeffs cfg .above sus).beR
  beT := (boundaryCoeffs cfg .above sus).beT
  bhI := (boundaryCoeffs cfg .above sus).bhI
  bhR := (boundaryCoeffs cfg .above sus).bhR
  bhT := (boundaryCoeffs cfg .above sus).bhT

@[expose] noncomputable def twoPortIn (cfg : Config) (sus : Susceptibilities) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  !![(boundaryCoeffs cfg .above sus).beI 0 0, (boundaryCoeffs cfg .above sus).beI 0 1,
     (boundaryCoeffs cfg .below sus).beI 0 0, (boundaryCoeffs cfg .below sus).beI 0 1;
     (boundaryCoeffs cfg .above sus).beI 1 0, (boundaryCoeffs cfg .above sus).beI 1 1,
     (boundaryCoeffs cfg .below sus).beI 1 0, (boundaryCoeffs cfg .below sus).beI 1 1;
     (boundaryCoeffs cfg .above sus).bhI 0 0, (boundaryCoeffs cfg .above sus).bhI 0 1,
     (boundaryCoeffs cfg .below sus).bhI 0 0, (boundaryCoeffs cfg .below sus).bhI 0 1;
     (boundaryCoeffs cfg .above sus).bhI 1 0, (boundaryCoeffs cfg .above sus).bhI 1 1,
     (boundaryCoeffs cfg .below sus).bhI 1 0, (boundaryCoeffs cfg .below sus).bhI 1 1]

theorem twoPortIn_mulVec_pack (cfg : Config) (sus : Susceptibilities)
    (a1 a2 : Vec2) :
    twoPortIn cfg sus *ᵥ pack a1 a2
      = pack ((boundaryCoeffs cfg .above sus).beI *ᵥ a1
            + (boundaryCoeffs cfg .below sus).beI *ᵥ a2)
        ((boundaryCoeffs cfg .above sus).bhI *ᵥ a1
            + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2) := by
  ext i
  fin_cases i <;>
    simp [twoPortIn, pack, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four,
      Fin.sum_univ_two] <;>
    ring

theorem pack_neg (x y : Vec2) : -pack x y = pack (-x) (-y) := by
  ext i
  fin_cases i <;> simp [pack]

theorem twoPortSystem_iff_twoPort_eq (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) :
    twoPortSystem cfg sus a1 b1 a2 b2
      ↔ Kmat (twoPortOut cfg sus) *ᵥ pack b1 b2
          = -(twoPortIn cfg sus *ᵥ pack a1 a2) := by
  rw [twoPortIn_mulVec_pack]
  constructor
  · rintro ⟨hE, hM⟩
    have h1 : (boundaryCoeffs cfg .above sus).beR *ᵥ b1
            + (boundaryCoeffs cfg .above sus).beT *ᵥ b2
          = -((boundaryCoeffs cfg .above sus).beI *ᵥ a1
            + (boundaryCoeffs cfg .below sus).beI *ᵥ a2) := by
      calc (boundaryCoeffs cfg .above sus).beR *ᵥ b1
              + (boundaryCoeffs cfg .above sus).beT *ᵥ b2
          = ((boundaryCoeffs cfg .above sus).beI *ᵥ a1
              + (boundaryCoeffs cfg .above sus).beR *ᵥ b1
              + (boundaryCoeffs cfg .below sus).beI *ᵥ a2
              + (boundaryCoeffs cfg .above sus).beT *ᵥ b2)
            - (boundaryCoeffs cfg .above sus).beI *ᵥ a1
            - (boundaryCoeffs cfg .below sus).beI *ᵥ a2 := by abel
        _ = -((boundaryCoeffs cfg .above sus).beI *ᵥ a1
              + (boundaryCoeffs cfg .below sus).beI *ᵥ a2) := by rw [hE]; abel
    have h2 : (boundaryCoeffs cfg .above sus).bhR *ᵥ b1
            + (boundaryCoeffs cfg .above sus).bhT *ᵥ b2
          = -((boundaryCoeffs cfg .above sus).bhI *ᵥ a1
            + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2) := by
      calc (boundaryCoeffs cfg .above sus).bhR *ᵥ b1
              + (boundaryCoeffs cfg .above sus).bhT *ᵥ b2
          = ((boundaryCoeffs cfg .above sus).bhI *ᵥ a1
              + (boundaryCoeffs cfg .above sus).bhR *ᵥ b1
              + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2
              + (boundaryCoeffs cfg .above sus).bhT *ᵥ b2)
            - (boundaryCoeffs cfg .above sus).bhI *ᵥ a1
            - (boundaryCoeffs cfg .below sus).bhI *ᵥ a2 := by abel
        _ = -((boundaryCoeffs cfg .above sus).bhI *ᵥ a1
              + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2) := by rw [hM]; abel
    rw [Kmat_mulVec_pack, pack_neg]
    simp only [Kop, twoPortOut]
    rw [h1, h2]
  · intro h
    rw [Kmat_mulVec_pack, pack_neg] at h
    simp only [Kop, twoPortOut] at h
    obtain ⟨hE, hM⟩ := pack_injective h
    refine ⟨?_, ?_⟩
    · calc (boundaryCoeffs cfg .above sus).beI *ᵥ a1
            + (boundaryCoeffs cfg .above sus).beR *ᵥ b1
            + (boundaryCoeffs cfg .below sus).beI *ᵥ a2
            + (boundaryCoeffs cfg .above sus).beT *ᵥ b2
          = ((boundaryCoeffs cfg .above sus).beR *ᵥ b1
              + (boundaryCoeffs cfg .above sus).beT *ᵥ b2)
            + ((boundaryCoeffs cfg .above sus).beI *ᵥ a1
              + (boundaryCoeffs cfg .below sus).beI *ᵥ a2) := by abel
        _ = -((boundaryCoeffs cfg .above sus).beI *ᵥ a1
              + (boundaryCoeffs cfg .below sus).beI *ᵥ a2)
            + ((boundaryCoeffs cfg .above sus).beI *ᵥ a1
              + (boundaryCoeffs cfg .below sus).beI *ᵥ a2) := by rw [hE]
        _ = 0 := by abel
    · calc (boundaryCoeffs cfg .above sus).bhI *ᵥ a1
            + (boundaryCoeffs cfg .above sus).bhR *ᵥ b1
            + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2
            + (boundaryCoeffs cfg .above sus).bhT *ᵥ b2
          = ((boundaryCoeffs cfg .above sus).bhR *ᵥ b1
              + (boundaryCoeffs cfg .above sus).bhT *ᵥ b2)
            + ((boundaryCoeffs cfg .above sus).bhI *ᵥ a1
              + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2) := by abel
        _ = -((boundaryCoeffs cfg .above sus).bhI *ᵥ a1
              + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2)
            + ((boundaryCoeffs cfg .above sus).bhI *ᵥ a1
              + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2) := by rw [hM]
        _ = 0 := by abel

theorem gstcSatisfied4_iff_twoPort_eq (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) (hk : cfg.kPar = 0) :
    gstcSatisfied4 cfg sus a1 b1 a2 b2
      ↔ Kmat (twoPortOut cfg sus) *ᵥ pack b1 b2
          = -(twoPortIn cfg sus *ᵥ pack a1 a2) :=
  (twoPortSystem_iff_gstcSatisfied4 cfg sus a1 b1 a2 b2 hk).symm.trans
    (twoPortSystem_iff_twoPort_eq cfg sus a1 b1 a2 b2)

@[expose] def scatteringMatrix4 (S : ScatteringMatrix) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![S.r1 0 0, S.r1 0 1, S.t12 0 0, S.t12 0 1;
     S.r1 1 0, S.r1 1 1, S.t12 1 0, S.t12 1 1;
     S.t21 0 0, S.t21 0 1, S.r2 0 0, S.r2 0 1;
     S.t21 1 0, S.t21 1 1, S.r2 1 0, S.r2 1 1]

@[expose] noncomputable def scatteringMatrix4_p (cfg : Config) (S : ScatteringMatrix) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  !![S.r1 0 0, S.r1 0 1, S.t12_norm cfg 0 0, S.t12_norm cfg 0 1;
     S.r1 1 0, S.r1 1 1, S.t12_norm cfg 1 0, S.t12_norm cfg 1 1;
     S.t21_norm cfg 0 0, S.t21_norm cfg 0 1, S.r2 0 0, S.r2 0 1;
     S.t21_norm cfg 1 0, S.t21_norm cfg 1 1, S.r2 1 0, S.r2 1 1]

theorem scatteringMatrix4_mulVec (S : ScatteringMatrix) (a1 a2 : Vec2) :
    scatteringMatrix4 S *ᵥ pack a1 a2 = pack (S.out1 a1 a2) (S.out2 a1 a2) := by
  ext i
  fin_cases i <;>
    simp [scatteringMatrix4, ScatteringMatrix.out1, ScatteringMatrix.out2, pack,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four, Fin.sum_univ_two] <;>
    ring

@[expose] def parityExchange : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

theorem parityExchange_sq : parityExchange * parityExchange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parityExchange, Matrix.mul_apply, Fin.sum_univ_four]

theorem mat4_mul_cancel_left (A B C : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.det ≠ 0)
    (h : A * B = A * C) : B = C := by
  have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => A⁻¹ * M) h
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),
    Matrix.one_mul, Matrix.mul_one] using hh

theorem mat4_mul_cancel_right (A B C : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.det ≠ 0)
    (h : B * A = C * A) : B = C := by
  have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M * A⁻¹) h
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
    Matrix.one_mul, Matrix.mul_one] using hh

@[expose] noncomputable def cayley4 (K : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • K)⁻¹
    * (2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Complex.I • K)

theorem cayley4_eq (K : Matrix (Fin 4) (Fin 4) ℂ)
    (h : IsUnit ((2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • K).det))
    (U : Matrix (Fin 4) (Fin 4) ℂ) :
    (2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • K) * U
        = 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Complex.I • K
      ↔ U = cayley4 K := by
  let A := 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • K
  let B := 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Complex.I • K
  have hA : IsUnit A.det := by
    simpa only [A] using h
  constructor
  · intro hU
    have hh := Matrix.mul_nonsing_inv_cancel_left A B hA
    have heq : A * U = A * (A⁻¹ * B) := hU.trans hh.symm
    calc U = A⁻¹ * (A * U) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hA, Matrix.one_mul]
      _ = A⁻¹ * (A * (A⁻¹ * B)) := by rw [heq]
      _ = A⁻¹ * B := by rw [Matrix.mul_nonsing_inv_cancel_left A B hA]
      _ = cayley4 K := by simp only [cayley4, A, B]
  · intro hU
    rw [hU, cayley4]
    exact Matrix.mul_nonsing_inv_cancel_left A B hA

@[expose] noncomputable def cayleyResponse (U : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (1 - U) * (1 + U)⁻¹

theorem cayleyResponse_equation (U : Matrix (Fin 4) (Fin 4) ℂ)
    (h1 : IsUnit ((1 + U).det)) :
    (1 + cayleyResponse U) * U = 1 - cayleyResponse U := by
  have hA : IsUnit ((1 + U).det) := h1
  have hone : (1 : Matrix (Fin 4) (Fin 4) ℂ) + U - 1 = U := by
    rw [sub_eq_iff_eq_add, add_comm]
  have hAU : (1 + U)⁻¹ * U = 1 - (1 + U)⁻¹ := by
    calc (1 + U)⁻¹ * U = (1 + U)⁻¹ * ((1 + U) - 1) := by rw [hone]
      _ = (1 + U)⁻¹ * (1 + U) - (1 + U)⁻¹ * 1 := by rw [Matrix.mul_sub]
      _ = 1 - (1 + U)⁻¹ := by rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
  have hU1 : U + (1 - U) = 1 := by
    rw [← add_sub_assoc, sub_eq_iff_eq_add, add_comm]
  unfold cayleyResponse
  calc (1 + (1 - U) * (1 + U)⁻¹) * U
      = U + (1 - U) * ((1 + U)⁻¹ * U) := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = U + (1 - U) * (1 - (1 + U)⁻¹) := by rw [hAU]
    _ = 1 - (1 - U) * (1 + U)⁻¹ := by
        rw [Matrix.mul_sub, Matrix.mul_one, ← add_sub_assoc, hU1]

theorem cayleyResponse_skew (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U.conjTranspose * U = 1) (h1 : IsUnit ((1 + U).det)) :
    (cayleyResponse U).conjTranspose = -(cayleyResponse U) := by
  have hA : IsUnit ((1 + U).det) := h1
  have hstar : ((1 + U).conjTranspose).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.mpr ((isUnit_iff_ne_zero).mp hA)
  have heq : cayleyResponse U * (1 + U) = 1 - U := by
    unfold cayleyResponse
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
  have hdag : (1 + U).conjTranspose * (cayleyResponse U).conjTranspose
      = (1 - U).conjTranspose := by
    rw [← Matrix.conjTranspose_mul, heq]
  have hz : (1 + U).conjTranspose
      * ((cayleyResponse U).conjTranspose + cayleyResponse U) * (1 + U) = 0 := by
    calc _ = ((1 + U).conjTranspose * (cayleyResponse U).conjTranspose) * (1 + U)
            + (1 + U).conjTranspose * (cayleyResponse U * (1 + U)) := by noncomm_ring
      _ = (1 - U).conjTranspose * (1 + U) + (1 + U).conjTranspose * (1 - U) := by
        rw [heq, hdag]
      _ = 2 * (1 - U.conjTranspose * U) := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
          Matrix.conjTranspose_one]
        noncomm_ring
      _ = 0 := by rw [hU]; noncomm_ring
  have hz' : ((cayleyResponse U).conjTranspose + cayleyResponse U) * (1 + U) = 0 := by
    apply mat4_mul_cancel_left (1 + U).conjTranspose _ _ hstar
    simpa only [Matrix.mul_assoc, Matrix.mul_zero] using hz
  have hz'' : (cayleyResponse U).conjTranspose + cayleyResponse U = 0 := by
    apply mat4_mul_cancel_right (1 + U) _ _ ((isUnit_iff_ne_zero).mp hA)
    simpa only [Matrix.zero_mul] using hz'
  exact eq_neg_of_add_eq_zero_left hz''

@[expose] noncomputable def cayleyOperator (U : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (Complex.I + Complex.I) • cayleyResponse U

theorem cayleyOperator_hermitian (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U.conjTranspose * U = 1) (h1 : IsUnit ((1 + U).det)) :
    (cayleyOperator U).conjTranspose = cayleyOperator U := by
  have hsk := cayleyResponse_skew U hU h1
  have hstar : star (Complex.I + Complex.I) = -(Complex.I + Complex.I) := by
    rw [star_add, star_I, neg_add]
  unfold cayleyOperator
  rw [Matrix.conjTranspose_smul, hstar, hsk]
  simp only [neg_smul, smul_neg, neg_neg]

theorem scatteringMatrix4_p_unitarity (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hcons : S.Conservative cfg sus) :
    (scatteringMatrix4_p cfg S).conjTranspose * (scatteringMatrix4_p cfg S) = 1 := by
  have h11 := two_port_unitarity_11 cfg sus S hk hloss hcons
  have h12 := two_port_unitarity_12 cfg sus S hk hloss hcons
  have h21 := two_port_unitarity_21 cfg sus S hk hloss hcons
  have h22 := two_port_unitarity_22 cfg sus S hk hloss hcons
  ext i j
  fin_cases i <;> fin_cases j
  · have e := congrArg (fun M : Ten2 => M 0 0) h11
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 0 1) h11
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 0 0) h12
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 0 1) h12
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 1 0) h11
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 1 1) h11
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 1 0) h12
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 1 1) h12
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 0 0) h21
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 0 1) h21
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 0 0) h22
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 0 1) h22
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 1 0) h21
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 1 1) h21
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 1 0) h22
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e
  · have e := congrArg (fun M : Ten2 => M 1 1) h22
    simp [Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply] at e
    simp [scatteringMatrix4_p, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]
    ring_nf at e ⊢
    exact e

theorem parityExchange_unitary : parityExchange.conjTranspose * parityExchange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parityExchange, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in

@[expose] noncomputable def portImpedance4 (cfg : Config) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![(cfg.upper.eta : ℂ), (cfg.upper.eta : ℂ),
    (cfg.lower.eta : ℂ), (cfg.lower.eta : ℂ)]

@[expose] noncomputable def portScale4 (cfg : Config) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![(Real.sqrt cfg.upper.eta : ℂ), (Real.sqrt cfg.upper.eta : ℂ),
    (Real.sqrt cfg.lower.eta : ℂ), (Real.sqrt cfg.lower.eta : ℂ)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in

theorem twoPort_boundary_reciprocity (cfg : Config) (sus : Susceptibilities)
    (hk : cfg.kPar = 0) (hr : sus.Reciprocal) :
    twoPortIn cfg sus * portImpedance4 cfg * (Kmat (twoPortOut cfg sus)).transpose =
      Kmat (twoPortOut cfg sus) * portImpedance4 cfg * (twoPortIn cfg sus).transpose := by
  have hu : (cfg.upper.eta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt cfg.upper.eta_pos)
  have hl : (cfg.lower.eta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt cfg.lower.eta_pos)
  have he := hr.1 1 0
  have hm := hr.2.1 1 0
  have hx (i j : Fin 3) : sus.em i j = -(sus.me j i) := hr.2.2 i j
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four,
    portImpedance4, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
    simp [twoPortIn, twoPortOut, Kmat,
      boundaryCoeffs_eq_normal cfg _ sus hk,
      boundaryCoeffsNormal, couplingWParNormal, couplingVParNormal,
      Wave.dir, Wave.medium, PropDir.sign, Side.jumpSign,
      waveY_normal_matrix, ncross, iPar, chiTT, he, hm, hx] <;>
    field_simp [hu, hl] <;> ring

theorem scatteringMatrix4_boundary_equation (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0)
    (hgstc : S.Conservative cfg sus) :
    Kmat (twoPortOut cfg sus) * scatteringMatrix4 S = -twoPortIn cfg sus := by
  apply Matrix.mulVec_injective
  funext v
  have h := (gstcSatisfied4_iff_twoPort_eq cfg sus
    (readR v) (S.out1 (readR v) (readT v)) (readT v)
    (S.out2 (readR v) (readT v)) hk).mp (hgstc (readR v) (readT v))
  rw [← scatteringMatrix4_mulVec, pack_unpack] at h
  simpa only [Matrix.mulVec_mulVec, Matrix.neg_mulVec, pack_unpack] using h

private theorem weighted_symmetry (M N D S : Matrix (Fin 4) (Fin 4) ℂ)
    (hdet : M.det ≠ 0) (hMS : M * S = -N)
    (hr : N * D * M.transpose = M * D * N.transpose) :
    S * D = D * S.transpose := by
  have ht : S.transpose * M.transpose = -N.transpose := by
    rw [← Matrix.transpose_mul, hMS, Matrix.transpose_neg]
  apply mat4_mul_cancel_left M _ _ hdet
  apply mat4_mul_cancel_right M.transpose _ _ (by simpa only [Matrix.det_transpose] using hdet)
  calc (M * (S * D)) * M.transpose = (M * S) * D * M.transpose := by noncomm_ring
    _ = -(N * D * M.transpose) := by rw [hMS]; noncomm_ring
    _ = -(M * D * N.transpose) := by rw [hr]
    _ = (M * (D * S.transpose)) * M.transpose := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ht]
      noncomm_ring

private lemma sqrt_balance (cfg : Config) (x y : ℂ)
    (h : x * (cfg.lower.eta : ℂ) = (cfg.upper.eta : ℂ) * y) :
    (((Real.sqrt cfg.lower.eta / Real.sqrt cfg.upper.eta : ℝ) : ℂ) * x) =
    (((Real.sqrt cfg.upper.eta / Real.sqrt cfg.lower.eta : ℝ) : ℂ) * y) := by
  have hu : (Real.sqrt cfg.upper.eta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 cfg.upper.eta_pos))
  have hl : (Real.sqrt cfg.lower.eta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 cfg.lower.eta_pos))
  have hsu : (Real.sqrt cfg.upper.eta : ℂ)^2 = (cfg.upper.eta : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt cfg.upper.eta_pos)]
  have hsl : (Real.sqrt cfg.lower.eta : ℂ)^2 = (cfg.lower.eta : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt cfg.lower.eta_pos)]
  push_cast
  field_simp
  linear_combination h + x * hsl - y * hsu

private lemma normalized_symmetry (cfg : Config) (S : ScatteringMatrix)
    (h : scatteringMatrix4 S * portImpedance4 cfg =
      portImpedance4 cfg * (scatteringMatrix4 S).transpose) :
    (scatteringMatrix4_p cfg S).transpose = scatteringMatrix4_p cfg S := by
  have hu : (cfg.upper.eta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt cfg.upper.eta_pos)
  have hl : (cfg.lower.eta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt cfg.lower.eta_pos)
  have he (i j : Fin 4) := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) h
  simp only [portImpedance4, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply] at he
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact (mul_right_cancel₀ hu (by simpa [scatteringMatrix4, scatteringMatrix4_p, mul_comm] using he 0 1)).symm
  · exact (sqrt_balance cfg _ _ (he 0 2)).symm
  · exact (sqrt_balance cfg _ _ (he 0 3)).symm
  · exact (mul_right_cancel₀ hu (by simpa [scatteringMatrix4, scatteringMatrix4_p, mul_comm] using he 1 0)).symm
  · rfl
  · exact (sqrt_balance cfg _ _ (he 1 2)).symm
  · exact (sqrt_balance cfg _ _ (he 1 3)).symm
  · exact sqrt_balance cfg _ _ (he 0 2)
  · exact sqrt_balance cfg _ _ (he 1 2)
  · rfl
  · exact (mul_right_cancel₀ hl (by simpa [scatteringMatrix4, scatteringMatrix4_p, mul_comm] using he 2 3)).symm
  · exact sqrt_balance cfg _ _ (he 0 3)
  · exact sqrt_balance cfg _ _ (he 1 3)
  · exact (mul_right_cancel₀ hl (by simpa [scatteringMatrix4, scatteringMatrix4_p, mul_comm] using he 3 2)).symm
  · rfl

theorem scatteringMatrix4_weighted_reciprocity (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hr : sus.Reciprocal)
    (hcons : S.Conservative cfg sus)
    (hdet : (Kmat (twoPortOut cfg sus)).det ≠ 0) :
    scatteringMatrix4 S * portImpedance4 cfg =
      portImpedance4 cfg * (scatteringMatrix4 S).transpose :=
  weighted_symmetry _ _ _ _ hdet
    (scatteringMatrix4_boundary_equation cfg sus S hk hcons)
    (twoPort_boundary_reciprocity cfg sus hk hr)

theorem scatteringMatrix4_p_reciprocity_of_conservative
    (cfg : Config) (sus : Susceptibilities) (S : ScatteringMatrix)
    (hk : cfg.kPar = 0) (hr : sus.Reciprocal) (hcons : S.Conservative cfg sus)
    (hdet : (Kmat (twoPortOut cfg sus)).det ≠ 0) :
    (scatteringMatrix4_p cfg S).transpose = scatteringMatrix4_p cfg S :=
  normalized_symmetry cfg S
    (scatteringMatrix4_weighted_reciprocity cfg sus S hk hr hcons hdet)

section ConstitutiveCayley

open scoped ComplexOrder
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

@[expose] noncomputable def biConstitutiveH (cfg : Config) (p : BIParams) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(cfg.vac.eps0 : ℂ)*p.ee00, (cfg.vac.eps0 : ℂ)*p.ee01,
       Complex.I*p.g00/(cfg.vac.c0 : ℂ), Complex.I*p.g01/(cfg.vac.c0 : ℂ);
     (cfg.vac.eps0 : ℂ)*p.ee01, (cfg.vac.eps0 : ℂ)*p.ee11,
       Complex.I*p.g10/(cfg.vac.c0 : ℂ), Complex.I*p.g11/(cfg.vac.c0 : ℂ);
     -Complex.I*p.g00/(cfg.vac.c0 : ℂ), -Complex.I*p.g10/(cfg.vac.c0 : ℂ),
       (cfg.vac.mu0 : ℂ)*p.mm00, (cfg.vac.mu0 : ℂ)*p.mm01;
     -Complex.I*p.g01/(cfg.vac.c0 : ℂ), -Complex.I*p.g11/(cfg.vac.c0 : ℂ),
       (cfg.vac.mu0 : ℂ)*p.mm01, (cfg.vac.mu0 : ℂ)*p.mm11]

@[expose] noncomputable def biMidpointMap4 (cfg : Config) : Matrix (Fin 4) (Fin 4) ℂ :=
  let z : ℂ := Real.sqrt cfg.upper.eta
  !![z/2, 0, z/2, 0; 0, z/2, 0, z/2;
     0, 1/(2*z), 0, -1/(2*z); -1/(2*z), 0, 1/(2*z), 0]
@[expose] noncomputable def biBoundaryRowMap4 (cfg : Config) : Matrix (Fin 4) (Fin 4) ℂ :=
  let z : ℂ := Real.sqrt cfg.upper.eta
  !![1/(2*z), 0, z/2, 0; 0, 1/(2*z), 0, z/2;
     -1/(2*z), 0, z/2, 0; 0, -1/(2*z), 0, z/2]

@[expose] noncomputable def biConstitutiveK (cfg : Config) (p : BIParams) : Matrix (Fin 4) (Fin 4) ℂ :=
  (-2 * (cfg.omega : ℂ)) • ((biMidpointMap4 cfg).conjTranspose * biConstitutiveH cfg p * biMidpointMap4 cfg)
@[expose] noncomputable def biBoundaryA (cfg : Config) (p : BIParams) : Matrix (Fin 4) (Fin 4) ℂ :=
  Kmat (twoPortOut cfg (encode p)) * portScale4 cfg * parityExchange
@[expose] noncomputable def biBoundaryB (cfg : Config) (p : BIParams) : Matrix (Fin 4) (Fin 4) ℂ :=
  twoPortIn cfg (encode p) * portScale4 cfg

theorem biConstitutiveH_hermitian (cfg : Config) (p : BIParams) :
    (biConstitutiveH cfg p).conjTranspose = biConstitutiveH cfg p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [biConstitutiveH, Matrix.conjTranspose_apply, star_div₀, star_mul, star_ofReal, star_I] <;> ring

theorem biConstitutiveK_hermitian (cfg : Config) (p : BIParams) :
    (biConstitutiveK cfg p).conjTranspose = biConstitutiveK cfg p := by
  unfold biConstitutiveK
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, biConstitutiveH_hermitian, star_mul, star_neg,
    star_ofReal, star_ofNat, mul_comm, Matrix.mul_assoc]

theorem bi_constitutive_outgoing (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) :
    biBoundaryRowMap4 cfg * biBoundaryA cfg p =
      -(1 : Matrix (Fin 4) (Fin 4) ℂ) + (Complex.I / 2) • biConstitutiveK cfg p := by
  have hz : (Real.sqrt cfg.upper.eta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 cfg.upper.eta_pos))
  have heta : (cfg.upper.eta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt cfg.upper.eta_pos)
  have hsq : (Real.sqrt cfg.upper.eta : ℂ)^2 = (cfg.upper.eta : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt cfg.upper.eta_pos)]
  unfold biBoundaryA biConstitutiveK twoPortOut
  rw [boundaryCoeffs_eq_normal cfg .above (encode p) hk]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
    Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Kmat, portScale4, parityExchange, boundaryCoeffsNormal,
      couplingWParNormal, couplingVParNormal, Wave.medium, Wave.dir, PropDir.sign,
      Side.jumpSign, waveY_normal_matrix, heq,
      encode, ten3OfTT, chiTT, BIParams.eeBlock, BIParams.mmBlock,
      BIParams.emBlock, BIParams.meBlock, biBoundaryRowMap4, biMidpointMap4, biConstitutiveH,
      ncross, iPar, star_div₀, star_ofReal] <;>
    simp only [← hsq] <;> field_simp [hz] <;> ring

theorem bi_constitutive_incoming (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) :
    biBoundaryRowMap4 cfg * biBoundaryB cfg p =
      (1 : Matrix (Fin 4) (Fin 4) ℂ) + (Complex.I / 2) • biConstitutiveK cfg p := by
  have hz : (Real.sqrt cfg.upper.eta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 cfg.upper.eta_pos))
  have heta : (cfg.upper.eta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt cfg.upper.eta_pos)
  have hsq : (Real.sqrt cfg.upper.eta : ℂ)^2 = (cfg.upper.eta : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt cfg.upper.eta_pos)]
  unfold biBoundaryB biConstitutiveK twoPortIn
  rw [boundaryCoeffs_eq_normal cfg .above (encode p) hk,
    boundaryCoeffs_eq_normal cfg .below (encode p) hk]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
    Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
  fin_cases i <;> fin_cases j <;>
    simp [portScale4, boundaryCoeffsNormal,
      couplingWParNormal, couplingVParNormal, Wave.medium, Wave.dir, PropDir.sign,
      Side.jumpSign, waveY_normal_matrix, heq,
      encode, ten3OfTT, chiTT, BIParams.eeBlock, BIParams.mmBlock,
      BIParams.emBlock, BIParams.meBlock, biBoundaryRowMap4, biMidpointMap4, biConstitutiveH,
      ncross, iPar, star_div₀, star_ofReal] <;>
    simp only [← hsq] <;> field_simp [hz] <;> ring

theorem biBoundaryRowMap4_det_ne_zero (cfg : Config) : (biBoundaryRowMap4 cfg).det ≠ 0 := by
  let z : ℂ := Real.sqrt cfg.upper.eta
  have hz : z ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 cfg.upper.eta_pos))
  dsimp [z] at hz
  let V : Matrix (Fin 4) (Fin 4) ℂ :=
    !![z, 0, -z, 0; 0, z, 0, -z; 1/z, 0, 1/z, 0; 0, 1/z, 0, 1/z]
  have hi : V * biBoundaryRowMap4 cfg = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, biBoundaryRowMap4, ← show (Real.sqrt cfg.upper.eta : ℂ) = z from rfl,
        Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp [hz] <;> ring
  have hd := congrArg Matrix.det hi
  rw [Matrix.det_mul, Matrix.det_one] at hd
  intro hzero
  simp [hzero] at hd

theorem hermitian_cayley4_den_isUnit (K : Matrix (Fin 4) (Fin 4) ℂ) (hK : K.conjTranspose = K) :
    IsUnit ((2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • K).det) := by
  let D := 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • K
  have hgram : D.conjTranspose * D = 4 + K.conjTranspose * K := by
    simp only [D, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_I, hK]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    norm_num [Complex.I_sq]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring_nf
    simp [Complex.I_sq]
  have hpos : (D.conjTranspose * D).PosDef := by
    rw [hgram]
    exact (Matrix.PosDef.natCast 4 (by decide)).add_posSemidef
      (Matrix.posSemidef_conjTranspose_mul_self K)
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit
  rw [Matrix.det_mul] at hd
  apply isUnit_iff_ne_zero.mpr
  intro hz
  exact (isUnit_iff_ne_zero.mp hd) (by rw [hz, mul_zero])

private lemma constitutive_equation_of_row_maps (W A B K C : Matrix (Fin 4) (Fin 4) ℂ)
    (hW : W.det ≠ 0)
    (ha : W*A = -(1/2 : ℂ) • (2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • K))
    (hb : W*B = (1/2 : ℂ) • (2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Complex.I • K)) :
    A*C = -B ↔ (2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • K)*C =
      2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Complex.I • K := by
  constructor
  · intro h
    have hh := congrArg (fun X => W*X) h
    rw [← Matrix.mul_assoc, ha, Matrix.mul_neg, hb, Matrix.smul_mul] at hh
    ext i j
    have he := congrArg (fun X : Matrix (Fin 4) (Fin 4) ℂ => X i j) hh
    simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul] at he
    linear_combination -2 * he
  · intro h
    apply mat4_mul_cancel_left W _ _ hW
    rw [← Matrix.mul_assoc, ha, Matrix.mul_neg, hb, Matrix.smul_mul, h]
    simp only [neg_smul]

theorem bi_constitutive_outgoing_den (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) :
    biBoundaryRowMap4 cfg * biBoundaryA cfg p = -(1/2 : ℂ) •
      (2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • biConstitutiveK cfg p) := by
  rw [bi_constitutive_outgoing cfg p hk heq]
  module
theorem bi_constitutive_incoming_num (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) :
    biBoundaryRowMap4 cfg * biBoundaryB cfg p = (1/2 : ℂ) •
      (2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Complex.I • biConstitutiveK cfg p) := by
  rw [bi_constitutive_incoming cfg p hk heq]
  module
theorem biConstitutiveK_den_isUnit (cfg : Config) (p : BIParams) :
    IsUnit ((2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • biConstitutiveK cfg p).det) :=
  hermitian_cayley4_den_isUnit _ (biConstitutiveK_hermitian cfg p)
theorem biBoundaryA_det_ne_zero (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) :
    (biBoundaryA cfg p).det ≠ 0 := by
  have hd := isUnit_iff_ne_zero.mp (biConstitutiveK_den_isUnit cfg p)
  have he : 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • biConstitutiveK cfg p =
      (-2 : ℂ) • (biBoundaryRowMap4 cfg * biBoundaryA cfg p) := by
    rw [bi_constitutive_outgoing cfg p hk heq]
    module
  intro hz
  apply hd
  rw [he, Matrix.det_smul, Matrix.det_mul, hz, mul_zero, mul_zero]

theorem cayley4_constitutive_equation_iff (K C : Matrix (Fin 4) (Fin 4) ℂ)
    (hD : IsUnit ((2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • K).det)) :
    2 • (C - 1) = Complex.I • (K * (C + 1)) ↔ C = cayley4 K := by
  rw [← cayley4_eq K hD C]
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
  constructor <;> intro h <;> ext i j
  all_goals
    have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) h
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul] at hh ⊢
    linear_combination hh

theorem bi_constitutive_system_iff (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (C : Matrix (Fin 4) (Fin 4) ℂ) :
    biBoundaryA cfg p * C = -biBoundaryB cfg p ↔
      C = cayley4 (biConstitutiveK cfg p) := by
  rw [constitutive_equation_of_row_maps _ _ _ _ C
    (biBoundaryRowMap4_det_ne_zero cfg)
    (bi_constitutive_outgoing_den cfg p hk heq)
    (bi_constitutive_incoming_num cfg p hk heq)]
  exact cayley4_eq _ (biConstitutiveK_den_isUnit cfg p) C

@[expose] noncomputable def biPowerResponse4 (cfg : Config) (p : BIParams) : Matrix (Fin 4) (Fin 4) ℂ :=
  parityExchange * cayley4 (biConstitutiveK cfg p)

theorem bi_cayley_action_iff (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) (a c : Vec4) :
    biBoundaryA cfg p *ᵥ c = -(biBoundaryB cfg p *ᵥ a) ↔
      c = cayley4 (biConstitutiveK cfg p) *ᵥ a := by
  have hmat := (bi_constitutive_system_iff cfg p hk heq
    (cayley4 (biConstitutiveK cfg p))).mpr rfl
  have hs : biBoundaryA cfg p *ᵥ (cayley4 (biConstitutiveK cfg p) *ᵥ a) =
      -(biBoundaryB cfg p *ᵥ a) := by
    rw [Matrix.mulVec_mulVec, hmat, Matrix.neg_mulVec]
  constructor
  · intro h
    exact mulVec_injective_of_det_ne_zero (biBoundaryA_det_ne_zero cfg p hk heq) (h.trans hs.symm)
  · intro h
    rwa [h]

theorem bi_gstc_iff_power_response (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) (a b : Vec4) :
    gstcSatisfied4 cfg (encode p)
      (readR (portScale4 cfg *ᵥ a)) (readR (portScale4 cfg *ᵥ b))
      (readT (portScale4 cfg *ᵥ a)) (readT (portScale4 cfg *ᵥ b)) ↔
      b = biPowerResponse4 cfg p *ᵥ a := by
  have ha : biBoundaryA cfg p * parityExchange =
      Kmat (twoPortOut cfg (encode p)) * portScale4 cfg := by
    unfold biBoundaryA
    rw [Matrix.mul_assoc, parityExchange_sq, Matrix.mul_one]
  have hn : gstcSatisfied4 cfg (encode p)
      (readR (portScale4 cfg *ᵥ a)) (readR (portScale4 cfg *ᵥ b))
      (readT (portScale4 cfg *ᵥ a)) (readT (portScale4 cfg *ᵥ b)) ↔
      biBoundaryA cfg p *ᵥ (parityExchange *ᵥ b) = -(biBoundaryB cfg p *ᵥ a) := by
    rw [gstcSatisfied4_iff_twoPort_eq cfg (encode p) _ _ _ _ hk, pack_unpack, pack_unpack]
    simp only [Matrix.mulVec_mulVec, ha, biBoundaryB]
  rw [hn, bi_cayley_action_iff cfg p hk heq]
  constructor
  · intro h
    have hh := congrArg (fun v : Vec4 => parityExchange *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, parityExchange_sq, Matrix.one_mulVec, biPowerResponse4] using hh
  · intro h
    rw [h, biPowerResponse4]
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, parityExchange_sq, Matrix.one_mul]

theorem portScale4_det_ne_zero (cfg : Config) : (portScale4 cfg).det ≠ 0 := by
  have hu : (Real.sqrt cfg.upper.eta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 cfg.upper.eta_pos))
  have hl : (Real.sqrt cfg.lower.eta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 cfg.lower.eta_pos))
  simp [portScale4, Matrix.det_diagonal, Fin.prod_univ_succ, hu, hl]

@[expose] noncomputable def biRawResponse4 (cfg : Config) (p : BIParams) : Matrix (Fin 4) (Fin 4) ℂ :=
  portScale4 cfg * biPowerResponse4 cfg p * (portScale4 cfg)⁻¹

theorem bi_gstc_iff_raw_response (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) (a b : Vec4) :
    gstcSatisfied4 cfg (encode p) (readR a) (readR b) (readT a) (readT b) ↔
      b = biRawResponse4 cfg p *ᵥ a := by
  have hL := isUnit_iff_ne_zero.mpr (portScale4_det_ne_zero cfg)
  have h := bi_gstc_iff_power_response cfg p hk heq ((portScale4 cfg)⁻¹ *ᵥ a) ((portScale4 cfg)⁻¹ *ᵥ b)
  simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hL, Matrix.one_mulVec] at h
  rw [h]
  constructor
  · intro hb
    calc b = portScale4 cfg *ᵥ ((portScale4 cfg)⁻¹ *ᵥ b) := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hL, Matrix.one_mulVec]
      _ = portScale4 cfg *ᵥ (biPowerResponse4 cfg p *ᵥ ((portScale4 cfg)⁻¹ *ᵥ a)) := by rw [hb]; simp only [Matrix.mulVec_mulVec]
      _ = biRawResponse4 cfg p *ᵥ a := by simp only [biRawResponse4, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · intro hb
    rw [hb, biRawResponse4]
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hL, Matrix.one_mul]

theorem bi_unique_scattering (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) (a : Vec4) :
    ∃! b : Vec4, gstcSatisfied4 cfg (encode p) (readR a) (readR b) (readT a) (readT b) := by
  refine ⟨biRawResponse4 cfg p *ᵥ a, (bi_gstc_iff_raw_response cfg p hk heq a _).mpr rfl, ?_⟩
  intro b hb
  exact (bi_gstc_iff_raw_response cfg p hk heq a b).mp hb

theorem portScale4_eq_scalar (cfg : Config) (heq : cfg.lower.eta = cfg.upper.eta) :
    portScale4 cfg = (Real.sqrt cfg.upper.eta : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [portScale4, heq]

theorem bi_boundary_det_ne_zero (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) :
    (Kmat (twoPortOut cfg (encode p))).det ≠ 0 := by
  intro hz
  apply biBoundaryA_det_ne_zero cfg p hk heq
  simp only [biBoundaryA, Matrix.det_mul, hz, zero_mul]

@[expose] def biZeroParams : BIParams := ⟨0,0,0,0,0,0,0,0,0,0⟩

theorem biConstitutiveK_zero (cfg : Config) : biConstitutiveK cfg biZeroParams = 0 := by
  have hH : biConstitutiveH cfg biZeroParams = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [biConstitutiveH, biZeroParams]
  simp only [biConstitutiveK, hH, Matrix.mul_zero, Matrix.zero_mul, smul_zero]

theorem bi_cayley_zero (cfg : Config) : cayley4 (biConstitutiveK cfg biZeroParams) = 1 := by
  rw [biConstitutiveK_zero]
  have hd : IsUnit ((2 • (1 : Matrix (Fin 4) (Fin 4) ℂ)).det) := by
    simpa using hermitian_cayley4_den_isUnit 0 (by simp)
  simp only [cayley4, smul_zero, sub_zero, add_zero]
  exact Matrix.nonsing_inv_mul _ hd

end ConstitutiveCayley

end GSTC.Scattering
