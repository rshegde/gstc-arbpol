/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIInverseCompleteness
public import GSTC.Scattering.NBTakagiExistence

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

public section
set_option autoImplicit false

namespace GSTC.Scattering.BIRankOneCompletion
open scoped Matrix ComplexOrder
open Matrix

@[expose] def projection (n : Vec2) : Ten2 := vecMulVec n (star n)
@[expose] def symmetricOuter (n : Vec2) : Ten2 := vecMulVec n n

theorem projection_square (n : Vec2) (hn : star n ⬝ᵥ n = 1) :
    projection n * projection n = projection n := by
  rw [projection, vecMulVec_mul_vecMulVec, hn, one_smul]

theorem projection_trace (n : Vec2) (hn : star n ⬝ᵥ n = 1) :
    Matrix.trace (projection n) = 1 := by
  rw [projection, trace_vecMulVec, dotProduct_comm]
  exact hn

theorem symmetricOuter_symmetric (n : Vec2) :
    (symmetricOuter n).transpose = symmetricOuter n := transpose_vecMulVec n n

theorem symmetricOuter_gram (n : Vec2) (hn : star n ⬝ᵥ n = 1) (c : ℂ) :
    (c • symmetricOuter n) * (c • symmetricOuter n).conjTranspose =
      (Complex.normSq c : ℂ) • projection n := by
  rw [Matrix.conjTranspose_smul, symmetricOuter, conjTranspose_vecMulVec,
    Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, dotProduct_comm n (star n), hn]
  simp only [one_smul, smul_smul]
  congr 1
  exact Complex.mul_conj c

theorem symmetric_rank_one_scalar (Z : Ten2) (n : Vec2) (d : ℝ)
    (hn : star n ⬝ᵥ n = 1) (hs : Z.transpose = Z)
    (hg : Z * Z.conjTranspose = (d : ℂ) • projection n) :
    ∃ c : ℂ, Z = c • symmetricOuter n ∧ Complex.normSq c = d := by
  have hz : (1-projection n) * Z = 0 := by
    apply (Matrix.mul_self_mul_conjTranspose_eq_zero Z (1-projection n)).mp
    rw [hg, Matrix.mul_smul, Matrix.sub_mul, Matrix.one_mul, projection_square n hn, sub_self, smul_zero]
  have hl : projection n * Z = Z := by
    rw [Matrix.sub_mul, Matrix.one_mul] at hz
    exact (sub_eq_zero.mp hz).symm
  have hr : Z * (projection n).transpose = Z := by
    have h := congrArg Matrix.transpose hl
    simpa only [Matrix.transpose_mul, hs] using h
  let c := star n ⬝ᵥ (Z *ᵥ star n)
  have he : Z = c • symmetricOuter n := by
    calc Z = projection n * Z * (projection n).transpose := by rw [hl,hr]
         _ = c • symmetricOuter n := by
           ext i j
           simp [projection, symmetricOuter, c, Matrix.mul_apply, Matrix.mulVec,
             dotProduct, Fin.sum_univ_two, Matrix.vecMulVec]
           ring
  refine ⟨c,he,?_⟩
  rw [he, symmetricOuter_gram n hn c] at hg
  have ht := congrArg Matrix.trace hg
  simp only [Matrix.trace_smul, projection_trace n hn, smul_eq_mul, mul_one] at ht
  exact Complex.ofReal_injective ht

theorem symmetric_rank_one_phase (Z : Ten2) (n : Vec2) (d : ℝ)
    (hn : star n ⬝ᵥ n = 1) (hs : Z.transpose = Z)
    (hg : Z * Z.conjTranspose = (d : ℂ) • projection n) :
    ∃ θ : ℝ, Z = (Complex.exp ((θ : ℂ)*Complex.I) * (Real.sqrt d : ℂ)) • symmetricOuter n := by
  obtain ⟨c,hc,hd⟩ := symmetric_rank_one_scalar Z n d hn hs hg
  have hnorm : ‖c‖ = Real.sqrt d := by
    rw [← hd, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg c)]
  have he := Complex.norm_mul_exp_arg_mul_I c
  rw [hnorm] at he
  refine ⟨c.arg,?_⟩
  rw [hc, mul_comm (Complex.exp _) _, he]

theorem phase_rank_one_gram (n : Vec2) (d θ : ℝ) (hn : star n ⬝ᵥ n = 1) (hd : 0 ≤ d) :
    let Z := (Complex.exp ((θ : ℂ)*Complex.I) * (Real.sqrt d : ℂ)) • symmetricOuter n
    Z.transpose = Z ∧ Z*Z.conjTranspose = (d : ℂ) • projection n := by
  constructor
  · rw [Matrix.transpose_smul, symmetricOuter_symmetric]
  · rw [symmetricOuter_gram n hn]
    congr 1
    congr 1
    have hp : ‖Complex.exp ((θ : ℂ)*Complex.I)‖ = 1 := by simp [Complex.norm_exp]
    rw [Complex.normSq_eq_norm_sq, norm_mul, hp, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg d), Real.sq_sqrt hd]

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ

@[expose] def block (A B C D : Ten2) : Mat4 := scatteringMatrix4 ⟨A,B,C,D⟩
@[expose] def completion (X Z Y : Ten2) : Mat4 := block Z X.transpose X Y

theorem block_mul (A B C D E F G H : Ten2) :
    block A B C D * block E F G H =
      block (A*E+B*G) (A*F+B*H) (C*E+D*G) (C*F+D*H) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, scatteringMatrix4, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, add_assoc]

theorem block_adjoint (A B C D : Ten2) :
    (block A B C D).conjTranspose = block A.conjTranspose C.conjTranspose B.conjTranspose D.conjTranspose := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem block_transpose (A B C D : Ten2) :
    (block A B C D).transpose = block A.transpose C.transpose B.transpose D.transpose := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem block_one : block 1 0 0 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem block_eq_iff (A B C D E F G H : Ten2) :
    block A B C D = block E F G H ↔ A=E ∧ B=F ∧ C=G ∧ D=H := by
  constructor
  · intro h
    have he (i j : Fin 4) := congrArg (fun M : Mat4 => M i j) h
    refine ⟨?_,?_,?_,?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        first | exact he 0 0 | exact he 0 1 | exact he 1 0 | exact he 1 1
    · ext i j
      fin_cases i <;> fin_cases j <;>
        first | exact he 0 2 | exact he 0 3 | exact he 1 2 | exact he 1 3
    · ext i j
      fin_cases i <;> fin_cases j <;>
        first | exact he 2 0 | exact he 2 1 | exact he 3 0 | exact he 3 1
    · ext i j
      fin_cases i <;> fin_cases j <;>
        first | exact he 2 2 | exact he 2 3 | exact he 3 2 | exact he 3 3
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    rfl

theorem completion_symmetric_iff (X Z Y : Ten2) :
    (completion X Z Y).transpose = completion X Z Y ↔ Z.transpose=Z ∧ Y.transpose=Y := by
  simp only [completion, block_transpose, block_eq_iff, Matrix.transpose_transpose,
    true_and, eq_self]

theorem completion_unitary_iff (X Z Y : Ten2) :
    (completion X Z Y).conjTranspose * completion X Z Y = 1 ↔
      Z*Z.conjTranspose + X.transpose*X.map star = 1 ∧
      Z*X.conjTranspose + X.transpose*Y.conjTranspose = 0 ∧
      X*Z.conjTranspose + Y*X.map star = 0 ∧
      X*X.conjTranspose + Y*Y.conjTranspose = 1 := by
  rw [mul_eq_one_comm]
  simp only [completion, block_adjoint, block_mul, Matrix.transpose_conjTranspose]
  rw [← block_one, block_eq_iff]

@[expose] noncomputable def forcedY (X Z : Ten2) : Ten2 :=
  -(X.conjTranspose)⁻¹ * Z.conjTranspose * X.transpose

theorem mixed_equation_iff (X Z Y : Ten2) (hX : X.det ≠ 0) :
    X.conjTranspose*Y + Z.conjTranspose*X.transpose = 0 ↔ Y = forcedY X Z := by
  have ha : X.conjTranspose.det ≠ 0 := by simpa using hX
  have hj := Matrix.mul_nonsing_inv X.conjTranspose (isUnit_iff_ne_zero.mpr ha)
  have hf : X.conjTranspose * forcedY X Z = -(Z.conjTranspose*X.transpose) := by
    simp only [forcedY, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, hj, Matrix.one_mul]
  constructor
  · intro h
    apply nb_mul_cancel_left X.conjTranspose _ _ ha
    rw [hf]
    exact eq_neg_of_add_eq_zero_left h
  · rintro rfl
    rw [hf]
    abel

theorem forcedY_eq_requested (X Z : Ten2) (hZ : Z.transpose=Z) :
    forcedY X Z = -((X.transpose).map star)⁻¹ * Z.map star * X.transpose := by
  rw [forcedY, conjTranspose_eq_map_star_of_symmetric hZ]
  rfl

theorem completion_from_reflection_gram (X Z : Ten2) (hX : X.det ≠ 0)
    (hZ : Z.transpose=Z) (hg : Z*Z.conjTranspose + X.transpose*X.map star=1) :
    (completion X Z (forcedY X Z)).transpose = completion X Z (forcedY X Z) ∧
    (completion X Z (forcedY X Z)).conjTranspose * completion X Z (forcedY X Z) = 1 := by
  let Y := forcedY X Z
  have hA : X.conjTranspose.det ≠ 0 := by simpa using hX
  have hU : (X.map star).det ≠ 0 := by
    have hh : (X.map star).transpose.det ≠ 0 := by simpa only [map_star_transpose] using hA
    simpa only [Matrix.det_transpose] using hh
  have hH : Z.conjTranspose.transpose = Z.conjTranspose := by
    rw [← Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, hZ]
  have hm : X.conjTranspose*Y = -(Z.conjTranspose*X.transpose) := by
    have h := (mixed_equation_iff X Z Y hX).mpr rfl
    exact eq_neg_of_add_eq_zero_left h
  have ht : Y.transpose * X.map star = -(X*Z.conjTranspose) := by
    have hh := congrArg Matrix.transpose hm
    simpa only [Matrix.transpose_mul, Matrix.conjTranspose_transpose,
      Matrix.transpose_neg, Matrix.transpose_transpose, hH] using hh
  have hgc : Z.conjTranspose*Z + X.conjTranspose*X = 1 := by
    have hh := congrArg Matrix.transpose hg
    simpa only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.transpose_transpose, map_star_transpose, hH, hZ] using hh
  have hAX : X.conjTranspose*X = 1-Z.conjTranspose*Z := by rw [← hgc]; noncomm_ring
  have hBU : X.transpose*X.map star = 1-Z*Z.conjTranspose := by rw [← hg]; noncomm_ring
  have hc : (X.conjTranspose*X)*Z.conjTranspose = Z.conjTranspose*(X.transpose*X.map star) := by
    rw [hAX,hBU]
    noncomm_ring
  have hy : Y.transpose=Y := by
    apply nb_mul_cancel_right (X.map star) _ _ hU
    apply nb_mul_cancel_left X.conjTranspose _ _ hA
    rw [ht, ← Matrix.mul_assoc X.conjTranspose Y, hm]
    simpa only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc] using congrArg Neg.neg hc
  have h21 : X*Z.conjTranspose + Y*X.map star = 0 := by rw [hy] at ht; rw [ht]; abel
  have h12 : Z*X.conjTranspose + X.transpose*Y.conjTranspose = 0 := by
    have hh := congrArg Matrix.conjTranspose h21
    simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero,
      show (X.map star).conjTranspose=X.transpose from by ext i j; simp] using hh
  have hYX : Y.conjTranspose*X = -(X.map star*Z) := by
    have hh := congrArg Matrix.conjTranspose hm
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose, Matrix.transpose_conjTranspose] using hh
  have h22 : X*X.conjTranspose + Y*Y.conjTranspose = 1 := by
    apply nb_mul_cancel_right X _ _ hX
    apply nb_mul_cancel_left X.conjTranspose _ _ hA
    calc _ = (X.conjTranspose*X)*(X.conjTranspose*X) + (X.conjTranspose*Y)*(Y.conjTranspose*X) := by
           noncomm_ring
         _ = (X.conjTranspose*X)*(X.conjTranspose*X) + Z.conjTranspose*(X.transpose*X.map star)*Z := by
           rw [hm,hYX]; noncomm_ring
         _ = 1-Z.conjTranspose*Z := by rw [hAX,hBU]; noncomm_ring
         _ = _ := by simpa only [Matrix.one_mul] using hAX.symm
  exact ⟨(completion_symmetric_iff X Z Y).mpr ⟨hZ,hy⟩,
    (completion_unitary_iff X Z Y).mpr ⟨hg,h12,h21,h22⟩⟩

end GSTC.Scattering.BIRankOneCompletion
