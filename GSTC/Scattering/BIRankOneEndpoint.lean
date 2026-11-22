/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Matrix

public section
set_option autoImplicit false

namespace GSTC.Scattering.BIRankOneEndpoint

open scoped Matrix

theorem gram_eq_zero_imp (Z : Ten2) (h : Z * Z.conjTranspose = 0) : Z = 0 := by
  ext i j
  have hii := congrArg (fun M => M i i) h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Matrix.zero_apply] at hii
  have hc0 : Z i 0 * star (Z i 0) = (↑(Complex.normSq (Z i 0)) : ℂ) := by
    rw [mul_comm]; exact Complex.normSq_eq_conj_mul_self.symm
  have hc1 : Z i 1 * star (Z i 1) = (↑(Complex.normSq (Z i 1)) : ℂ) := by
    rw [mul_comm]; exact Complex.normSq_eq_conj_mul_self.symm
  have hsum : (↑(Complex.normSq (Z i 0)) : ℂ) + (↑(Complex.normSq (Z i 1)) : ℂ) = 0 := by
    rw [← hc0, ← hc1]; exact hii
  have hre : Complex.normSq (Z i 0) + Complex.normSq (Z i 1) = 0 := by
    exact_mod_cast hsum
  have h0 : Z i 0 = 0 := Complex.normSq_eq_zero.mp (by
    linarith [Complex.normSq_nonneg (Z i 0), Complex.normSq_nonneg (Z i 1)])
  have h1 : Z i 1 = 0 := Complex.normSq_eq_zero.mp (by
    linarith [Complex.normSq_nonneg (Z i 0), Complex.normSq_nonneg (Z i 1)])
  fin_cases j
  · exact h0
  · exact h1

theorem mixed_eq_zero_imp (X Y : Ten2) (hX : X.det ≠ 0)
    (h : X.transpose * Y.conjTranspose = 0) : Y = 0 := by
  have hXt : (X.transpose).det ≠ 0 := by rw [Matrix.det_transpose]; exact hX
  have hunit : IsUnit (X.transpose).det := isUnit_iff_ne_zero.mpr hXt
  have hY : Y.conjTranspose = 0 := by
    calc Y.conjTranspose = (X.transpose)⁻¹ * (X.transpose * Y.conjTranspose) :=
          (Matrix.nonsing_inv_mul_cancel_left _ _ hunit).symm
      _ = 0 := by rw [h, Matrix.mul_zero]
  calc Y = (Y.conjTranspose).conjTranspose := by rw [Matrix.conjTranspose_conjTranspose]
    _ = 0 := by rw [hY, Matrix.conjTranspose_zero]

theorem map_star_transpose_mul_map_star (X : Ten2) :
    (X.transpose * X.map star).map star = X.conjTranspose * X := by
  ext i j
  simp [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two]

theorem map_star_conjTranspose_mul (X : Ten2) :
    (X.conjTranspose * X).map star = X.transpose * X.map star := by
  ext i j
  simp [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two]

theorem transpose_mul_conj_eq_one_iff (X : Ten2) :
    X.transpose * X.map star = 1 ↔ X.conjTranspose * X = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun M => M.map star) h
    rw [map_star_transpose_mul_map_star] at h'
    simpa using h'
  · intro h
    have h' := congrArg (fun M => M.map star) h
    rw [map_star_conjTranspose_mul] at h'
    simpa using h'

end GSTC.Scattering.BIRankOneEndpoint
