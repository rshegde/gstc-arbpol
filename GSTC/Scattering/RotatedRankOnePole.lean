/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module
public import GSTC.Scattering.RotatedRankOneRecovery

public section
set_option autoImplicit false
namespace GSTC.Scattering.RotatedRankOneRecovery
open scoped Matrix
open Matrix BIInverse RotatedRankOneResources

theorem rotatedC_det (s r c j x y h k : ℝ)
    (hr : r^2+s^2=1) (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hb : k^2+h^2=1) :
    (1 + rotatedC s r c j x y h k).det =
      2 * ((x : ℂ) + Complex.I * (y : ℂ))^2 * (rotF s c x y : ℂ) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  norm_num [rotatedC, Fin.succAbove]
  apply Complex.ext
  · simp only [rotF, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_sub]
    norm_num only [Complex.re_ofNat, Complex.im_ofNat]
    ring_nf
    linear_combination ((((c) ^ 2 * (h) ^ 2 * (x) ^ 2) + ((c) ^ 2 * (k) ^ 2 * (x) ^ 2) + ((c) ^ 4 * (h) ^ 2 * (x) ^ 4) + ((c) ^ 4 * (h) ^ 2 * (y) ^ 4) + ((c) ^ 4 * (k) ^ 2 * (x) ^ 4) + ((c) ^ 4 * (k) ^ 2 * (y) ^ 4) + ((h) ^ 2 * (j) ^ 4 * (x) ^ 4) + ((h) ^ 2 * (j) ^ 4 * (y) ^ 4) + ((j) ^ 4 * (k) ^ 2 * (x) ^ 4) + ((j) ^ 4 * (k) ^ 2 * (y) ^ 4) + (-1 * (c) ^ 2 * (h) ^ 2 * (y) ^ 2) + (-1 * (c) ^ 2 * (k) ^ 2 * (y) ^ 2) + (2 * (c) ^ 3 * (h) ^ 2 * (x) ^ 3) + (2 * (c) ^ 3 * (k) ^ 2 * (x) ^ 3) + (-6 * x * (c) ^ 3 * (h) ^ 2 * (y) ^ 2) + (-6 * x * (c) ^ 3 * (k) ^ 2 * (y) ^ 2) + (-6 * (c) ^ 4 * (h) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-6 * (c) ^ 4 * (k) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-6 * (h) ^ 2 * (j) ^ 4 * (x) ^ 2 * (y) ^ 2) + (-6 * (j) ^ 4 * (k) ^ 2 * (x) ^ 2 * (y) ^ 2) + (2 * c * (h) ^ 2 * (j) ^ 2 * (x) ^ 3) + (2 * c * (j) ^ 2 * (k) ^ 2 * (x) ^ 3) + (2 * (c) ^ 2 * (h) ^ 2 * (j) ^ 2 * (x) ^ 4) + (2 * (c) ^ 2 * (h) ^ 2 * (j) ^ 2 * (y) ^ 4) + (2 * (c) ^ 2 * (j) ^ 2 * (k) ^ 2 * (x) ^ 4) + (2 * (c) ^ 2 * (j) ^ 2 * (k) ^ 2 * (y) ^ 4) + (-12 * (c) ^ 2 * (h) ^ 2 * (j) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-12 * (c) ^ 2 * (j) ^ 2 * (k) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-6 * c * x * (h) ^ 2 * (j) ^ 2 * (y) ^ 2) + (-6 * c * x * (j) ^ 2 * (k) ^ 2 * (y) ^ 2))) * hr + ((((h) ^ 2 * (x) ^ 4) + ((h) ^ 2 * (y) ^ 4) + ((k) ^ 2 * (x) ^ 4) + ((k) ^ 2 * (y) ^ 4) + ((s) ^ 2 * (x) ^ 4) + ((s) ^ 2 * (y) ^ 4) + (-2 * s * (y) ^ 2) + (2 * s * (x) ^ 2) + ((c) ^ 2 * (h) ^ 2 * (x) ^ 4) + ((c) ^ 2 * (h) ^ 2 * (y) ^ 4) + ((c) ^ 2 * (k) ^ 2 * (x) ^ 4) + ((c) ^ 2 * (k) ^ 2 * (y) ^ 4) + ((c) ^ 2 * (s) ^ 2 * (x) ^ 4) + ((c) ^ 2 * (s) ^ 2 * (y) ^ 4) + ((h) ^ 2 * (j) ^ 2 * (x) ^ 4) + ((h) ^ 2 * (j) ^ 2 * (y) ^ 4) + ((j) ^ 2 * (k) ^ 2 * (x) ^ 4) + ((j) ^ 2 * (k) ^ 2 * (y) ^ 4) + ((j) ^ 2 * (s) ^ 2 * (x) ^ 4) + ((j) ^ 2 * (s) ^ 2 * (y) ^ 4) + (-1 * (h) ^ 2 * (s) ^ 2 * (x) ^ 4) + (-1 * (h) ^ 2 * (s) ^ 2 * (y) ^ 4) + (-1 * (k) ^ 2 * (s) ^ 2 * (x) ^ 4) + (-1 * (k) ^ 2 * (s) ^ 2 * (y) ^ 4) + (-6 * (h) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-6 * (k) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-6 * (s) ^ 2 * (x) ^ 2 * (y) ^ 2) + (2 * c * s * (x) ^ 3) + (2 * c * (h) ^ 2 * (x) ^ 3) + (2 * c * (k) ^ 2 * (x) ^ 3) + (2 * c * (s) ^ 2 * (x) ^ 3) + (-1 * (c) ^ 2 * (h) ^ 2 * (s) ^ 2 * (x) ^ 4) + (-1 * (c) ^ 2 * (h) ^ 2 * (s) ^ 2 * (y) ^ 4) + (-1 * (c) ^ 2 * (k) ^ 2 * (s) ^ 2 * (x) ^ 4) + (-1 * (c) ^ 2 * (k) ^ 2 * (s) ^ 2 * (y) ^ 4) + (-1 * (h) ^ 2 * (j) ^ 2 * (s) ^ 2 * (x) ^ 4) + (-1 * (h) ^ 2 * (j) ^ 2 * (s) ^ 2 * (y) ^ 4) + (-1 * (j) ^ 2 * (k) ^ 2 * (s) ^ 2 * (x) ^ 4) + (-1 * (j) ^ 2 * (k) ^ 2 * (s) ^ 2 * (y) ^ 4) + (-6 * c * s * x * (y) ^ 2) + (-6 * c * x * (h) ^ 2 * (y) ^ 2) + (-6 * c * x * (k) ^ 2 * (y) ^ 2) + (-6 * c * x * (s) ^ 2 * (y) ^ 2) + (-6 * (c) ^ 2 * (h) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-6 * (c) ^ 2 * (k) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-6 * (c) ^ 2 * (s) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-6 * (h) ^ 2 * (j) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-6 * (j) ^ 2 * (k) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-6 * (j) ^ 2 * (s) ^ 2 * (x) ^ 2 * (y) ^ 2) + (-2 * c * (h) ^ 2 * (s) ^ 2 * (x) ^ 3) + (-2 * c * (k) ^ 2 * (s) ^ 2 * (x) ^ 3) + (6 * (h) ^ 2 * (s) ^ 2 * (x) ^ 2 * (y) ^ 2) + (6 * (k) ^ 2 * (s) ^ 2 * (x) ^ 2 * (y) ^ 2) + (6 * c * x * (h) ^ 2 * (s) ^ 2 * (y) ^ 2) + (6 * c * x * (k) ^ 2 * (s) ^ 2 * (y) ^ 2) + (6 * (c) ^ 2 * (h) ^ 2 * (s) ^ 2 * (x) ^ 2 * (y) ^ 2) + (6 * (c) ^ 2 * (k) ^ 2 * (s) ^ 2 * (x) ^ 2 * (y) ^ 2) + (6 * (h) ^ 2 * (j) ^ 2 * (s) ^ 2 * (x) ^ 2 * (y) ^ 2) + (6 * (j) ^ 2 * (k) ^ 2 * (s) ^ 2 * (x) ^ 2 * (y) ^ 2))) * hc + ((-2 + (c) ^ 2 + (h) ^ 2 + (k) ^ 2 + (s) ^ 2 + (-2 * (y) ^ 2) + (6 * (x) ^ 2) + ((h) ^ 2 * (y) ^ 2) + ((k) ^ 2 * (y) ^ 2) + ((s) ^ 2 * (y) ^ 2) + (-1 * (c) ^ 2 * (h) ^ 2) + (-1 * (c) ^ 2 * (k) ^ 2) + (-1 * (c) ^ 2 * (s) ^ 2) + (-1 * (h) ^ 2 * (s) ^ 2) + (-1 * (k) ^ 2 * (s) ^ 2) + (-7 * (h) ^ 2 * (x) ^ 2) + (-7 * (k) ^ 2 * (x) ^ 2) + (-7 * (s) ^ 2 * (x) ^ 2) + (-2 * s * (x) ^ 2) + (2 * s * (y) ^ 2) + (4 * c * x) + ((c) ^ 2 * (h) ^ 2 * (s) ^ 2) + ((c) ^ 2 * (k) ^ 2 * (s) ^ 2) + (-1 * (h) ^ 2 * (s) ^ 2 * (y) ^ 2) + (-1 * (k) ^ 2 * (s) ^ 2 * (y) ^ 2) + (-6 * c * x * (h) ^ 2) + (-6 * c * x * (k) ^ 2) + (-6 * c * x * (s) ^ 2) + (-2 * c * s * x) + (7 * (h) ^ 2 * (s) ^ 2 * (x) ^ 2) + (7 * (k) ^ 2 * (s) ^ 2 * (x) ^ 2) + (6 * c * x * (h) ^ 2 * (s) ^ 2) + (6 * c * x * (k) ^ 2 * (s) ^ 2))) * hx + ((1 + (-1 * (c) ^ 2) + (-1 * (s) ^ 2) + (-8 * (x) ^ 2) + (8 * (x) ^ 4) + ((c) ^ 2 * (s) ^ 2) + (-8 * (s) ^ 2 * (x) ^ 4) + (-6 * c * x) + (2 * (c) ^ 2 * (x) ^ 2) + (8 * c * (x) ^ 3) + (8 * (s) ^ 2 * (x) ^ 2) + (-8 * c * (s) ^ 2 * (x) ^ 3) + (-2 * (c) ^ 2 * (s) ^ 2 * (x) ^ 2) + (6 * c * x * (s) ^ 2))) * hb
  · simp only [rotF, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_sub]
    norm_num only [Complex.re_ofNat, Complex.im_ofNat]
    ring_nf
    linear_combination (((-2 * (c) ^ 3 * (h) ^ 2 * (y) ^ 3) + (-2 * (c) ^ 3 * (k) ^ 2 * (y) ^ 3) + (-4 * x * (c) ^ 4 * (h) ^ 2 * (y) ^ 3) + (-4 * x * (c) ^ 4 * (k) ^ 2 * (y) ^ 3) + (-4 * x * (h) ^ 2 * (j) ^ 4 * (y) ^ 3) + (-4 * x * (j) ^ 4 * (k) ^ 2 * (y) ^ 3) + (-2 * c * (h) ^ 2 * (j) ^ 2 * (y) ^ 3) + (-2 * c * (j) ^ 2 * (k) ^ 2 * (y) ^ 3) + (2 * x * y * (c) ^ 2 * (h) ^ 2) + (2 * x * y * (c) ^ 2 * (k) ^ 2) + (4 * y * (c) ^ 4 * (h) ^ 2 * (x) ^ 3) + (4 * y * (c) ^ 4 * (k) ^ 2 * (x) ^ 3) + (4 * y * (h) ^ 2 * (j) ^ 4 * (x) ^ 3) + (4 * y * (j) ^ 4 * (k) ^ 2 * (x) ^ 3) + (6 * y * (c) ^ 3 * (h) ^ 2 * (x) ^ 2) + (6 * y * (c) ^ 3 * (k) ^ 2 * (x) ^ 2) + (-8 * x * (c) ^ 2 * (h) ^ 2 * (j) ^ 2 * (y) ^ 3) + (-8 * x * (c) ^ 2 * (j) ^ 2 * (k) ^ 2 * (y) ^ 3) + (6 * c * y * (h) ^ 2 * (j) ^ 2 * (x) ^ 2) + (6 * c * y * (j) ^ 2 * (k) ^ 2 * (x) ^ 2) + (8 * y * (c) ^ 2 * (h) ^ 2 * (j) ^ 2 * (x) ^ 3) + (8 * y * (c) ^ 2 * (j) ^ 2 * (k) ^ 2 * (x) ^ 3))) * hr + (((-4 * x * (h) ^ 2 * (y) ^ 3) + (-4 * x * (k) ^ 2 * (y) ^ 3) + (-4 * x * (s) ^ 2 * (y) ^ 3) + (-2 * c * s * (y) ^ 3) + (-2 * c * (h) ^ 2 * (y) ^ 3) + (-2 * c * (k) ^ 2 * (y) ^ 3) + (-2 * c * (s) ^ 2 * (y) ^ 3) + (4 * s * x * y) + (4 * y * (h) ^ 2 * (x) ^ 3) + (4 * y * (k) ^ 2 * (x) ^ 3) + (4 * y * (s) ^ 2 * (x) ^ 3) + (-4 * x * (c) ^ 2 * (h) ^ 2 * (y) ^ 3) + (-4 * x * (c) ^ 2 * (k) ^ 2 * (y) ^ 3) + (-4 * x * (c) ^ 2 * (s) ^ 2 * (y) ^ 3) + (-4 * x * (h) ^ 2 * (j) ^ 2 * (y) ^ 3) + (-4 * x * (j) ^ 2 * (k) ^ 2 * (y) ^ 3) + (-4 * x * (j) ^ 2 * (s) ^ 2 * (y) ^ 3) + (-4 * y * (h) ^ 2 * (s) ^ 2 * (x) ^ 3) + (-4 * y * (k) ^ 2 * (s) ^ 2 * (x) ^ 3) + (2 * c * (h) ^ 2 * (s) ^ 2 * (y) ^ 3) + (2 * c * (k) ^ 2 * (s) ^ 2 * (y) ^ 3) + (4 * x * (h) ^ 2 * (s) ^ 2 * (y) ^ 3) + (4 * x * (k) ^ 2 * (s) ^ 2 * (y) ^ 3) + (4 * y * (c) ^ 2 * (h) ^ 2 * (x) ^ 3) + (4 * y * (c) ^ 2 * (k) ^ 2 * (x) ^ 3) + (4 * y * (c) ^ 2 * (s) ^ 2 * (x) ^ 3) + (4 * y * (h) ^ 2 * (j) ^ 2 * (x) ^ 3) + (4 * y * (j) ^ 2 * (k) ^ 2 * (x) ^ 3) + (4 * y * (j) ^ 2 * (s) ^ 2 * (x) ^ 3) + (6 * c * s * y * (x) ^ 2) + (6 * c * y * (h) ^ 2 * (x) ^ 2) + (6 * c * y * (k) ^ 2 * (x) ^ 2) + (6 * c * y * (s) ^ 2 * (x) ^ 2) + (-6 * c * y * (h) ^ 2 * (s) ^ 2 * (x) ^ 2) + (-6 * c * y * (k) ^ 2 * (s) ^ 2 * (x) ^ 2) + (-4 * y * (c) ^ 2 * (h) ^ 2 * (s) ^ 2 * (x) ^ 3) + (-4 * y * (c) ^ 2 * (k) ^ 2 * (s) ^ 2 * (x) ^ 3) + (-4 * y * (h) ^ 2 * (j) ^ 2 * (s) ^ 2 * (x) ^ 3) + (-4 * y * (j) ^ 2 * (k) ^ 2 * (s) ^ 2 * (x) ^ 3) + (4 * x * (c) ^ 2 * (h) ^ 2 * (s) ^ 2 * (y) ^ 3) + (4 * x * (c) ^ 2 * (k) ^ 2 * (s) ^ 2 * (y) ^ 3) + (4 * x * (h) ^ 2 * (j) ^ 2 * (s) ^ 2 * (y) ^ 3) + (4 * x * (j) ^ 2 * (k) ^ 2 * (s) ^ 2 * (y) ^ 3))) * hc + (((4 * x * y) + (-4 * s * x * y) + (-4 * x * y * (h) ^ 2) + (-4 * x * y * (k) ^ 2) + (-4 * x * y * (s) ^ 2) + (-2 * c * s * y) + (-2 * c * y * (h) ^ 2) + (-2 * c * y * (k) ^ 2) + (-2 * c * y * (s) ^ 2) + (2 * c * y * (h) ^ 2 * (s) ^ 2) + (2 * c * y * (k) ^ 2 * (s) ^ 2) + (4 * x * y * (h) ^ 2 * (s) ^ 2) + (4 * x * y * (k) ^ 2 * (s) ^ 2))) * hx + (((-4 * x * y) + (-2 * c * y) + (8 * y * (x) ^ 3) + (-8 * y * (s) ^ 2 * (x) ^ 3) + (2 * c * y * (s) ^ 2) + (2 * x * y * (c) ^ 2) + (4 * x * y * (s) ^ 2) + (8 * c * y * (x) ^ 2) + (-8 * c * y * (s) ^ 2 * (x) ^ 2) + (-2 * x * y * (c) ^ 2 * (s) ^ 2))) * hb

theorem rotatedC_pole_iff (s r c j x y h k : ℝ)
    (hr : r^2+s^2=1) (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hb : k^2+h^2=1) :
    IsUnit ((1 + rotatedC s r c j x y h k).det) ↔ rotF s c x y ≠ 0 := by
  have hz : (x : ℂ) + Complex.I * (y : ℂ) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp at hre him
    nlinarith
  rw [rotatedC_det s r c j x y h k hr hc hx hb, isUnit_iff_ne_zero]
  constructor
  · intro hn hf
    apply hn
    simp [hf]
  · intro hf
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hz))
      (Complex.ofReal_ne_zero.mpr hf)

theorem cayleyPreimage_rotatedC (s r c j x y h k : ℝ)
    (hr : r^2+s^2=1) (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hb : k^2+h^2=1)
    (hf : rotF s c x y ≠ 0) :
    cayleyPreimage (rotatedC s r c j x y h k) =
      ((rotF s c x y : ℂ)⁻¹) • recoveryNumerator s r c j x y h k := by
  have hp := (rotatedC_pole_iff s r c j x y h k hr hc hx hb).mpr hf
  have hn := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ =>
    A * (1 + rotatedC s r c j x y h k)⁻¹)
      (recoveryNumerator_equation s r c j x y h k hr hc hx hb)
  simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_nonsing_inv _ hp,
    Matrix.mul_one] at hn
  rw [hn, smul_smul]
  unfold cayleyPreimage cayleyOperator cayleyResponse
  congr 1
  have hf' := Complex.ofReal_ne_zero.mpr hf
  field_simp [hf']
  ring

end GSTC.Scattering.RotatedRankOneRecovery
