/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.RotatedRankOneResources
public import GSTC.Scattering.BIFrontierCompletion

public section
set_option autoImplicit false

namespace GSTC.Scattering.RotatedRankOneRecovery
open scoped Matrix
open Matrix BIInverse RotatedRankOneResources

@[expose] noncomputable def rotatedC (s r c j x y h k : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let z : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
  let b : ℂ := (h : ℂ) + Complex.I * (k : ℂ)
  let bc : ℂ := (h : ℂ) - Complex.I * (k : ℂ)
  !![z*c*s, -z*j, -r*z^2*bc*c^2, -r*z^2*bc*c*j;
     z*j*s, z*c, -r*z^2*bc*c*j, -r*z^2*bc*j^2;
     r*b, 0, z*c*s, z*j*s;
     0, 0, -z*j, z*c]

@[expose] noncomputable def recoveryNumerator (s r c j x y h k : ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let l := k*x-h*y
  let m := h*x+k*y
  locusMatrix (4*y*(c+x)) (4*y*(c*s+x))
    ((2*j*y*(1-s) : ℝ) + Complex.I * (2*j*(c+x)*(1+s) : ℝ))
    ((2*r*(-j^2*k+2*(c+x)*l) : ℝ) + Complex.I*(2*r*(-j^2*h+2*(c+x)*m) : ℝ))
    ((2*j*r*(c*k+l) : ℝ) + Complex.I*(2*j*r*(c*h+m) : ℝ))
    ((2*r*j^2*k : ℝ) + Complex.I*(2*r*j^2*h : ℝ))

theorem recoveryNumerator_equation (s r c j x y h k : ℝ)
    (hr : r^2+s^2=1) (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hb : k^2+h^2=1) :
    recoveryNumerator s r c j x y h k * (1 + rotatedC s r c j x y h k) =
      (2 * Complex.I * (rotF s c x y : ℂ)) • (1 - rotatedC s r c j x y h k) := by
  ext i j'
  fin_cases i <;> fin_cases j'
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-4 * c * y * (h) ^ 2) + (-4 * c * y * (k) ^ 2) + (-4 * x * y * (h) ^ 2) + (-4 * x * y * (k) ^ 2))) * hr + (((-4 * x * y * (s) ^ 2) + (-2 * c * s * y) + (-2 * c * y * (s) ^ 2))) * hc + (((-2 * c * y * (s) ^ 2) + (2 * c * s * y))) * hx + (((-4 * c * y) + (-4 * x * y) + (4 * c * y * (s) ^ 2) + (4 * x * y * (s) ^ 2))) * hb
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * (h) ^ 2 * (j) ^ 2) + (-2 * (j) ^ 2 * (k) ^ 2) + (4 * (h) ^ 2 * (x) ^ 2) + (4 * (k) ^ 2 * (x) ^ 2) + (4 * c * x * (h) ^ 2) + (4 * c * x * (k) ^ 2))) * hr + (((-2 * (h) ^ 2) + (-2 * (k) ^ 2) + (-2 * (s) ^ 2 * (y) ^ 2) + (2 * s * (x) ^ 2) + (2 * s * (y) ^ 2) + (2 * (h) ^ 2 * (s) ^ 2) + (2 * (k) ^ 2 * (s) ^ 2) + (2 * (s) ^ 2 * (x) ^ 2) + (2 * c * s * x) + (2 * c * x * (s) ^ 2))) * hc + ((2 + (-2 * (s) ^ 2) + (2 * s * (c) ^ 2) + (2 * (c) ^ 2 * (s) ^ 2) + (2 * c * s * x) + (2 * c * x * (s) ^ 2))) * hx + ((-2 + (2 * (c) ^ 2) + (2 * (s) ^ 2) + (4 * (x) ^ 2) + (-4 * (s) ^ 2 * (x) ^ 2) + (-2 * (c) ^ 2 * (s) ^ 2) + (4 * c * x) + (-4 * c * x * (s) ^ 2))) * hb
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * j * y) + (2 * j * s * y))) * hx
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * c * j) + (-2 * j * x) + (-2 * c * j * s) + (-2 * j * s * x))) * hx
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * k * r) + (-2 * k * r * (x) ^ 2) + (2 * k * r * (y) ^ 2) + (-2 * c * k * r * x) + (-2 * c * k * r * (x) ^ 3) + (-2 * k * r * (c) ^ 2 * (x) ^ 2) + (2 * c * h * r * y) + (2 * c * h * r * (y) ^ 3) + (2 * k * r * (c) ^ 2 * (y) ^ 2) + (4 * h * r * x * y) + (-2 * c * h * r * s * (y) ^ 3) + (-2 * c * k * r * s * x) + (-2 * c * k * r * s * (x) ^ 3) + (-2 * c * k * r * x * (y) ^ 2) + (-2 * k * r * s * (c) ^ 2 * (x) ^ 2) + (2 * c * h * r * s * y) + (2 * c * h * r * y * (x) ^ 2) + (2 * k * r * s * (c) ^ 2 * (y) ^ 2) + (4 * h * r * x * y * (c) ^ 2) + (4 * h * r * s * x * y * (c) ^ 2) + (6 * c * h * r * s * y * (x) ^ 2) + (6 * c * k * r * s * x * (y) ^ 2))) * hc + (((2 * k * r) + (-2 * k * r * (c) ^ 2) + (-2 * c * k * r * x) + (-2 * k * r * x * (c) ^ 3) + (-2 * k * r * (c) ^ 2 * (x) ^ 2) + (-2 * k * r * (c) ^ 2 * (y) ^ 2) + (2 * c * h * r * y) + (2 * h * r * y * (c) ^ 3) + (-2 * c * h * r * s * y) + (-2 * k * r * s * x * (c) ^ 3) + (-2 * k * r * s * (c) ^ 2 * (x) ^ 2) + (2 * c * k * r * s * x) + (2 * h * r * s * y * (c) ^ 3) + (2 * k * r * s * (c) ^ 2 * (y) ^ 2) + (4 * h * r * s * x * y * (c) ^ 2))) * hx
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * h * r) + (-2 * h * r * (x) ^ 2) + (2 * h * r * (y) ^ 2) + (-4 * k * r * x * y) + (-2 * c * h * r * x) + (-2 * c * h * r * (x) ^ 3) + (-2 * c * k * r * y) + (-2 * c * k * r * (y) ^ 3) + (-2 * h * r * (c) ^ 2 * (x) ^ 2) + (2 * h * r * (c) ^ 2 * (y) ^ 2) + (-4 * k * r * x * y * (c) ^ 2) + (-2 * c * h * r * s * x) + (-2 * c * h * r * s * (x) ^ 3) + (-2 * c * h * r * x * (y) ^ 2) + (-2 * c * k * r * s * y) + (-2 * c * k * r * y * (x) ^ 2) + (-2 * h * r * s * (c) ^ 2 * (x) ^ 2) + (2 * c * k * r * s * (y) ^ 3) + (2 * h * r * s * (c) ^ 2 * (y) ^ 2) + (-6 * c * k * r * s * y * (x) ^ 2) + (-4 * k * r * s * x * y * (c) ^ 2) + (6 * c * h * r * s * x * (y) ^ 2))) * hc + (((2 * h * r) + (-2 * h * r * (c) ^ 2) + (-2 * c * h * r * x) + (-2 * c * k * r * y) + (-2 * h * r * x * (c) ^ 3) + (-2 * h * r * (c) ^ 2 * (x) ^ 2) + (-2 * h * r * (c) ^ 2 * (y) ^ 2) + (-2 * k * r * y * (c) ^ 3) + (-2 * h * r * s * x * (c) ^ 3) + (-2 * h * r * s * (c) ^ 2 * (x) ^ 2) + (-2 * k * r * s * y * (c) ^ 3) + (2 * c * h * r * s * x) + (2 * c * k * r * s * y) + (2 * h * r * s * (c) ^ 2 * (y) ^ 2) + (-4 * k * r * s * x * y * (c) ^ 2))) * hx
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * j * k * r * (x) ^ 3) + (2 * h * j * r * (y) ^ 3) + (-2 * c * j * k * r * (x) ^ 2) + (-2 * h * j * r * s * (y) ^ 3) + (-2 * j * k * r * s * x) + (-2 * j * k * r * s * (x) ^ 3) + (-2 * j * k * r * x * (y) ^ 2) + (2 * c * j * k * r * (y) ^ 2) + (2 * h * j * r * s * y) + (2 * h * j * r * y * (x) ^ 2) + (-2 * c * j * k * r * s * (x) ^ 2) + (2 * c * j * k * r * s * (y) ^ 2) + (4 * c * h * j * r * x * y) + (6 * h * j * r * s * y * (x) ^ 2) + (6 * j * k * r * s * x * (y) ^ 2) + (4 * c * h * j * r * s * x * y))) * hc + (((-2 * c * j * k * r) + (-2 * j * k * r * x) + (2 * h * j * r * y) + (-2 * c * j * k * r * (x) ^ 2) + (-2 * c * j * k * r * (y) ^ 2) + (-2 * h * j * r * s * y) + (-2 * j * k * r * x * (c) ^ 2) + (2 * h * j * r * y * (c) ^ 2) + (2 * j * k * r * s * x) + (-2 * c * j * k * r * s * (x) ^ 2) + (-2 * j * k * r * s * x * (c) ^ 2) + (2 * c * j * k * r * s * (y) ^ 2) + (2 * h * j * r * s * y * (c) ^ 2) + (4 * c * h * j * r * s * x * y))) * hx
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * h * j * r * (x) ^ 3) + (-2 * j * k * r * (y) ^ 3) + (-2 * c * h * j * r * (x) ^ 2) + (-2 * h * j * r * s * x) + (-2 * h * j * r * s * (x) ^ 3) + (-2 * h * j * r * x * (y) ^ 2) + (-2 * j * k * r * s * y) + (-2 * j * k * r * y * (x) ^ 2) + (2 * c * h * j * r * (y) ^ 2) + (2 * j * k * r * s * (y) ^ 3) + (-6 * j * k * r * s * y * (x) ^ 2) + (-4 * c * j * k * r * x * y) + (-2 * c * h * j * r * s * (x) ^ 2) + (2 * c * h * j * r * s * (y) ^ 2) + (6 * h * j * r * s * x * (y) ^ 2) + (-4 * c * j * k * r * s * x * y))) * hc + (((-2 * c * h * j * r) + (-2 * h * j * r * x) + (-2 * j * k * r * y) + (-2 * c * h * j * r * (x) ^ 2) + (-2 * c * h * j * r * (y) ^ 2) + (-2 * h * j * r * x * (c) ^ 2) + (-2 * j * k * r * y * (c) ^ 2) + (2 * h * j * r * s * x) + (2 * j * k * r * s * y) + (-2 * c * h * j * r * s * (x) ^ 2) + (-2 * h * j * r * s * x * (c) ^ 2) + (-2 * j * k * r * s * y * (c) ^ 2) + (2 * c * h * j * r * s * (y) ^ 2) + (-4 * c * j * k * r * s * x * y))) * hx
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * j * y * (h) ^ 2) + (-2 * j * y * (k) ^ 2))) * hr + (((-2 * j * y * (s) ^ 2) + (2 * j * s * y))) * hx + (((-2 * j * y) + (2 * j * y * (s) ^ 2))) * hb
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((2 * c * j * (h) ^ 2) + (2 * c * j * (k) ^ 2) + (2 * j * x * (h) ^ 2) + (2 * j * x * (k) ^ 2))) * hr + (((2 * c * j * s) + (2 * c * j * (s) ^ 2) + (2 * j * s * x) + (2 * j * x * (s) ^ 2))) * hx + (((2 * c * j) + (2 * j * x) + (-2 * c * j * (s) ^ 2) + (-2 * j * x * (s) ^ 2))) * hb
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-4 * x * y) + (-2 * c * y) + (-2 * c * s * y))) * hc + (((2 * c * y) + (-2 * c * s * y))) * hx
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * (y) ^ 2) + (2 * (x) ^ 2) + (2 * c * x) + (2 * s * (x) ^ 2) + (2 * s * (y) ^ 2) + (2 * c * s * x))) * hc + (((2 * (c) ^ 2) + (2 * c * x) + (2 * s * (c) ^ 2) + (2 * c * s * x))) * hx
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * j * k * r * x) + (2 * h * j * r * y))) * hc + (((-2 * c * j * k * r) + (-2 * c * j * k * r * (x) ^ 2) + (-2 * c * j * k * r * (y) ^ 2) + (-2 * j * k * r * x * (c) ^ 2) + (2 * h * j * r * y * (c) ^ 2) + (-2 * c * j * k * r * s * (x) ^ 2) + (-2 * j * k * r * s * x * (c) ^ 2) + (2 * c * j * k * r * s * (y) ^ 2) + (2 * h * j * r * s * y * (c) ^ 2) + (4 * c * h * j * r * s * x * y))) * hx
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * h * j * r * x) + (-2 * j * k * r * y))) * hc + (((-2 * c * h * j * r) + (-2 * c * h * j * r * (x) ^ 2) + (-2 * c * h * j * r * (y) ^ 2) + (-2 * h * j * r * x * (c) ^ 2) + (-2 * j * k * r * y * (c) ^ 2) + (-2 * c * h * j * r * s * (x) ^ 2) + (-2 * h * j * r * s * x * (c) ^ 2) + (-2 * j * k * r * s * y * (c) ^ 2) + (2 * c * h * j * r * s * (y) ^ 2) + (-4 * c * j * k * r * s * x * y))) * hx
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((2 * k * r) + (-2 * k * r * (x) ^ 4) + (-2 * k * r * (y) ^ 4) + (-4 * k * r * (x) ^ 2 * (y) ^ 2) + (-2 * c * h * r * y) + (-2 * c * k * r * (x) ^ 3) + (-2 * k * r * s * (x) ^ 4) + (-2 * k * r * s * (y) ^ 2) + (2 * c * h * r * (y) ^ 3) + (2 * c * k * r * x) + (2 * k * r * s * (x) ^ 2) + (2 * k * r * s * (y) ^ 4) + (-4 * h * r * s * x * y) + (-2 * c * h * r * s * y) + (-2 * c * k * r * s * (x) ^ 3) + (-2 * c * k * r * x * (y) ^ 2) + (2 * c * h * r * s * (y) ^ 3) + (2 * c * h * r * y * (x) ^ 2) + (2 * c * k * r * s * x) + (4 * h * r * s * x * (y) ^ 3) + (4 * h * r * s * y * (x) ^ 3) + (-2 * c * k * r * s * x * (y) ^ 2) + (2 * c * h * r * s * y * (x) ^ 2))) * hc + (((-2 * k * r) + (-2 * k * r * (x) ^ 2) + (-2 * k * r * (y) ^ 2) + (2 * k * r * (c) ^ 2) + (-2 * c * k * r * x) + (-2 * h * r * y * (c) ^ 3) + (-2 * k * r * s * (x) ^ 2) + (2 * c * h * r * y) + (2 * k * r * s * (y) ^ 2) + (2 * k * r * x * (c) ^ 3) + (2 * k * r * (c) ^ 2 * (x) ^ 2) + (2 * k * r * (c) ^ 2 * (y) ^ 2) + (-2 * c * k * r * s * x) + (-2 * h * r * s * y * (c) ^ 3) + (-2 * k * r * s * (c) ^ 2 * (y) ^ 2) + (2 * c * h * r * s * y) + (2 * k * r * s * x * (c) ^ 3) + (2 * k * r * s * (c) ^ 2 * (x) ^ 2) + (4 * h * r * s * x * y) + (-4 * h * r * s * x * y * (c) ^ 2))) * hx
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((2 * h * r) + (-2 * h * r * (x) ^ 4) + (-2 * h * r * (y) ^ 4) + (-4 * h * r * (x) ^ 2 * (y) ^ 2) + (-2 * c * h * r * (x) ^ 3) + (-2 * c * k * r * (y) ^ 3) + (-2 * h * r * s * (x) ^ 4) + (-2 * h * r * s * (y) ^ 2) + (2 * c * h * r * x) + (2 * c * k * r * y) + (2 * h * r * s * (x) ^ 2) + (2 * h * r * s * (y) ^ 4) + (-4 * k * r * s * x * (y) ^ 3) + (-4 * k * r * s * y * (x) ^ 3) + (-2 * c * h * r * s * (x) ^ 3) + (-2 * c * h * r * x * (y) ^ 2) + (-2 * c * k * r * s * (y) ^ 3) + (-2 * c * k * r * y * (x) ^ 2) + (2 * c * h * r * s * x) + (2 * c * k * r * s * y) + (4 * k * r * s * x * y) + (-2 * c * h * r * s * x * (y) ^ 2) + (-2 * c * k * r * s * y * (x) ^ 2))) * hc + (((-2 * h * r) + (-2 * h * r * (x) ^ 2) + (-2 * h * r * (y) ^ 2) + (2 * h * r * (c) ^ 2) + (-2 * c * h * r * x) + (-2 * c * k * r * y) + (-2 * h * r * s * (x) ^ 2) + (2 * h * r * s * (y) ^ 2) + (2 * h * r * x * (c) ^ 3) + (2 * h * r * (c) ^ 2 * (x) ^ 2) + (2 * h * r * (c) ^ 2 * (y) ^ 2) + (2 * k * r * y * (c) ^ 3) + (-4 * k * r * s * x * y) + (-2 * c * h * r * s * x) + (-2 * c * k * r * s * y) + (-2 * h * r * s * (c) ^ 2 * (y) ^ 2) + (2 * h * r * s * x * (c) ^ 3) + (2 * h * r * s * (c) ^ 2 * (x) ^ 2) + (2 * k * r * s * y * (c) ^ 3) + (4 * k * r * s * x * y * (c) ^ 2))) * hx
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * k * r) + (2 * k * r * s * (x) ^ 2) + (2 * k * r * s * (y) ^ 2))) * hc + (((2 * k * r) + (2 * k * r * s * (c) ^ 2) + (4 * c * k * r * s * x))) * hx
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((2 * h * r) + (-2 * h * r * s * (x) ^ 2) + (-2 * h * r * s * (y) ^ 2))) * hc + (((-2 * h * r) + (-2 * h * r * s * (c) ^ 2) + (-4 * c * h * r * s * x))) * hx
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((2 * h * j * r * y) + (2 * j * k * r * x))) * hc + (((-4 * j * k * r * x) + (-2 * c * j * k * r))) * hx
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * h * j * r * x) + (2 * j * k * r * y))) * hc + (((2 * c * h * j * r) + (4 * h * j * r * x))) * hx
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-4 * (c) ^ 3 * (h) ^ 2 * (y) ^ 3) + (-4 * (c) ^ 3 * (k) ^ 2 * (y) ^ 3) + (-4 * x * (c) ^ 2 * (h) ^ 2 * (y) ^ 3) + (-4 * x * (c) ^ 2 * (k) ^ 2 * (y) ^ 3) + (-4 * y * (c) ^ 2 * (h) ^ 2 * (x) ^ 3) + (-4 * y * (c) ^ 2 * (k) ^ 2 * (x) ^ 3) + (-4 * y * (c) ^ 3 * (h) ^ 2 * (x) ^ 2) + (-4 * y * (c) ^ 3 * (k) ^ 2 * (x) ^ 2) + (-2 * c * (h) ^ 2 * (j) ^ 2 * (y) ^ 3) + (-2 * c * (j) ^ 2 * (k) ^ 2 * (y) ^ 3) + (-2 * c * y * (h) ^ 2 * (j) ^ 2 * (x) ^ 2) + (-2 * c * y * (j) ^ 2 * (k) ^ 2 * (x) ^ 2))) * hr + (((-4 * x * y) + (-2 * c * y) + (-2 * c * s * y) + (-2 * c * (h) ^ 2 * (y) ^ 3) + (-2 * c * (k) ^ 2 * (y) ^ 3) + (-2 * c * y * (h) ^ 2 * (x) ^ 2) + (-2 * c * y * (k) ^ 2 * (x) ^ 2) + (2 * c * (h) ^ 2 * (s) ^ 2 * (y) ^ 3) + (2 * c * (k) ^ 2 * (s) ^ 2 * (y) ^ 3) + (2 * c * y * (h) ^ 2 * (s) ^ 2 * (x) ^ 2) + (2 * c * y * (k) ^ 2 * (s) ^ 2 * (x) ^ 2))) * hc + (((-2 * c * y * (h) ^ 2) + (-2 * c * y * (k) ^ 2) + (-2 * c * y * (s) ^ 2) + (-2 * y * (c) ^ 3 * (h) ^ 2) + (-2 * y * (c) ^ 3 * (k) ^ 2) + (2 * c * s * y) + (-4 * x * y * (c) ^ 2 * (h) ^ 2) + (-4 * x * y * (c) ^ 2 * (k) ^ 2) + (2 * c * y * (h) ^ 2 * (s) ^ 2) + (2 * c * y * (k) ^ 2 * (s) ^ 2) + (2 * y * (c) ^ 3 * (h) ^ 2 * (s) ^ 2) + (2 * y * (c) ^ 3 * (k) ^ 2 * (s) ^ 2) + (4 * x * y * (c) ^ 2 * (h) ^ 2 * (s) ^ 2) + (4 * x * y * (c) ^ 2 * (k) ^ 2 * (s) ^ 2))) * hx + (((-2 * c * y) + (-2 * y * (c) ^ 3) + (-4 * x * y * (c) ^ 2) + (2 * c * y * (s) ^ 2) + (2 * y * (c) ^ 3 * (s) ^ 2) + (4 * x * y * (c) ^ 2 * (s) ^ 2))) * hb
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((4 * (c) ^ 2 * (h) ^ 2 * (x) ^ 4) + (4 * (c) ^ 2 * (k) ^ 2 * (x) ^ 4) + (4 * (c) ^ 3 * (h) ^ 2 * (x) ^ 3) + (4 * (c) ^ 3 * (k) ^ 2 * (x) ^ 3) + (2 * c * (h) ^ 2 * (j) ^ 2 * (x) ^ 3) + (2 * c * (j) ^ 2 * (k) ^ 2 * (x) ^ 3) + (4 * x * (c) ^ 3 * (h) ^ 2 * (y) ^ 2) + (4 * x * (c) ^ 3 * (k) ^ 2 * (y) ^ 2) + (4 * (c) ^ 2 * (h) ^ 2 * (x) ^ 2 * (y) ^ 2) + (4 * (c) ^ 2 * (k) ^ 2 * (x) ^ 2 * (y) ^ 2) + (2 * c * x * (h) ^ 2 * (j) ^ 2 * (y) ^ 2) + (2 * c * x * (j) ^ 2 * (k) ^ 2 * (y) ^ 2))) * hr + (((-2 * (y) ^ 2) + (2 * (x) ^ 2) + (2 * c * x) + (2 * s * (x) ^ 2) + (2 * s * (y) ^ 2) + (2 * c * s * x) + (2 * c * (h) ^ 2 * (x) ^ 3) + (2 * c * (k) ^ 2 * (x) ^ 3) + (-2 * c * (h) ^ 2 * (s) ^ 2 * (x) ^ 3) + (-2 * c * (k) ^ 2 * (s) ^ 2 * (x) ^ 3) + (2 * c * x * (h) ^ 2 * (y) ^ 2) + (2 * c * x * (k) ^ 2 * (y) ^ 2) + (-2 * c * x * (h) ^ 2 * (s) ^ 2 * (y) ^ 2) + (-2 * c * x * (k) ^ 2 * (s) ^ 2 * (y) ^ 2))) * hc + (((2 * (c) ^ 2) + (2 * s * (c) ^ 2) + (2 * c * s * x) + (2 * c * x * (h) ^ 2) + (2 * c * x * (k) ^ 2) + (2 * c * x * (s) ^ 2) + (2 * x * (c) ^ 3 * (h) ^ 2) + (2 * x * (c) ^ 3 * (k) ^ 2) + (4 * (c) ^ 2 * (h) ^ 2 * (x) ^ 2) + (4 * (c) ^ 2 * (k) ^ 2 * (x) ^ 2) + (-4 * (c) ^ 2 * (h) ^ 2 * (s) ^ 2 * (x) ^ 2) + (-4 * (c) ^ 2 * (k) ^ 2 * (s) ^ 2 * (x) ^ 2) + (-2 * c * x * (h) ^ 2 * (s) ^ 2) + (-2 * c * x * (k) ^ 2 * (s) ^ 2) + (-2 * x * (c) ^ 3 * (h) ^ 2 * (s) ^ 2) + (-2 * x * (c) ^ 3 * (k) ^ 2 * (s) ^ 2))) * hx + (((2 * c * x) + (2 * x * (c) ^ 3) + (4 * (c) ^ 2 * (x) ^ 2) + (-4 * (c) ^ 2 * (s) ^ 2 * (x) ^ 2) + (-2 * c * x * (s) ^ 2) + (-2 * x * (c) ^ 3 * (s) ^ 2))) * hb
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * (h) ^ 2 * (j) ^ 3 * (y) ^ 3) + (-2 * (j) ^ 3 * (k) ^ 2 * (y) ^ 3) + (-4 * j * (c) ^ 2 * (h) ^ 2 * (y) ^ 3) + (-4 * j * (c) ^ 2 * (k) ^ 2 * (y) ^ 3) + (-2 * y * (h) ^ 2 * (j) ^ 3 * (x) ^ 2) + (-2 * y * (j) ^ 3 * (k) ^ 2 * (x) ^ 2) + (-4 * c * j * x * (h) ^ 2 * (y) ^ 3) + (-4 * c * j * x * (k) ^ 2 * (y) ^ 3) + (-4 * c * j * y * (h) ^ 2 * (x) ^ 3) + (-4 * c * j * y * (k) ^ 2 * (x) ^ 3) + (-4 * j * y * (c) ^ 2 * (h) ^ 2 * (x) ^ 2) + (-4 * j * y * (c) ^ 2 * (k) ^ 2 * (x) ^ 2))) * hr + (((-2 * j * (h) ^ 2 * (y) ^ 3) + (-2 * j * (k) ^ 2 * (y) ^ 3) + (-2 * j * y * (h) ^ 2 * (x) ^ 2) + (-2 * j * y * (k) ^ 2 * (x) ^ 2) + (2 * j * (h) ^ 2 * (s) ^ 2 * (y) ^ 3) + (2 * j * (k) ^ 2 * (s) ^ 2 * (y) ^ 3) + (2 * j * y * (h) ^ 2 * (s) ^ 2 * (x) ^ 2) + (2 * j * y * (k) ^ 2 * (s) ^ 2 * (x) ^ 2))) * hc + (((-2 * j * y * (h) ^ 2) + (-2 * j * y * (k) ^ 2) + (-2 * j * y * (s) ^ 2) + (2 * j * s * y) + (-2 * j * y * (c) ^ 2 * (h) ^ 2) + (-2 * j * y * (c) ^ 2 * (k) ^ 2) + (2 * j * y * (h) ^ 2 * (s) ^ 2) + (2 * j * y * (k) ^ 2 * (s) ^ 2) + (-4 * c * j * x * y * (h) ^ 2) + (-4 * c * j * x * y * (k) ^ 2) + (2 * j * y * (c) ^ 2 * (h) ^ 2 * (s) ^ 2) + (2 * j * y * (c) ^ 2 * (k) ^ 2 * (s) ^ 2) + (4 * c * j * x * y * (h) ^ 2 * (s) ^ 2) + (4 * c * j * x * y * (k) ^ 2 * (s) ^ 2))) * hx + (((-2 * j * y) + (-2 * j * y * (c) ^ 2) + (2 * j * y * (s) ^ 2) + (-4 * c * j * x * y) + (2 * j * y * (c) ^ 2 * (s) ^ 2) + (4 * c * j * x * y * (s) ^ 2))) * hb
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((2 * (h) ^ 2 * (j) ^ 3 * (x) ^ 3) + (2 * (j) ^ 3 * (k) ^ 2 * (x) ^ 3) + (2 * x * (h) ^ 2 * (j) ^ 3 * (y) ^ 2) + (2 * x * (j) ^ 3 * (k) ^ 2 * (y) ^ 2) + (4 * c * j * (h) ^ 2 * (x) ^ 4) + (4 * c * j * (k) ^ 2 * (x) ^ 4) + (4 * j * (c) ^ 2 * (h) ^ 2 * (x) ^ 3) + (4 * j * (c) ^ 2 * (k) ^ 2 * (x) ^ 3) + (4 * c * j * (h) ^ 2 * (x) ^ 2 * (y) ^ 2) + (4 * c * j * (k) ^ 2 * (x) ^ 2 * (y) ^ 2) + (4 * j * x * (c) ^ 2 * (h) ^ 2 * (y) ^ 2) + (4 * j * x * (c) ^ 2 * (k) ^ 2 * (y) ^ 2))) * hr + (((2 * j * (h) ^ 2 * (x) ^ 3) + (2 * j * (k) ^ 2 * (x) ^ 3) + (-2 * j * (h) ^ 2 * (s) ^ 2 * (x) ^ 3) + (-2 * j * (k) ^ 2 * (s) ^ 2 * (x) ^ 3) + (2 * j * x * (h) ^ 2 * (y) ^ 2) + (2 * j * x * (k) ^ 2 * (y) ^ 2) + (-2 * j * x * (h) ^ 2 * (s) ^ 2 * (y) ^ 2) + (-2 * j * x * (k) ^ 2 * (s) ^ 2 * (y) ^ 2))) * hc + (((2 * c * j) + (2 * c * j * s) + (2 * j * s * x) + (2 * j * x * (h) ^ 2) + (2 * j * x * (k) ^ 2) + (2 * j * x * (s) ^ 2) + (-2 * j * x * (h) ^ 2 * (s) ^ 2) + (-2 * j * x * (k) ^ 2 * (s) ^ 2) + (2 * j * x * (c) ^ 2 * (h) ^ 2) + (2 * j * x * (c) ^ 2 * (k) ^ 2) + (4 * c * j * (h) ^ 2 * (x) ^ 2) + (4 * c * j * (k) ^ 2 * (x) ^ 2) + (-4 * c * j * (h) ^ 2 * (s) ^ 2 * (x) ^ 2) + (-4 * c * j * (k) ^ 2 * (s) ^ 2 * (x) ^ 2) + (-2 * j * x * (c) ^ 2 * (h) ^ 2 * (s) ^ 2) + (-2 * j * x * (c) ^ 2 * (k) ^ 2 * (s) ^ 2))) * hx + (((2 * j * x) + (-2 * j * x * (s) ^ 2) + (2 * j * x * (c) ^ 2) + (4 * c * j * (x) ^ 2) + (-4 * c * j * (s) ^ 2 * (x) ^ 2) + (-2 * j * x * (c) ^ 2 * (s) ^ 2))) * hb
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((2 * h * j * r * s * y) + (2 * j * k * r * s * x))) * hc + ((2 * c * j * k * r * s)) * hx
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * h * j * r * s * x) + (2 * j * k * r * s * y))) * hc + ((-2 * c * h * j * r * s)) * hx
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((2 * k * r) + (-2 * k * r * (x) ^ 2) + (-2 * k * r * (y) ^ 2))) * hc + (((-2 * k * r) + (2 * k * r * (c) ^ 2))) * hx
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * h * r) + (2 * h * r * (x) ^ 2) + (2 * h * r * (y) ^ 2))) * hc + (((2 * h * r) + (-2 * h * r * (c) ^ 2))) * hx
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * j * (c) ^ 2 * (h) ^ 2 * (y) ^ 3) + (-2 * j * (c) ^ 2 * (k) ^ 2 * (y) ^ 3) + (-4 * c * x * y * (h) ^ 2 * (j) ^ 3) + (-4 * c * x * y * (j) ^ 3 * (k) ^ 2) + (-4 * j * x * y * (c) ^ 3 * (h) ^ 2) + (-4 * j * x * y * (c) ^ 3 * (k) ^ 2) + (-2 * j * y * (c) ^ 2 * (h) ^ 2 * (x) ^ 2) + (-2 * j * y * (c) ^ 2 * (k) ^ 2 * (x) ^ 2))) * hr + (((-4 * c * j * x * y * (h) ^ 2) + (-4 * c * j * x * y * (k) ^ 2) + (4 * c * j * x * y * (h) ^ 2 * (s) ^ 2) + (4 * c * j * x * y * (k) ^ 2 * (s) ^ 2))) * hc + (((-2 * j * y) + (2 * j * s * y) + (-2 * j * y * (c) ^ 2 * (h) ^ 2) + (-2 * j * y * (c) ^ 2 * (k) ^ 2) + (2 * j * y * (c) ^ 2 * (h) ^ 2 * (s) ^ 2) + (2 * j * y * (c) ^ 2 * (k) ^ 2 * (s) ^ 2))) * hx + (((-2 * j * y * (c) ^ 2) + (-4 * c * j * x * y) + (2 * j * y * (c) ^ 2 * (s) ^ 2) + (4 * c * j * x * y * (s) ^ 2))) * hb
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * c * (h) ^ 2 * (j) ^ 3 * (y) ^ 2) + (-2 * c * (j) ^ 3 * (k) ^ 2 * (y) ^ 2) + (-2 * j * (c) ^ 3 * (h) ^ 2 * (y) ^ 2) + (-2 * j * (c) ^ 3 * (k) ^ 2 * (y) ^ 2) + (2 * c * (h) ^ 2 * (j) ^ 3 * (x) ^ 2) + (2 * c * (j) ^ 3 * (k) ^ 2 * (x) ^ 2) + (2 * j * (c) ^ 2 * (h) ^ 2 * (x) ^ 3) + (2 * j * (c) ^ 2 * (k) ^ 2 * (x) ^ 3) + (2 * j * (c) ^ 3 * (h) ^ 2 * (x) ^ 2) + (2 * j * (c) ^ 3 * (k) ^ 2 * (x) ^ 2) + (2 * j * x * (c) ^ 2 * (h) ^ 2 * (y) ^ 2) + (2 * j * x * (c) ^ 2 * (k) ^ 2 * (y) ^ 2))) * hr + (((-2 * c * j * (h) ^ 2 * (y) ^ 2) + (-2 * c * j * (k) ^ 2 * (y) ^ 2) + (2 * c * j * (h) ^ 2 * (x) ^ 2) + (2 * c * j * (k) ^ 2 * (x) ^ 2) + (-2 * c * j * (h) ^ 2 * (s) ^ 2 * (x) ^ 2) + (-2 * c * j * (k) ^ 2 * (s) ^ 2 * (x) ^ 2) + (2 * c * j * (h) ^ 2 * (s) ^ 2 * (y) ^ 2) + (2 * c * j * (k) ^ 2 * (s) ^ 2 * (y) ^ 2))) * hc + (((-2 * j * x) + (-2 * c * j * s) + (-2 * c * j * (h) ^ 2) + (-2 * c * j * (k) ^ 2) + (-2 * c * j * (s) ^ 2) + (-2 * j * s * x) + (2 * c * j * (h) ^ 2 * (s) ^ 2) + (2 * c * j * (k) ^ 2 * (s) ^ 2) + (2 * j * x * (c) ^ 2 * (h) ^ 2) + (2 * j * x * (c) ^ 2 * (k) ^ 2) + (-2 * j * x * (c) ^ 2 * (h) ^ 2 * (s) ^ 2) + (-2 * j * x * (c) ^ 2 * (k) ^ 2 * (s) ^ 2))) * hx + (((-2 * c * j) + (2 * c * j * (s) ^ 2) + (2 * j * x * (c) ^ 2) + (4 * c * j * (x) ^ 2) + (-4 * c * j * (s) ^ 2 * (x) ^ 2) + (-2 * j * x * (c) ^ 2 * (s) ^ 2))) * hb
  · apply Complex.ext
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-4 * x * y * (h) ^ 2 * (j) ^ 4) + (-4 * x * y * (j) ^ 4 * (k) ^ 2) + (-2 * c * (h) ^ 2 * (j) ^ 2 * (y) ^ 3) + (-2 * c * (j) ^ 2 * (k) ^ 2 * (y) ^ 3) + (-4 * x * y * (c) ^ 2 * (h) ^ 2 * (j) ^ 2) + (-4 * x * y * (c) ^ 2 * (j) ^ 2 * (k) ^ 2) + (-2 * c * y * (h) ^ 2 * (j) ^ 2 * (x) ^ 2) + (-2 * c * y * (j) ^ 2 * (k) ^ 2 * (x) ^ 2))) * hr + (((-4 * x * y * (h) ^ 2) + (-4 * x * y * (k) ^ 2) + (-4 * x * y * (s) ^ 2) + (-2 * c * s * y) + (-2 * c * y * (s) ^ 2) + (-2 * c * (h) ^ 2 * (y) ^ 3) + (-2 * c * (k) ^ 2 * (y) ^ 3) + (-4 * x * y * (h) ^ 2 * (j) ^ 2) + (-4 * x * y * (j) ^ 2 * (k) ^ 2) + (-2 * c * y * (h) ^ 2 * (x) ^ 2) + (-2 * c * y * (k) ^ 2 * (x) ^ 2) + (2 * c * (h) ^ 2 * (s) ^ 2 * (y) ^ 3) + (2 * c * (k) ^ 2 * (s) ^ 2 * (y) ^ 3) + (4 * x * y * (h) ^ 2 * (s) ^ 2) + (4 * x * y * (k) ^ 2 * (s) ^ 2) + (2 * c * y * (h) ^ 2 * (s) ^ 2 * (x) ^ 2) + (2 * c * y * (k) ^ 2 * (s) ^ 2 * (x) ^ 2) + (4 * x * y * (h) ^ 2 * (j) ^ 2 * (s) ^ 2) + (4 * x * y * (j) ^ 2 * (k) ^ 2 * (s) ^ 2))) * hc + (((2 * c * y) + (-2 * c * s * y) + (-2 * c * y * (h) ^ 2) + (-2 * c * y * (k) ^ 2) + (2 * y * (c) ^ 3 * (h) ^ 2) + (2 * y * (c) ^ 3 * (k) ^ 2) + (-2 * y * (c) ^ 3 * (h) ^ 2 * (s) ^ 2) + (-2 * y * (c) ^ 3 * (k) ^ 2 * (s) ^ 2) + (2 * c * y * (h) ^ 2 * (s) ^ 2) + (2 * c * y * (k) ^ 2 * (s) ^ 2))) * hx + (((-4 * x * y) + (-2 * c * y) + (2 * y * (c) ^ 3) + (-2 * y * (c) ^ 3 * (s) ^ 2) + (2 * c * y * (s) ^ 2) + (4 * x * y * (c) ^ 2) + (4 * x * y * (s) ^ 2) + (-4 * x * y * (c) ^ 2 * (s) ^ 2))) * hb
    · simp [recoveryNumerator, rotatedC, locusMatrix, rotF, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.smul_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        pow_two]
      linear_combination (((-2 * (h) ^ 2 * (j) ^ 4 * (y) ^ 2) + (-2 * (j) ^ 4 * (k) ^ 2 * (y) ^ 2) + (2 * (h) ^ 2 * (j) ^ 4 * (x) ^ 2) + (2 * (j) ^ 4 * (k) ^ 2 * (x) ^ 2) + (-2 * (c) ^ 2 * (h) ^ 2 * (j) ^ 2 * (y) ^ 2) + (-2 * (c) ^ 2 * (j) ^ 2 * (k) ^ 2 * (y) ^ 2) + (2 * c * (h) ^ 2 * (j) ^ 2 * (x) ^ 3) + (2 * c * (j) ^ 2 * (k) ^ 2 * (x) ^ 3) + (2 * (c) ^ 2 * (h) ^ 2 * (j) ^ 2 * (x) ^ 2) + (2 * (c) ^ 2 * (j) ^ 2 * (k) ^ 2 * (x) ^ 2) + (2 * c * x * (h) ^ 2 * (j) ^ 2 * (y) ^ 2) + (2 * c * x * (j) ^ 2 * (k) ^ 2 * (y) ^ 2))) * hr + (((-2 * (h) ^ 2 * (y) ^ 2) + (-2 * (k) ^ 2 * (y) ^ 2) + (-2 * (s) ^ 2 * (y) ^ 2) + (2 * s * (x) ^ 2) + (2 * s * (y) ^ 2) + (2 * (h) ^ 2 * (x) ^ 2) + (2 * (k) ^ 2 * (x) ^ 2) + (2 * (s) ^ 2 * (x) ^ 2) + (-2 * (h) ^ 2 * (j) ^ 2 * (y) ^ 2) + (-2 * (h) ^ 2 * (s) ^ 2 * (x) ^ 2) + (-2 * (j) ^ 2 * (k) ^ 2 * (y) ^ 2) + (-2 * (k) ^ 2 * (s) ^ 2 * (x) ^ 2) + (2 * c * s * x) + (2 * c * x * (s) ^ 2) + (2 * c * (h) ^ 2 * (x) ^ 3) + (2 * c * (k) ^ 2 * (x) ^ 3) + (2 * (h) ^ 2 * (j) ^ 2 * (x) ^ 2) + (2 * (h) ^ 2 * (s) ^ 2 * (y) ^ 2) + (2 * (j) ^ 2 * (k) ^ 2 * (x) ^ 2) + (2 * (k) ^ 2 * (s) ^ 2 * (y) ^ 2) + (-2 * c * (h) ^ 2 * (s) ^ 2 * (x) ^ 3) + (-2 * c * (k) ^ 2 * (s) ^ 2 * (x) ^ 3) + (-2 * (h) ^ 2 * (j) ^ 2 * (s) ^ 2 * (x) ^ 2) + (-2 * (j) ^ 2 * (k) ^ 2 * (s) ^ 2 * (x) ^ 2) + (2 * c * x * (h) ^ 2 * (y) ^ 2) + (2 * c * x * (k) ^ 2 * (y) ^ 2) + (2 * (h) ^ 2 * (j) ^ 2 * (s) ^ 2 * (y) ^ 2) + (2 * (j) ^ 2 * (k) ^ 2 * (s) ^ 2 * (y) ^ 2) + (-2 * c * x * (h) ^ 2 * (s) ^ 2 * (y) ^ 2) + (-2 * c * x * (k) ^ 2 * (s) ^ 2 * (y) ^ 2))) * hc + ((2 + (-2 * (h) ^ 2) + (-2 * (k) ^ 2) + (-2 * (s) ^ 2) + (2 * c * x) + (2 * s * (c) ^ 2) + (2 * (c) ^ 2 * (h) ^ 2) + (2 * (c) ^ 2 * (k) ^ 2) + (2 * (c) ^ 2 * (s) ^ 2) + (2 * (h) ^ 2 * (s) ^ 2) + (2 * (k) ^ 2 * (s) ^ 2) + (-2 * x * (c) ^ 3 * (h) ^ 2) + (-2 * x * (c) ^ 3 * (k) ^ 2) + (-2 * (c) ^ 2 * (h) ^ 2 * (s) ^ 2) + (-2 * (c) ^ 2 * (k) ^ 2 * (s) ^ 2) + (2 * c * s * x) + (2 * c * x * (h) ^ 2) + (2 * c * x * (k) ^ 2) + (-2 * c * x * (h) ^ 2 * (s) ^ 2) + (-2 * c * x * (k) ^ 2 * (s) ^ 2) + (2 * x * (c) ^ 3 * (h) ^ 2 * (s) ^ 2) + (2 * x * (c) ^ 3 * (k) ^ 2 * (s) ^ 2))) * hx + ((-2 + (2 * (c) ^ 2) + (2 * (s) ^ 2) + (4 * (x) ^ 2) + (-4 * (c) ^ 2 * (x) ^ 2) + (-4 * (s) ^ 2 * (x) ^ 2) + (-2 * x * (c) ^ 3) + (-2 * (c) ^ 2 * (s) ^ 2) + (2 * c * x) + (-2 * c * x * (s) ^ 2) + (2 * x * (c) ^ 3 * (s) ^ 2) + (4 * (c) ^ 2 * (s) ^ 2 * (x) ^ 2))) * hb

end GSTC.Scattering.RotatedRankOneRecovery
