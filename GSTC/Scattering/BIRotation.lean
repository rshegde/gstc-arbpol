/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.TransverseRotation

public section
namespace GSTC.Scattering
namespace BIRotation
open Matrix
open scoped Matrix
open TransverseRotation

structure TensorDecomp where

  m : ℝ

  j : ℝ

  x : ℝ

  z : ℝ

@[expose] def tensorOf (d : TensorDecomp) : Ten2 :=
  !![((d.m + d.z : ℝ) : ℂ), ((d.x - d.j : ℝ) : ℂ);
     ((d.x + d.j : ℝ) : ℂ), ((d.m - d.z : ℝ) : ℂ)]

@[expose] noncomputable def decompA (p : BIParams) : TensorDecomp where
  m := (p.ee00 + p.ee11) / 2
  j := 0
  x := p.ee01
  z := (p.ee00 - p.ee11) / 2

@[expose] noncomputable def decompD (p : BIParams) : TensorDecomp where
  m := (p.mm00 + p.mm11) / 2
  j := 0
  x := p.mm01
  z := (p.mm00 - p.mm11) / 2

@[expose] def gBlock (p : BIParams) : Ten2 :=
  !![(p.g00 : ℂ), (p.g01 : ℂ); (p.g10 : ℂ), (p.g11 : ℂ)]

@[expose] noncomputable def decompG (p : BIParams) : TensorDecomp where
  m := (p.g00 + p.g11) / 2
  j := (p.g10 - p.g01) / 2
  x := (p.g01 + p.g10) / 2
  z := (p.g00 - p.g11) / 2

theorem tensorOf_decompA (p : BIParams) : tensorOf (decompA p) = p.eeBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorOf, decompA, BIParams.eeBlock, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;> ring

theorem tensorOf_decompD (p : BIParams) : tensorOf (decompD p) = p.mmBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorOf, decompD, BIParams.mmBlock, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;> ring

theorem tensorOf_decompG (p : BIParams) : tensorOf (decompG p) = gBlock p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorOf, decompG, gBlock, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

theorem tensor_conjugate (d : TensorDecomp) (γ : ℝ) :
    (rotation γ).transpose * tensorOf d * rotation γ =
      tensorOf ⟨d.m, d.j, rotX γ d.x d.z, rotZ γ d.x d.z⟩ := by
  have hcos : Real.cos (2 * γ) = Real.cos γ * Real.cos γ - Real.sin γ * Real.sin γ := by
    rw [show (2 : ℝ) * γ = γ + γ by ring, Real.cos_add]
  have hsin : Real.sin (2 * γ) = Real.sin γ * Real.cos γ + Real.cos γ * Real.sin γ := by
    rw [show (2 : ℝ) * γ = γ + γ by ring, Real.sin_add]
  have hsq : Real.cos γ ^ 2 + Real.sin γ ^ 2 = 1 := Real.cos_sq_add_sin_sq γ
  have hm : d.m * (Real.cos γ ^ 2 + Real.sin γ ^ 2) = d.m := by rw [hsq]; ring
  have hj : d.j * (Real.cos γ ^ 2 + Real.sin γ ^ 2) = d.j := by rw [hsq]; ring
  ext i k
  fin_cases i <;> fin_cases k
  all_goals simp [rotation, tensorOf, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply]
  all_goals apply Complex.ext
  all_goals simp [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_im]
  all_goals try simp only [rotX, rotZ, rotAtX, rotAtZ]
  all_goals try rw [hcos]
  all_goals try rw [hsin]
  all_goals nlinarith [hm, hj]

@[expose] noncomputable def rotateParams (γ : ℝ) (p : BIParams) : BIParams :=
  let dA := decompA p
  let dD := decompD p
  let dG := decompG p
  { ee00 := dA.m + rotZ γ dA.x dA.z
    ee01 := rotX γ dA.x dA.z
    ee11 := dA.m - rotZ γ dA.x dA.z
    mm00 := dD.m + rotZ γ dD.x dD.z
    mm01 := rotX γ dD.x dD.z
    mm11 := dD.m - rotZ γ dD.x dD.z
    g00 := dG.m + rotZ γ dG.x dG.z
    g01 := rotX γ dG.x dG.z - dG.j
    g10 := rotX γ dG.x dG.z + dG.j
    g11 := dG.m - rotZ γ dG.x dG.z }

theorem rotateParams_eeBlock (γ : ℝ) (p : BIParams) :
    (rotateParams γ p).eeBlock = (rotation γ).transpose * p.eeBlock * rotation γ := by
  rw [← tensorOf_decompA (rotateParams γ p), ← tensorOf_decompA p,
    tensor_conjugate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [decompA, rotateParams, tensorOf, Matrix.cons_val_zero,
      Matrix.cons_val_one]

theorem rotateParams_mmBlock (γ : ℝ) (p : BIParams) :
    (rotateParams γ p).mmBlock = (rotation γ).transpose * p.mmBlock * rotation γ := by
  rw [← tensorOf_decompD (rotateParams γ p), ← tensorOf_decompD p,
    tensor_conjugate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [decompD, rotateParams, tensorOf, Matrix.cons_val_zero,
      Matrix.cons_val_one]

theorem rotateParams_gBlock (γ : ℝ) (p : BIParams) :
    gBlock (rotateParams γ p) = (rotation γ).transpose * gBlock p * rotation γ := by
  rw [← tensorOf_decompG (rotateParams γ p), ← tensorOf_decompG p,
    tensor_conjugate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [decompG, rotateParams, tensorOf, Matrix.cons_val_zero,
      Matrix.cons_val_one]

end BIRotation
end GSTC.Scattering
