/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.NormalIncidence

public section

namespace GSTC.Scattering

open scoped Matrix

theorem cFactor_zero (m : Medium) : cFactor m 0 = 1 := by
  simp [cFactor]

theorem zTM_zero (m : Medium) : zTM m 0 = m.eta := by
  simp [zTM, cFactor_zero]

theorem zTE_zero (m : Medium) : zTE m 0 = m.eta := by
  simp [zTE, cFactor_zero]

theorem waveY_normal (m : Medium) :
    waveY m 0 = ((1 / (m.eta : ℂ))) • (1 : Ten2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [waveY, zTM_zero, zTE_zero, Matrix.smul_apply]

theorem smul_mul_comm (M N : Ten2) (c : ℂ) : c • (M * N) = M * (c • N) := by
  symm
  exact Matrix.mul_smul M c N

@[expose] def BoundaryCoeffs.congr (A : Ten2) (b : BoundaryCoeffs) : BoundaryCoeffs where
  beI := Matrix.transpose A * b.beI * A
  beR := Matrix.transpose A * b.beR * A
  beT := Matrix.transpose A * b.beT * A
  bhI := Matrix.transpose A * b.bhI * A
  bhR := Matrix.transpose A * b.bhR * A
  bhT := Matrix.transpose A * b.bhT * A

end GSTC.Scattering
