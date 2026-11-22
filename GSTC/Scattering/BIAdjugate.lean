/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIFeasibility

public section

namespace GSTC.Scattering

open scoped Matrix
open BIFeasibility

@[expose] noncomputable def biDenominator (cfg : Config) (p : BIParams) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • biConstitutiveK cfg p

@[expose] noncomputable def biNumerator4 (cfg : Config) (p : BIParams) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Complex.I • biConstitutiveK cfg p

@[expose] noncomputable def biDet (cfg : Config) (p : BIParams) : ℂ :=
  (biDenominator cfg p).det

theorem biDet_ne_zero (cfg : Config) (p : BIParams) : biDet cfg p ≠ 0 := by
  have hu := biConstitutiveK_den_isUnit cfg p
  rw [biDet, biDenominator]
  exact (isUnit_iff_ne_zero).mp hu

@[expose] noncomputable def biAdjugateNumerator (cfg : Config) (p : BIParams) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  parityExchange * (biDenominator cfg p).adjugate * biNumerator4 cfg p

private lemma smul_mul_comm (a : ℂ) (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    (a • M) * N = M * (a • N) := by
  ext i j
  simp [Matrix.smul_apply, Matrix.mul_apply]
  ring

theorem biDenominator_mul_cayley (cfg : Config) (p : BIParams) :
    biDenominator cfg p * cayley4 (biConstitutiveK cfg p) = biNumerator4 cfg p := by
  have hD := biConstitutiveK_den_isUnit cfg p
  have h := (cayley4_eq (biConstitutiveK cfg p) hD (cayley4 (biConstitutiveK cfg p))).mpr rfl
  simpa [biDenominator, biNumerator4] using h

theorem biDet_mul_cayley (cfg : Config) (p : BIParams) :
    biDet cfg p • cayley4 (biConstitutiveK cfg p)
      = (biDenominator cfg p).adjugate * biNumerator4 cfg p := by
  have hadj : (biDenominator cfg p).adjugate * biDenominator cfg p
      = (biDenominator cfg p).det • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
    Matrix.adjugate_mul _
  calc biDet cfg p • cayley4 (biConstitutiveK cfg p)
      = (biDet cfg p • (1 : Matrix (Fin 4) (Fin 4) ℂ))
          * cayley4 (biConstitutiveK cfg p) := by
        rw [Matrix.smul_mul, Matrix.one_mul]
      _ = ((biDenominator cfg p).adjugate * biDenominator cfg p)
          * cayley4 (biConstitutiveK cfg p) := by
        rw [biDet, ← hadj]
      _ = (biDenominator cfg p).adjugate
          * (biDenominator cfg p * cayley4 (biConstitutiveK cfg p)) := by
        rw [Matrix.mul_assoc]
      _ = (biDenominator cfg p).adjugate * biNumerator4 cfg p := by
        rw [biDenominator_mul_cayley]

theorem biDet_mul_powerResponse (cfg : Config) (p : BIParams) :
    biDet cfg p • biPowerResponse4 cfg p = biAdjugateNumerator cfg p := by
  rw [biAdjugateNumerator, biPowerResponse4]
  calc biDet cfg p • (parityExchange * cayley4 (biConstitutiveK cfg p))
      = (biDet cfg p • parityExchange) * cayley4 (biConstitutiveK cfg p) := by
        rw [← Matrix.smul_mul]
      _ = parityExchange * (biDet cfg p • cayley4 (biConstitutiveK cfg p)) := by
        exact smul_mul_comm _ _ _
      _ = parityExchange
          * ((biDenominator cfg p).adjugate * biNumerator4 cfg p) := by
        rw [biDet_mul_cayley]
      _ = parityExchange * (biDenominator cfg p).adjugate * biNumerator4 cfg p := by
        rw [Matrix.mul_assoc]

@[expose] noncomputable def biNumeratorT (cfg : Config) (p : BIParams) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(biAdjugateNumerator cfg p) 2 0, (biAdjugateNumerator cfg p) 2 1;
     (biAdjugateNumerator cfg p) 3 0, (biAdjugateNumerator cfg p) 3 1]

theorem biDet_mul_forwardT (cfg : Config) (p : BIParams) :
    biDet cfg p • biForwardT cfg p = biNumeratorT cfg p := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 2 0)
    (biDet_mul_powerResponse cfg p)
  have h' := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 2 1)
    (biDet_mul_powerResponse cfg p)
  have h'' := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 3 0)
    (biDet_mul_powerResponse cfg p)
  have h''' := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 3 1)
    (biDet_mul_powerResponse cfg p)
  simp at h h' h'' h'''
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [biNumeratorT, biForwardT]
  · exact h
  · exact h'
  · exact h''
  · exact h'''

end GSTC.Scattering
