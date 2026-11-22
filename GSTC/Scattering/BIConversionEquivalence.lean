/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIAdjugate
public import GSTC.Scattering.BIPhysicalFeasibility

public section

namespace GSTC.Scattering

open scoped Matrix
open BIFeasibility
open BIPhysicalFeasibility

private lemma smul_vec_cancel (a : ℂ) (x y : Vec2) (ha : a ≠ 0)
    (h : a • x = a • y) : x = y := by
  ext i
  have hi := congrArg (fun v : Vec2 => v i) h
  simpa only [Pi.smul_apply] using mul_left_cancel₀ ha hi

private lemma smulMatrix_mulVec (a : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Vec2) :
    (a • M) *ᵥ v = a • (M *ᵥ v) := by
  ext i
  simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Matrix.smul_apply,
    Pi.smul_apply]
  ring

private lemma smul_smul (a b : ℂ) (v : Vec2) : (a * b) • v = a • (b • v) := by
  ext i
  simp only [Pi.smul_apply]
  ring

theorem biForwardT_eq_iff_cleared (cfg : Config) (p : BIParams) (u v : Vec2)
    (α : ℂ) :
    biForwardT cfg p *ᵥ u = α • v
      ↔ biNumeratorT cfg p *ᵥ u = (biDet cfg p * α) • v := by
  have hdet := biDet_ne_zero cfg p
  have hmul := biDet_mul_forwardT cfg p
  constructor
  · intro h
    rw [← hmul, smulMatrix_mulVec, h]
    exact (smul_smul _ _ _).symm
  · intro h
    have hQ : (biDet cfg p • biForwardT cfg p) *ᵥ u
        = (biDet cfg p * α) • v := by
      rw [← hmul] at h
      exact h
    rw [smulMatrix_mulVec] at hQ
    have hQ' : biDet cfg p • (biForwardT cfg p *ᵥ u)
        = biDet cfg p • (α • v) := by
      rw [← smul_smul]
      exact hQ
    exact smul_vec_cancel _ _ _ hdet hQ'

end GSTC.Scattering
