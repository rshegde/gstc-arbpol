/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Operator.BoundaryOperator

open scoped Matrix

public section

namespace GSTC.Scattering.Operator

open GSTC.Scattering

theorem mulVec_injective_of_det_ne_zero {M : Matrix (Fin 4) (Fin 4) ℂ} (h : M.det ≠ 0)
    {z1 z2 : Vec4} (hz : M *ᵥ z1 = M *ᵥ z2) : z1 = z2 := by
  have h0 : M *ᵥ (z1 - z2) = 0 := by rw [Matrix.mulVec_sub, hz, sub_self]
  by_contra hne
  exact (Matrix.exists_mulVec_eq_zero_iff.not.mpr h) ⟨z1 - z2, sub_ne_zero.mpr hne, h0⟩

end GSTC.Scattering.Operator
