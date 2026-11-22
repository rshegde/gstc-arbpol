/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Matrix

open scoped Matrix

public section

namespace GSTC.Scattering

@[expose] def ncross : Ten2 := !![0, -1; 1, 0]

@[expose] def iPar : Ten2 := 1

theorem iPar_mulVec (v : Vec2) : iPar *ᵥ v = v := by
  rw [iPar]
  simp

theorem ncross_apply (v : Vec2) : ncross *ᵥ v = ![-v 1, v 0] := by
  funext i
  fin_cases i
  · rw [Matrix.mulVec_apply_eq_sum]
    simp [ncross]
  · rw [Matrix.mulVec_apply_eq_sum]
    simp [ncross]

end GSTC.Scattering
