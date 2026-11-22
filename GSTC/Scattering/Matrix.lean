/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Prelude

open scoped Matrix

public section

namespace GSTC.Scattering

abbrev Vec2 := Fin 2 → ℂ

abbrev Row2 := Matrix (Fin 1) (Fin 2) ℂ

abbrev Ten2 := Matrix (Fin 2) (Fin 2) ℂ

@[expose] def dot2 (u v : Vec2) : ℂ := u 0 * v 0 + u 1 * v 1

@[expose] def outer (u v : Vec2) : Ten2 :=
  !![u 0 * v 0, u 0 * v 1; u 1 * v 0, u 1 * v 1]

@[expose] def colRow (u : Vec2) (r : Row2) : Ten2 :=
  !![u 0 * r 0 0, u 0 * r 0 1; u 1 * r 0 0, u 1 * r 0 1]

theorem outer_zero_right (u : Vec2) : outer u 0 = 0 := by
  ext i j
  fin_cases i
  all_goals (fin_cases j <;> simp [outer])

theorem colRow_zero_left (r : Row2) : colRow 0 r = 0 := by
  ext i j
  fin_cases i
  all_goals (fin_cases j <;> simp [colRow])

@[expose] def rowEval (r : Row2) (v : Vec2) : ℂ := r 0 0 * v 0 + r 0 1 * v 1

@[expose] noncomputable def ten2_inv (A : Ten2) (_h : A.det ≠ 0) : Ten2 :=
  !![A 1 1 / A.det, -(A 0 1) / A.det; -(A 1 0) / A.det, A 0 0 / A.det]

theorem ten2_inv_eq_inv (A : Ten2) (h : A.det ≠ 0) : ten2_inv A h = A⁻¹ := by
  have h' : A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0 := by
    simpa [Matrix.det_fin_two] using h
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ten2_inv, Matrix.adjugate_apply, Matrix.det_fin_two] <;>
    field_simp

theorem ten2_inv_mul (A : Ten2) (h : A.det ≠ 0) : ten2_inv A h * A = (1 : Ten2) := by
  rw [ten2_inv_eq_inv A h]
  exact Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr h)

theorem ten2_mul_inv (A : Ten2) (h : A.det ≠ 0) : A * ten2_inv A h = (1 : Ten2) := by
  rw [ten2_inv_eq_inv A h]
  exact Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr h)

end GSTC.Scattering
