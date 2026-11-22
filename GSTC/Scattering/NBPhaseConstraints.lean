/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.NBSynthesis

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NoncommRing

public section

namespace GSTC.Scattering
namespace NBPhaseConstraints

open scoped Matrix
open scoped ComplexConjugate

@[expose] def bilinear (x y : Vec2) : ℂ := x 0 * y 0 + x 1 * y 1

theorem bilinear_comm (x y : Vec2) : bilinear x y = bilinear y x := by
  simp [bilinear]
  ring

theorem bilinear_smul_right (c : ℂ) (x y : Vec2) :
    bilinear x (c • y) = c * bilinear x y := by
  simp [bilinear, Pi.smul_apply, smul_eq_mul]
  ring

theorem bilinear_mulVec (X : Ten2) (a b : Vec2) :
    bilinear (X *ᵥ a) b = bilinear a (X.transpose *ᵥ b) := by
  simp [bilinear, Matrix.mulVec_apply]
  ring

theorem nb_two_state_phase_forced {T : Ten2} (hT : T.transpose = T)
    {u₁ u₂ v₁ v₂ : Vec2} {γ₁ γ₂ : ℂ}
    (h₁ : T *ᵥ u₁ = γ₁ • v₁) (h₂ : T *ᵥ u₂ = γ₂ • v₂) :
    γ₁ * bilinear u₂ v₁ = γ₂ * bilinear u₁ v₂ := by
  have hsym : T.transpose *ᵥ u₂ = T *ᵥ u₂ := by
    rw [hT]
  calc γ₁ * bilinear u₂ v₁
      = bilinear u₂ (γ₁ • v₁) := by rw [← bilinear_smul_right]
    _ = bilinear u₂ (T *ᵥ u₁) := by rw [h₁]
    _ = bilinear (T *ᵥ u₁) u₂ := by rw [bilinear_comm]
    _ = bilinear u₁ (T.transpose *ᵥ u₂) := bilinear_mulVec T u₁ u₂
    _ = bilinear u₁ (T *ᵥ u₂) := by rw [hsym]
    _ = bilinear u₁ (γ₂ • v₂) := by rw [h₂]
    _ = γ₂ * bilinear u₁ v₂ := by rw [bilinear_smul_right]

theorem nb_phase_star_mul (φ : ℂ) (hφ : ‖φ‖ = 1) : star φ * φ = 1 := by
  rw [Complex.star_def, Complex.conj_mul', hφ]
  norm_num

theorem nb_phase_mem_unitary (φ : ℂ) (hφ : ‖φ‖ = 1) : φ ∈ unitary ℂ := by
  rw [Unitary.mem_iff]
  constructor
  · exact nb_phase_star_mul φ hφ
  · simpa [mul_comm] using nb_phase_star_mul φ hφ

theorem nb_phase_midpoint (X Y : Ten2) (φ : ℂ) :
    ((1 / 2 : ℂ) • (φ • X + φ • Y)) = φ • ((1 / 2 : ℂ) • (X + Y)) := by
  module

theorem nb_phase_preserves_symmetric_unitary {X : Ten2} (hX : X.transpose = X)
    (hU : X ∈ unitary Ten2) (φ : ℂ) (hφ : ‖φ‖ = 1) :
    (φ • X).transpose = φ • X ∧ (φ • X) ∈ unitary Ten2 := by
  constructor
  · rw [Matrix.transpose_smul, hX]
  · exact Unitary.smul_mem_of_mem (nb_phase_mem_unitary φ hφ) hU

end NBPhaseConstraints

end GSTC.Scattering
