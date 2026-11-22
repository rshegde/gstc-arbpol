/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.JonesOperatorClassification

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

public section
namespace GSTC.Scattering
namespace PauliRepresentation

open scoped Matrix

@[expose] def sigmaX : Ten2 := !![0, 1; 1, 0]

@[expose] def sigmaY : Ten2 := !![0, -Complex.I; Complex.I, 0]

@[expose] def sigmaZ : Ten2 := !![1, 0; 0, -1]

@[expose] noncomputable def pauliForm (q r_x r_y r_z : ℝ) : Ten2 :=
  q • (1 : Ten2) + Complex.I • (r_x • sigmaX + r_y • sigmaY + r_z • sigmaZ)

theorem pauliForm_apply_zero_one (q r_x r_y r_z : ℝ) :
    pauliForm q r_x r_y r_z 0 1 = Complex.I * r_x + r_y := by
  simp [pauliForm, sigmaX, sigmaY, sigmaZ]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem pauliForm_apply_one_zero (q r_x r_y r_z : ℝ) :
    pauliForm q r_x r_y r_z 1 0 = Complex.I * r_x - r_y := by
  simp [pauliForm, sigmaX, sigmaY, sigmaZ]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem pauliSymmetry_iff (q r_x r_y r_z : ℝ) :
    (pauliForm q r_x r_y r_z).transpose = pauliForm q r_x r_y r_z ↔ r_y = 0 := by
  constructor
  · intro h
    have h01 := congrArg (fun M : Ten2 => M 0 1) h
    rw [Matrix.transpose_apply, pauliForm_apply_one_zero, pauliForm_apply_zero_one] at h01
    have hre := congrArg Complex.re h01
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at hre
    linarith
  · intro hr
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [pauliForm, sigmaX, sigmaY, sigmaZ, hr]

@[expose] def coordinates (M : Ten2) : Fin 4 → ℝ :=
  ![(M 0 0).re, (M 0 1).im, (M 0 1).re, (M 0 0).im]

theorem norm_det_unitary (X : Ten2) (hX : X ∈ unitary Ten2) : ‖X.det‖ = 1 := by
  have hu : X.conjTranspose * X = 1 := (Unitary.mem_iff.mp hX).1
  have hd := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at hd
  have hn := congrArg norm hd
  simp only [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg X.det]

theorem determinant_center (X : Ten2) (hX : X ∈ unitary Ten2) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (z • X).det = 1 := by
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff X.det).mp (norm_det_unitary X hX)
  refine ⟨Complex.exp (((-θ / 2 : ℝ) : ℂ) * Complex.I),
    Complex.norm_exp_ofReal_mul_I _, ?_⟩
  rw [Matrix.det_smul, Fintype.card_fin, pow_two, ← hθ,
    ← Complex.exp_add, ← Complex.exp_add]
  convert Complex.exp_zero using 1
  congr 1
  push_cast
  ring

theorem adjoint_eq_adjugate (M : Ten2) (hM : M ∈ unitary Ten2) (hd : M.det = 1) :
    M.conjTranspose = M.adjugate := by
  have hu : M.conjTranspose * M = 1 := (Unitary.mem_iff.mp hM).1
  calc
    M.conjTranspose = M.conjTranspose * (M * M.adjugate) := by
      rw [Matrix.mul_adjugate, hd, one_smul, Matrix.mul_one]
    _ = M.adjugate := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]

theorem special_unitary_pauli (M : Ten2) (hM : M ∈ unitary Ten2) (hd : M.det = 1) :
    M = pauliForm (coordinates M 0) (coordinates M 1)
      (coordinates M 2) (coordinates M 3) := by
  have ha := adjoint_eq_adjugate M hM hd
  rw [Matrix.adjugate_fin_two] at ha
  have h00 := congrArg (fun A : Ten2 => A 0 0) ha
  have h10 := congrArg (fun A : Ten2 => A 1 0) ha
  have hd' : M 1 1 = star (M 0 0) := by
    simpa [Matrix.conjTranspose_apply] using h00.symm
  have hc' : M 1 0 = -star (M 0 1) := by
    simpa [Matrix.conjTranspose_apply] using (congrArg Neg.neg h10).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [coordinates, pauliForm, sigmaX, sigmaY, sigmaZ, hd', hc']

theorem coordinates_unit_sphere (M : Ten2) (hM : M ∈ unitary Ten2) :
    coordinates M 0 ^ 2 + coordinates M 1 ^ 2 +
      coordinates M 2 ^ 2 + coordinates M 3 ^ 2 = 1 := by
  have hu : M * M.conjTranspose = 1 := (Unitary.mem_iff.mp hM).2
  have hh := congrArg (fun A : Ten2 => (A 0 0).re) hu
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Complex.mul_re, coordinates] at hh ⊢
  nlinarith [hh]

theorem pauli_pairing (q x y z q' x' y' z' : ℝ) :
    ((pauliForm q x y z * (pauliForm q' x' y' z').conjTranspose) 0 0).re =
      q*q' + x*x' + y*y' + z*z' := by
  simp [pauliForm, sigmaX, sigmaY, sigmaZ, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring

end PauliRepresentation
end GSTC.Scattering
