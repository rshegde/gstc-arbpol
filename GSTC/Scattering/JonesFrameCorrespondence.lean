/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.OrthogonalSpectralPhase

public section
set_option autoImplicit false
namespace GSTC.Scattering.JonesFrameCorrespondence
open Matrix PauliRepresentation
open scoped Matrix

@[expose] noncomputable def balancedPhase (t : ℝ) : Ten2 :=
  diag2 (Complex.exp ((t : ℂ) * Complex.I))
    (Complex.exp (((-t : ℝ) : ℂ) * Complex.I))

@[expose] noncomputable def generator : Ten2 := Complex.I • sigmaZ

@[expose] noncomputable def base (U V : Ten2) (z : ℂ) : Ten2 :=
  (z • V) * U.conjTranspose

@[expose] noncomputable def tangent (U V : Ten2) (z : ℂ) : Ten2 :=
  (z • V) * generator * U.conjTranspose

@[expose] noncomputable def frameCoefficients (U V : Ten2) (z : ℂ) : PhaseCoefficients :=
  let a := coordinates (base U V z)
  let b := coordinates (tangent U V z)
  ⟨a 0, a 1, a 2, a 3, b 0, b 1, b 2, b 3⟩

theorem generator_unitary : generator ∈ unitary Ten2 := by
  apply Unitary.mem_iff.mpr
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [generator, sigmaZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem generator_det : generator.det = 1 := by
  simp [generator, sigmaZ, Matrix.det_fin_two]

theorem generator_adjoint : generator.conjTranspose = -generator := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [generator, sigmaZ]

theorem balancedPhase_eq (t : ℝ) :
    balancedPhase t = (Real.cos t : ℂ) • (1 : Ten2) +
      (Real.sin t : ℂ) • generator := by
  have hn : Complex.exp (-((t : ℂ) * Complex.I)) =
      (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I := by
    simpa [sub_eq_add_neg] using Complex.exp_ofReal_mul_I (-t)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balancedPhase, diag2, generator, sigmaZ, hn, Complex.exp_ofReal_mul_I,
      sub_eq_add_neg]

theorem base_unitary (U V : Ten2) (z : ℂ)
    (hU : U ∈ unitary Ten2) (hV : V ∈ unitary Ten2) (hz : ‖z‖ = 1) :
    base U V z ∈ unitary Ten2 :=
  (unitary Ten2).mul_mem
    (Unitary.smul_mem_of_mem (NBPhaseConstraints.nb_phase_mem_unitary z hz) hV)
    (Unitary.star_mem hU)

theorem tangent_unitary (U V : Ten2) (z : ℂ)
    (hU : U ∈ unitary Ten2) (hV : V ∈ unitary Ten2) (hz : ‖z‖ = 1) :
    tangent U V z ∈ unitary Ten2 :=
  (unitary Ten2).mul_mem ((unitary Ten2).mul_mem
    (Unitary.smul_mem_of_mem (NBPhaseConstraints.nb_phase_mem_unitary z hz) hV)
    generator_unitary) (Unitary.star_mem hU)

theorem tangent_det (U V : Ten2) (z : ℂ) :
    (tangent U V z).det = (base U V z).det := by
  simp [tangent, base, Matrix.det_mul, generator_det]

theorem base_tangent_skew (U V : Ten2) (z : ℂ) (hU : U ∈ unitary Ten2) :
    base U V z * (tangent U V z).conjTranspose +
      tangent U V z * (base U V z).conjTranspose = 0 := by
  have hu : U.conjTranspose * U = 1 := (Unitary.mem_iff.mp hU).1
  simp only [base, tangent, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc U.conjTranspose U, hu, Matrix.one_mul]
  rw [generator_adjoint]
  simp

theorem frameCoefficients_orthonormal (U V : Ten2) (z : ℂ)
    (hU : U ∈ unitary Ten2) (hV : V ∈ unitary Ten2) (hz : ‖z‖ = 1)
    (hd : (base U V z).det = 1) :
    let c := frameCoefficients U V z
    (c.q_c^2 + c.a_x^2 + c.a_y^2 + c.a_z^2 = 1) ∧
    (c.q_s^2 + c.b_x^2 + c.b_y^2 + c.b_z^2 = 1) ∧
    (c.q_c*c.q_s + c.a_x*c.b_x + c.a_y*c.b_y + c.a_z*c.b_z = 0) := by
  have hA := base_unitary U V z hU hV hz
  have hB := tangent_unitary U V z hU hV hz
  refine ⟨coordinates_unit_sphere _ hA, coordinates_unit_sphere _ hB, ?_⟩
  have hAB := base_tangent_skew U V z hU
  have hpa := special_unitary_pauli _ hA hd
  have hpb := special_unitary_pauli _ hB ((tangent_det U V z).trans hd)
  rw [hpa, hpb] at hAB
  have hh := congrArg (fun M : Ten2 => (M 0 0).re) hAB
  simp only [Matrix.add_apply, Complex.add_re, Matrix.zero_apply, Complex.zero_re,
    pauli_pairing] at hh
  dsimp [frameCoefficients]
  nlinarith only [hh]

theorem phaseMatrix_frame (U V : Ten2) (z : ℂ)
    (hU : U ∈ unitary Ten2) (hV : V ∈ unitary Ten2) (hz : ‖z‖ = 1)
    (hd : (base U V z).det = 1) (t : ℝ) :
    phaseMatrix (frameCoefficients U V z) t =
      z • (V * balancedPhase t * U.conjTranspose) := by
  have ha := special_unitary_pauli _ (base_unitary U V z hU hV hz) hd
  have hb := special_unitary_pauli _ (tangent_unitary U V z hU hV hz)
    ((tangent_det U V z).trans hd)
  let c := frameCoefficients U V z
  have hlin : phaseMatrix c t =
      (Real.cos t : ℂ) • pauliForm c.q_c c.a_x c.a_y c.a_z +
      (Real.sin t : ℂ) • pauliForm c.q_s c.b_x c.b_y c.b_z := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [phaseMatrix, phaseQ, phaseRx, phaseRy, phaseRz,
        pauliForm, sigmaX, sigmaY, sigmaZ] <;> ring
  change phaseMatrix c t = _
  rw [hlin]
  change (Real.cos t : ℂ) • pauliForm (coordinates (base U V z) 0)
    (coordinates (base U V z) 1) (coordinates (base U V z) 2) (coordinates (base U V z) 3) +
    (Real.sin t : ℂ) • pauliForm (coordinates (tangent U V z) 0)
    (coordinates (tangent U V z) 1) (coordinates (tangent U V z) 2)
    (coordinates (tangent U V z) 3) = _
  rw [← ha, ← hb, balancedPhase_eq]
  simp [base, tangent, Matrix.mul_add, Matrix.add_mul,
    smul_smul, mul_comm, mul_assoc]

theorem exists_frameCoefficients (U V : Ten2)
    (hU : U ∈ unitary Ten2) (hV : V ∈ unitary Ten2) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (base U V z).det = 1 := by
  have hb : V * U.conjTranspose ∈ unitary Ten2 :=
    (unitary Ten2).mul_mem hV (Unitary.star_mem hU)
  obtain ⟨z, hz, hd⟩ := determinant_center _ hb
  exact ⟨z, hz, by simpa [base, Matrix.smul_mul] using hd⟩

theorem unit_phases_balanced (a b z : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hz : ‖z‖ = 1) :
    ∃ t α : ℝ,
      a = Complex.exp (Complex.I * α) * z * Complex.exp ((t : ℂ) * Complex.I) ∧
      b = Complex.exp (Complex.I * α) * z * Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨A, hA⟩ := (Complex.norm_eq_one_iff a).mp ha
  obtain ⟨B, hB⟩ := (Complex.norm_eq_one_iff b).mp hb
  obtain ⟨Z, hZ⟩ := (Complex.norm_eq_one_iff z).mp hz
  refine ⟨(A-B)/2, (A+B)/2-Z, ?_, ?_⟩
  · rw [← hA, ← hZ, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [← hB, ← hZ, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem scalar_frame_diagonal (U V : Ten2) (w a b : ℂ) :
    w • (V * diag2 a b * U.conjTranspose) =
      V * diag2 (w*a) (w*b) * U.conjTranspose := by
  have hd : diag2 (w*a) (w*b) = w • diag2 a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2]
  rw [hd, Matrix.mul_smul, Matrix.smul_mul]

theorem phaseTransmission_frame (U V : Ten2) (z : ℂ)
    (hU : U ∈ unitary Ten2) (hV : V ∈ unitary Ten2) (hz : ‖z‖ = 1)
    (hd : (base U V z).det = 1) (t α : ℝ) :
    phaseTransmission (frameCoefficients U V z) t α =
      V * diag2
        (Complex.exp (Complex.I * α) * z * Complex.exp ((t : ℂ) * Complex.I))
        (Complex.exp (Complex.I * α) * z *
          Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) * U.conjTranspose := by
  rw [phaseTransmission, phaseMatrix_frame U V z hU hV hz hd, smul_smul]
  exact scalar_frame_diagonal U V _ _ _

@[expose] def frameFamily (U V T : Ten2) : Prop :=
  ∃ a b : ℂ, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ T = V * diag2 a b * U.conjTranspose

theorem frameFamily_iff_phaseTransmission (U V : Ten2) (z : ℂ)
    (hU : U ∈ unitary Ten2) (hV : V ∈ unitary Ten2) (hz : ‖z‖ = 1)
    (hd : (base U V z).det = 1) (T : Ten2) :
    frameFamily U V T ↔
      ∃ t α : ℝ, T = phaseTransmission (frameCoefficients U V z) t α := by
  constructor
  · rintro ⟨a,b,ha,hb,rfl⟩
    obtain ⟨t,α,h₁,h₂⟩ := unit_phases_balanced a b z ha hb hz
    exact ⟨t,α,by rw [phaseTransmission_frame U V z hU hV hz hd, ← h₁, ← h₂]⟩
  · rintro ⟨t,α,rfl⟩
    have hα : ‖Complex.exp (Complex.I * α)‖ = 1 := by
      rw [mul_comm]
      exact Complex.norm_exp_ofReal_mul_I α
    refine ⟨_,_,?_,?_,phaseTransmission_frame U V z hU hV hz hd t α⟩ <;>
      rw [norm_mul, norm_mul, hα, hz, Complex.norm_exp_ofReal_mul_I] <;> norm_num

@[expose] def column (U : Ten2) (j : Fin 2) : Vec2 := fun i => U i j

theorem column_normalized (U : Ten2) (hU : U ∈ unitary Ten2) (j : Fin 2) :
    BIPhysicalFeasibility.isNormalizedJones (column U j) := by
  apply (BIPhysicalFeasibility.isNormalizedJones_iff _).mpr
  have hu : U.conjTranspose * U = 1 := (Unitary.mem_iff.mp hU).1
  have hh := congrArg (fun M : Ten2 => M j j) hu
  simpa [isNormalized, jonesInner, column, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct] using hh

theorem frameFamily_iff_columns (U V T : Ten2) (hU : U ∈ unitary Ten2) :
    frameFamily U V T ↔ ∃ a b : ℂ, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
      T *ᵥ column U 0 = a • column V 0 ∧
      T *ᵥ column U 1 = b • column V 1 := by
  have hu : U.conjTranspose * U = 1 := (Unitary.mem_iff.mp hU).1
  have hu' : U * U.conjTranspose = 1 := (Unitary.mem_iff.mp hU).2
  have matrix_columns (a b : ℂ) : T * U = V * diag2 a b ↔
      T *ᵥ column U 0 = a • column V 0 ∧
      T *ᵥ column U 1 = b • column V 1 := by
    constructor
    · intro h
      constructor <;> ext i
      · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, column, diag2,
          Fin.sum_univ_two, mul_comm] using congrArg (fun M : Ten2 => M i 0) h
      · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, column, diag2,
          Fin.sum_univ_two, mul_comm] using congrArg (fun M : Ten2 => M i 1) h
    · rintro ⟨h0,h1⟩
      ext i j
      fin_cases j
      · have hh := congrFun h0 i
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, column, diag2,
          Fin.sum_univ_two] at hh ⊢
        linear_combination hh
      · have hh := congrFun h1 i
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, column, diag2,
          Fin.sum_univ_two] at hh ⊢
        linear_combination hh
  constructor
  · rintro ⟨a,b,ha,hb,hT⟩
    refine ⟨a,b,ha,hb,(matrix_columns a b).mp ?_⟩
    rw [hT, Matrix.mul_assoc, Matrix.mul_assoc, hu, Matrix.mul_one]
  · rintro ⟨a,b,ha,hb,h0,h1⟩
    refine ⟨a,b,ha,hb,?_⟩
    have hm := congrArg (fun M : Ten2 => M * U.conjTranspose)
      ((matrix_columns a b).mpr ⟨h0,h1⟩)
    simpa only [Matrix.mul_assoc, hu', Matrix.mul_one] using hm

end GSTC.Scattering.JonesFrameCorrespondence
