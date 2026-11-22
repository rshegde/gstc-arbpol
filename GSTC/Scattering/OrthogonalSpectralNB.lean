/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.

Licensed under the MIT License.

Part of the GSTC formalization of the manuscript
`rshegde/paper-gstc_arbpol_bounds`, Section 3B.1.
-/
module

public import GSTC.Scattering.NBFeasibilityClassification
public import GSTC.Scattering.OrthogonalSpectralPole
public import GSTC.Scattering.PauliRepresentation

public section
set_option autoImplicit false

namespace GSTC.Scattering
namespace OrthogonalSpectralNB

open scoped Matrix
open PauliRepresentation
open OrthogonalSpectralBridge
open NBFeasibilityClassification
open BIFeasibility
open JonesOperatorClassification

theorem phaseMatrix_eq_pauliForm (c : PhaseCoefficients) (t : ℝ) :
    phaseMatrix c t
      = pauliForm (phaseQ c t) (phaseRx c t) (phaseRy c t) (phaseRz c t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseMatrix, pauliForm, sigmaX, sigmaY, sigmaZ,
      Matrix.add_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

private theorem smul_transpose_iff (z : ℂ) (M : Ten2) (hz : z ≠ 0) :
    (z • M).transpose = z • M ↔ M.transpose = M := by
  constructor
  · intro h
    have h' : z • M.transpose = z • M := by
      ext i j
      have hh := congrArg (fun X : Ten2 => X i j) h
      simp only [Matrix.transpose_apply, Matrix.smul_apply] at hh
      exact hh
    ext i j
    have hh := congrArg (fun X : Ten2 => X i j) h'
    simp only [Matrix.smul_apply] at hh
    exact mul_left_cancel₀ hz hh
  · intro h
    ext i j
    have hh := congrArg (fun X : Ten2 => X j i) h
    rw [Matrix.transpose_apply] at hh
    simp only [Matrix.transpose_apply, Matrix.smul_apply]
    rw [← hh]

theorem phaseMatrix_transpose_symm_iff (c : PhaseCoefficients) (t : ℝ) :
    (phaseMatrix c t).transpose = phaseMatrix c t ↔ phaseRy c t = 0 := by
  rw [phaseMatrix_eq_pauliForm]
  exact pauliSymmetry_iff _ _ _ _

theorem phaseTransmission_transpose_symm_iff (c : PhaseCoefficients) (t α : ℝ) :
    (phaseTransmission c t α).transpose = phaseTransmission c t α ↔ phaseRy c t = 0 := by
  rw [phaseTransmission]
  exact (smul_transpose_iff _ _ (Complex.exp_ne_zero _)).trans
    (phaseMatrix_transpose_symm_iff c t)

theorem nb_phaseFamily_feasible_iff (cfg : Config) (c : PhaseCoefficients)
    (t α : ℝ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hsphere : phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1) :
    (∃ z : ℂ, ∃ p : BIParams, ‖z‖ = 1 ∧ NoCoupling p ∧
        biForwardT cfg p = z • phaseTransmission c t α)
      ↔ phaseRy c t = 0 := by
  have hu : phaseTransmission c t α ∈ unitary Ten2 := by
    rw [← jonesUnitary_iff_mem_unitary]
    unfold JonesUnitary
    rw [show (ten2Adjoint (phaseTransmission c t α)
        : Ten2) = (phaseTransmission c t α).conjTranspose from by
      ext i j
      simp [ten2Adjoint, Matrix.conjTranspose_apply]]
    exact phaseTransmission_unitary c t α hsphere
  rw [nb_unitary_feasible_iff_symmetric cfg (phaseTransmission c t α) hk heq hu]
  exact phaseTransmission_transpose_symm_iff c t α

end OrthogonalSpectralNB
end GSTC.Scattering
