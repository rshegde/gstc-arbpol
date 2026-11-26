/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.JonesFrameSpectralMinimum
public import GSTC.Scattering.OrthogonalSpectralMinimum
public import GSTC.Scattering.PauliRepresentation

public section
set_option autoImplicit false
namespace GSTC.Scattering.LinearCircularSpectralMinimum

open Matrix PauliRepresentation JonesFrameCorrespondence OrthogonalSpectralPhase
open ClassFeasibility ClassMinimumBudget SusceptibilityBudget BIFeasibility
open BIPolynomials MaterialSpace
open scoped Matrix

@[expose] noncomputable def invSqrtTwo : ℝ := 1 / Real.sqrt 2

theorem invSqrtTwo_sq : invSqrtTwo ^ 2 = 1 / 2 := by
  unfold invSqrtTwo
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]

theorem two_mul_invSqrtTwo : 2 * invSqrtTwo = Real.sqrt 2 := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  unfold invSqrtTwo
  calc 2 * (1 / Real.sqrt 2) = (2 * 1) / Real.sqrt 2 := by rw [mul_div_assoc]
    _ = 2 / Real.sqrt 2 := by rw [mul_one]
    _ = Real.sqrt 2 := by
      rw [div_eq_iff hne]
      nlinarith [hsq]

theorem sqrt_two_div_two : Real.sqrt 2 / 2 = invSqrtTwo := by
  rw [div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)]
  rw [mul_comm]
  exact two_mul_invSqrtTwo.symm

theorem sqrt_half_eq_invSqrtTwo : Real.sqrt (1 / 2) = invSqrtTwo := by
  have h1 : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h3 : 0 ≤ Real.sqrt (1 / 2) := Real.sqrt_nonneg _
  have h4 : 0 ≤ Real.sqrt 2 / 2 := by positivity
  have h5 : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by nlinarith [h1, h2, h3, h4]
  rw [h5, sqrt_two_div_two]

@[expose] noncomputable def linearCircular : Ten2 :=
  !![(invSqrtTwo : ℂ), (invSqrtTwo : ℂ);
    Complex.I * (invSqrtTwo : ℂ), -(Complex.I * (invSqrtTwo : ℂ))]

@[expose] noncomputable def circularStateOne : Vec2 :=
  fun i => if i = 0 then (invSqrtTwo : ℂ) else Complex.I * (invSqrtTwo : ℂ)

@[expose] noncomputable def circularStateTwo : Vec2 :=
  fun i => if i = 0 then (invSqrtTwo : ℂ) else -(Complex.I * (invSqrtTwo : ℂ))

theorem column_linearCircular_zero : column linearCircular 0 = circularStateOne := by
  funext i
  fin_cases i <;> simp [column, linearCircular, circularStateOne]

theorem column_linearCircular_one : column linearCircular 1 = circularStateTwo := by
  funext i
  fin_cases i <;> simp [column, linearCircular, circularStateTwo]

theorem one_mem_unitary : (1 : Ten2) ∈ unitary Ten2 := by
  simp

theorem linearCircular_unitary : linearCircular ∈ unitary Ten2 := by
  apply Unitary.mem_iff.mpr
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
      simp [linearCircular, Matrix.mul_apply, Fin.sum_univ_two] <;>
      nlinarith [invSqrtTwo_sq]

@[expose] noncomputable def circularCenter : ℂ := ⟨invSqrtTwo, invSqrtTwo⟩

theorem circularCenter_norm : ‖circularCenter‖ = 1 := by
  simp only [circularCenter]
  rw [Complex.norm_def, Complex.normSq_mk]
  have hX : invSqrtTwo * invSqrtTwo + invSqrtTwo * invSqrtTwo = 1 := by
    nlinarith [invSqrtTwo_sq]
  rw [hX, Real.sqrt_one]

theorem base_circular : base (1 : Ten2) linearCircular circularCenter
    = circularCenter • linearCircular := by
  simp [base, Matrix.conjTranspose_one]

theorem smul_circular : circularCenter • linearCircular
    = pauliForm (1 / 2) (1 / 2) (1 / 2) (1 / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
      simp [Matrix.smul_apply, linearCircular, circularCenter, pauliForm,
        sigmaX, sigmaY, sigmaZ, Matrix.add_apply] <;>
      nlinarith [invSqrtTwo_sq]

theorem base_linearCircular :
    base (1 : Ten2) linearCircular circularCenter
      = pauliForm (1 / 2) (1 / 2) (1 / 2) (1 / 2) := by
  rw [base_circular, smul_circular]

theorem tangent_linearCircular :
    tangent (1 : Ten2) linearCircular circularCenter
      = pauliForm (-1 / 2) (-1 / 2) (1 / 2) (1 / 2) := by
  have ht : tangent (1 : Ten2) linearCircular circularCenter
      = (circularCenter • linearCircular) * generator := by
    simp [tangent, Matrix.conjTranspose_one]
  rw [ht, smul_circular]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
      simp [pauliForm, generator, sigmaX, sigmaY, sigmaZ, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply] <;> ring

theorem base_circular_det : (base (1 : Ten2) linearCircular circularCenter).det = 1 := by
  rw [base_linearCircular]
  exact (pauliForm_special_unitary (1 / 2) (1 / 2) (1 / 2) (1 / 2) (by norm_num)).2

@[expose] noncomputable def circCoeffs : PhaseCoefficients :=
  ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2, -1 / 2, -1 / 2, 1 / 2, 1 / 2⟩

theorem circCoeffs_eq :
    circCoeffs = ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2, -1 / 2, -1 / 2, 1 / 2, 1 / 2⟩ := rfl

theorem frameCoefficients_linearCircular :
    frameCoefficients (1 : Ten2) linearCircular circularCenter = circCoeffs := by
  simp only [frameCoefficients]
  rw [base_linearCircular, tangent_linearCircular,
    coordinates_pauliForm, coordinates_pauliForm]
  rfl

theorem phaseQ_circ (t : ℝ) : phaseQ circCoeffs t = (Real.cos t - Real.sin t) / 2 := by
  simp [phaseQ, circCoeffs]
  ring

theorem phaseRx_circ (t : ℝ) : phaseRx circCoeffs t = (Real.cos t - Real.sin t) / 2 := by
  simp [phaseRx, circCoeffs]
  ring

theorem phaseRy_circ (t : ℝ) : phaseRy circCoeffs t = (Real.cos t + Real.sin t) / 2 := by
  simp [phaseRy, circCoeffs]
  ring

theorem phaseRz_circ (t : ℝ) : phaseRz circCoeffs t = (Real.cos t + Real.sin t) / 2 := by
  simp [phaseRz, circCoeffs]
  ring

theorem phaseMinimum_linearCircular (cfg : Config) (t : ℝ) :
    phaseMinimum cfg (frameCoefficients (1 : Ten2) linearCircular circularCenter) t
      = freeSpaceK0 cfg * 2 *
        max
          (max (spectralElectricScale cfg) (spectralMagneticScale cfg) * invSqrtTwo)
          (spectralChiralScale cfg * (|Real.cos t + Real.sin t| / 2))
        / (1 + |Real.cos t - Real.sin t| / 2) := by
  unfold phaseMinimum
  rw [frameCoefficients_linearCircular, phaseQ_circ, phaseRx_circ,
    phaseRy_circ, phaseRz_circ]
  have hsq : ((Real.cos t - Real.sin t) / 2) ^ 2 + ((Real.cos t + Real.sin t) / 2) ^ 2
      = 1 / 2 := by
    nlinarith [Real.cos_sq_add_sin_sq t]
  rw [hsq, sqrt_half_eq_invSqrtTwo]
  simp only [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

@[expose] noncomputable def circularBudget (t : ℝ) : ℝ :=
  Real.sqrt 2 / (1 + |Real.cos t - Real.sin t| / 2)

@[expose] noncomputable def circularBudgetMin : ℝ := 2 * (Real.sqrt 2 - 1)

@[expose] noncomputable def circularOptimumPhase : ℝ := 3 * Real.pi / 4

theorem abs_cos_add_sin_le (t : ℝ) : |Real.cos t + Real.sin t| ≤ Real.sqrt 2 := by
  have hsq : (Real.cos t + Real.sin t) ^ 2 ≤ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq t, sq_nonneg (Real.cos t + Real.sin t),
      sq_nonneg (Real.cos t - Real.sin t)]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq

theorem abs_cos_sub_sin_le (t : ℝ) : |Real.cos t - Real.sin t| ≤ Real.sqrt 2 := by
  have hsq : (Real.cos t - Real.sin t) ^ 2 ≤ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq t, sq_nonneg (Real.cos t - Real.sin t),
      sq_nonneg (Real.cos t + Real.sin t)]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq

theorem phaseMinimum_linearCircular_freeSpace (cfg : Config) (t : ℝ)
    (hω : cfg.omega = 1) (hη : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1) :
    phaseMinimum cfg (frameCoefficients (1 : Ten2) linearCircular circularCenter) t
      = circularBudget t := by
  rw [phaseMinimum_linearCircular cfg t]
  have hbound : |Real.cos t + Real.sin t| / 2 ≤ invSqrtTwo := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [mul_comm, two_mul_invSqrtTwo]
    exact abs_cos_add_sin_le t
  simp [circularBudget, freeSpaceK0, spectralElectricScale,
    spectralMagneticScale, spectralChiralScale, hω, hη, heps, hmu, hc0]
  rw [max_eq_left hbound, two_mul_invSqrtTwo]

theorem circularBudget_le (t : ℝ) : circularBudget t ≥ circularBudgetMin := by
  have hden : 0 < 1 + |Real.cos t - Real.sin t| / 2 := by positivity
  have hdn : 0 < 1 + Real.sqrt 2 / 2 := by positivity
  have hnum : 0 < Real.sqrt 2 := by positivity
  have hdenle : 1 + |Real.cos t - Real.sin t| / 2 ≤ 1 + Real.sqrt 2 / 2 := by
    have h := div_le_div_of_nonneg_right (abs_cos_sub_sin_le t)
      (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have h1 : Real.sqrt 2 / (1 + |Real.cos t - Real.sin t| / 2)
      ≥ Real.sqrt 2 / (1 + Real.sqrt 2 / 2) := by
    rw [ge_iff_le, div_le_div_iff₀ hdn hden]
    exact mul_le_mul_of_nonneg_left hdenle (le_of_lt hnum)
  have hid : Real.sqrt 2 / (1 + Real.sqrt 2 / 2) = 2 * (Real.sqrt 2 - 1) := by
    have hne : 1 + Real.sqrt 2 / 2 ≠ 0 := by positivity
    apply (div_eq_iff hne).2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold circularBudget circularBudgetMin
  linarith

theorem cos_three_pi_div_four : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2) / 2 := by
  rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_four]
  ring

theorem sin_three_pi_div_four : Real.sin (3 * Real.pi / 4) = (Real.sqrt 2) / 2 := by
  rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.sin_pi_sub,
    Real.sin_pi_div_four]

theorem circularBudget_eq_optimum :
    circularBudget circularOptimumPhase = circularBudgetMin := by
  have hdiff : Real.cos (3 * Real.pi / 4) - Real.sin (3 * Real.pi / 4)
      = -(Real.sqrt 2) := by
    rw [cos_three_pi_div_four, sin_three_pi_div_four]
    ring
  have habs : |Real.cos (3 * Real.pi / 4) - Real.sin (3 * Real.pi / 4)|
      = Real.sqrt 2 := by
    rw [hdiff, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold circularBudget circularBudgetMin circularOptimumPhase
  rw [habs]
  have hne : 1 + Real.sqrt 2 / 2 ≠ 0 := by positivity
  apply (div_eq_iff hne).2
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem nbAdmissible_linearCircular (t : ℝ) :
    nbAdmissible (frameCoefficients (1 : Ten2) linearCircular circularCenter) t
      ↔ Real.cos t + Real.sin t = 0 := by
  unfold nbAdmissible
  constructor
  · intro h
    have h' := (Set.mem_ofPred
      (p := fun y => phaseRy (frameCoefficients (1 : Ten2) linearCircular circularCenter) y = 0)
      (a := t)).1 h
    rw [frameCoefficients_linearCircular, phaseRy_circ] at h'
    linarith
  · intro h
    have h' : phaseRy (frameCoefficients (1 : Ten2) linearCircular circularCenter) t = 0 := by
      rw [frameCoefficients_linearCircular, phaseRy_circ]
      linarith
    exact (Set.mem_ofPred
      (p := fun y => phaseRy (frameCoefficients (1 : Ten2) linearCircular circularCenter) y = 0)
      (a := t)).2 h'

theorem nbAdmissible_circularOptimum :
    nbAdmissible (frameCoefficients (1 : Ten2) linearCircular circularCenter)
      circularOptimumPhase := by
  rw [nbAdmissible_linearCircular]
  unfold circularOptimumPhase
  rw [cos_three_pi_div_four, sin_three_pi_div_four]
  ring

theorem phaseMinimum_le_optimum (cfg : Config)
    (hω : cfg.omega = 1) (hη : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1) :
    ∀ t, phaseMinimum cfg (frameCoefficients (1 : Ten2) linearCircular circularCenter)
      circularOptimumPhase
      ≤ phaseMinimum cfg (frameCoefficients (1 : Ten2) linearCircular circularCenter) t := by
  intro t
  rw [phaseMinimum_linearCircular_freeSpace cfg _ hω hη heps hmu hc0,
    phaseMinimum_linearCircular_freeSpace cfg _ hω hη heps hmu hc0]
  rw [circularBudget_eq_optimum]
  exact circularBudget_le t

theorem biMinimum_linearCircular (cfg : Config)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hω : cfg.omega = 1) (hη : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1) :
    minimumBudget cfg .BI (column (1 : Ten2) 0) (column (1 : Ten2) 1)
      (column linearCircular 0) (column linearCircular 1) (1,1)
      = (2 * (Real.sqrt 2 - 1) : WithTop ℝ)
    ∧ ∃ p : BIParams,
        assign p ∈ classMaterials cfg .BI (column (1 : Ten2) 0)
          (column (1 : Ten2) 1) (column linearCircular 0)
          (column linearCircular 1) (1,1)
        ∧ spectralTotalBudget cfg (assign p) = 2 * (Real.sqrt 2 - 1) := by
  have hval : phaseMinimum cfg (frameCoefficients (1 : Ten2) linearCircular circularCenter)
      circularOptimumPhase = 2 * (Real.sqrt 2 - 1) := by
    rw [phaseMinimum_linearCircular_freeSpace cfg _ hω hη heps hmu hc0]
    exact circularBudget_eq_optimum
  obtain ⟨hb, hp⟩ := JonesFrameSpectralMinimum.bi_minimum_eq cfg (1 : Ten2)
    linearCircular circularCenter hk heq one_mem_unitary linearCircular_unitary
    circularCenter_norm base_circular_det circularOptimumPhase
    (phaseMinimum_le_optimum cfg hω hη heps hmu hc0)
  rw [hval] at hb
  obtain ⟨p, hp1, hp2⟩ := hp
  rw [hval] at hp2
  exact ⟨hb, p, hp1, hp2⟩

theorem nbMinimum_linearCircular (cfg : Config)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hω : cfg.omega = 1) (hη : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1) :
    minimumBudget cfg .NB (column (1 : Ten2) 0) (column (1 : Ten2) 1)
      (column linearCircular 0) (column linearCircular 1) (1,1)
      = (2 * (Real.sqrt 2 - 1) : WithTop ℝ)
    ∧ ∃ p : BIParams,
        NoCoupling p ∧
        assign p ∈ classMaterials cfg .NB (column (1 : Ten2) 0)
          (column (1 : Ten2) 1) (column linearCircular 0)
          (column linearCircular 1) (1,1)
        ∧ spectralTotalBudget cfg (assign p) = 2 * (Real.sqrt 2 - 1) := by
  have hval : phaseMinimum cfg (frameCoefficients (1 : Ten2) linearCircular circularCenter)
      circularOptimumPhase = 2 * (Real.sqrt 2 - 1) := by
    rw [phaseMinimum_linearCircular_freeSpace cfg _ hω hη heps hmu hc0]
    exact circularBudget_eq_optimum
  obtain ⟨hb, hp⟩ := JonesFrameSpectralMinimum.nb_minimum_eq cfg (1 : Ten2)
    linearCircular circularCenter hk heq one_mem_unitary linearCircular_unitary
    circularCenter_norm base_circular_det circularOptimumPhase
    nbAdmissible_circularOptimum
    (fun t _ => by
      rw [phaseMinimum_linearCircular_freeSpace cfg _ hω hη heps hmu hc0,
        phaseMinimum_linearCircular_freeSpace cfg _ hω hη heps hmu hc0]
      rw [circularBudget_eq_optimum]
      exact circularBudget_le t)
  rw [hval] at hb
  obtain ⟨p, hp1, hp2⟩ := hp
  rw [hval] at hp2
  have hnc : NoCoupling p := by
    have hcls := (mem_classMaterials_iff cfg .NB (column (1 : Ten2) 0)
      (column (1 : Ten2) 1) (column linearCircular 0)
      (column linearCircular 1) (1,1) (assign p)).mp hp1
    rw [parameters_assign] at hcls
    exact hcls.2
  exact ⟨hb, p, hnc, hp1, hp2⟩

theorem bi_eq_nb_minimum_linearCircular (cfg : Config)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (hω : cfg.omega = 1) (hη : cfg.upper.eta = 1)
    (heps : cfg.vac.eps0 = 1) (hmu : cfg.vac.mu0 = 1) (hc0 : cfg.vac.c0 = 1) :
    minimumBudget cfg .BI (column (1 : Ten2) 0) (column (1 : Ten2) 1)
      (column linearCircular 0) (column linearCircular 1) (1,1)
    = minimumBudget cfg .NB (column (1 : Ten2) 0) (column (1 : Ten2) 1)
      (column linearCircular 0) (column linearCircular 1) (1,1) := by
  have hb := biMinimum_linearCircular cfg hk heq hω hη heps hmu hc0
  have hn := nbMinimum_linearCircular cfg hk heq hω hη heps hmu hc0
  rw [hb.1, hn.1]

end GSTC.Scattering.LinearCircularSpectralMinimum
