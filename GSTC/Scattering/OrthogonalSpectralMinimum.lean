/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.SusceptibilityBudget

public section
set_option autoImplicit false

namespace GSTC.Scattering

open BIPolynomials BIInverse MaterialSpace ClassFeasibility SusceptibilityBudget
open SpectralMatrixSupport
open scoped Matrix

@[expose] noncomputable def spectralElectricScale (cfg : Config) : ℝ :=
  1 / (cfg.omega * cfg.upper.eta * cfg.vac.eps0)

@[expose] noncomputable def spectralMagneticScale (cfg : Config) : ℝ :=
  cfg.upper.eta / (cfg.omega * cfg.vac.mu0)

@[expose] noncomputable def spectralChiralScale (cfg : Config) : ℝ :=
  cfg.vac.c0 / cfg.omega

@[expose] noncomputable def spectralLocusSheet (cfg : Config) (a d : ℝ) (x y : ℝ) : BIParams :=
  recoverParameters cfg (locusMatrix a d (x - Complex.I * y) 0 0 0)

theorem spectralLocusSheet_eq (cfg : Config) (a d : ℝ) (x y : ℝ) :
    spectralLocusSheet cfg a d x y =
      ⟨-spectralElectricScale cfg * a, -spectralElectricScale cfg * x,
        -spectralElectricScale cfg * d,
        -spectralMagneticScale cfg * d, spectralMagneticScale cfg * x,
        -spectralMagneticScale cfg * a,
        spectralChiralScale cfg * y, 0, 0, spectralChiralScale cfg * y⟩ := by
  have hω : cfg.omega ≠ 0 := ne_of_gt cfg.omega_pos
  have he : cfg.vac.eps0 ≠ 0 := ne_of_gt cfg.vac.eps0_pos
  have hm : cfg.vac.mu0 ≠ 0 := ne_of_gt cfg.vac.mu0_pos
  have hc : cfg.vac.c0 ≠ 0 := ne_of_gt cfg.vac.c0_pos
  simp [spectralLocusSheet, recoverParameters, locusMatrix, spectralElectricScale,
    spectralMagneticScale, spectralChiralScale,
    Real.sq_sqrt (le_of_lt cfg.upper.eta_pos),
    star_sub, star_mul, star_ofReal, star_I,
    Complex.sub_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  simp

theorem opNorm_electricBlock_locus (cfg : Config) (a d : ℝ) (x y : ℝ) :
    opNorm (electricBlock (assign (spectralLocusSheet cfg a d x y)))
      = spectralElectricScale cfg
        * (Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2|) := by
  have hE : 0 ≤ spectralElectricScale cfg := by
    have h1 := cfg.omega_pos
    have h2 := cfg.upper.eta_pos
    have h3 := cfg.vac.eps0_pos
    unfold spectralElectricScale
    positivity
  have hblk : electricBlock (assign (spectralLocusSheet cfg a d x y))
      = spectralElectricScale cfg • (!![-a, -x; -x, -d] : Mat) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [electricBlock, spectralLocusSheet_eq, assign,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsplit : (!![-a, -x; -x, -d] : Mat)
      = (-(a + d) / 2) • (1 : Mat)
        + !![-(a - d) / 2, -x; -x, -(-(a - d) / 2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sub_eq_add_neg] <;> ring
  rw [hblk, opNorm_smul, hsplit, opNorm_scalar_tracelessSymm2]
  have hE' : |spectralElectricScale cfg| = spectralElectricScale cfg := abs_of_nonneg hE
  rw [hE']
  have habs : |-(a + d) / 2| = |(a + d) / 2| := by
    rw [show -(a + d) / 2 = -((a + d) / 2) by ring, abs_neg]
  have hsq : (-(a - d) / 2)^2 = ((a - d) / 2)^2 := by ring
  rw [habs, hsq]
  ring

theorem opNorm_magneticBlock_locus (cfg : Config) (a d : ℝ) (x y : ℝ) :
    opNorm (magneticBlock (assign (spectralLocusSheet cfg a d x y)))
      = spectralMagneticScale cfg
        * (Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2|) := by
  have hM : 0 ≤ spectralMagneticScale cfg := by
    have h1 := cfg.omega_pos
    have h2 := cfg.upper.eta_pos
    have h3 := cfg.vac.mu0_pos
    unfold spectralMagneticScale
    positivity
  have hblk : magneticBlock (assign (spectralLocusSheet cfg a d x y))
      = spectralMagneticScale cfg • (!![-d, x; x, -a] : Mat) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [magneticBlock, spectralLocusSheet_eq, assign,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsplit : (!![-d, x; x, -a] : Mat)
      = (-(a + d) / 2) • (1 : Mat)
        + !![(a - d) / 2, x; x, -((a - d) / 2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sub_eq_add_neg] <;> ring
  rw [hblk, opNorm_smul, hsplit, opNorm_scalar_tracelessSymm2]
  have hM' : |spectralMagneticScale cfg| = spectralMagneticScale cfg := abs_of_nonneg hM
  rw [hM']
  have habs : |-(a + d) / 2| = |(a + d) / 2| := by
    rw [show -(a + d) / 2 = -((a + d) / 2) by ring, abs_neg]
  rw [habs]
  ring

theorem opNorm_couplingBlock_locus (cfg : Config) (a d : ℝ) (x y : ℝ) :
    opNorm (couplingBlock (assign (spectralLocusSheet cfg a d x y)))
      = spectralChiralScale cfg * |y| := by
  have hC : 0 ≤ spectralChiralScale cfg := by
    have h1 := cfg.omega_pos
    have h2 := cfg.vac.c0_pos
    unfold spectralChiralScale
    positivity
  have hblk : couplingBlock (assign (spectralLocusSheet cfg a d x y))
      = spectralChiralScale cfg • (!![y, 0; 0, y] : Mat) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [couplingBlock, spectralLocusSheet_eq, assign,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hblk, opNorm_smul, opNorm_diagonal2, max_self]
  have hC' : |spectralChiralScale cfg| = spectralChiralScale cfg := abs_of_nonneg hC
  rw [hC']

theorem spectralLocus_directCost (cfg : Config) (a d : ℝ) (x y : ℝ) :
    spectralDirectCost (assign (spectralLocusSheet cfg a d x y))
      = max (spectralElectricScale cfg) (spectralMagneticScale cfg)
        * (Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2|) := by
  have hE : 0 ≤ spectralElectricScale cfg := by
    have h1 := cfg.omega_pos
    have h2 := cfg.upper.eta_pos
    have h3 := cfg.vac.eps0_pos
    unfold spectralElectricScale
    positivity
  have hM : 0 ≤ spectralMagneticScale cfg := by
    have h1 := cfg.omega_pos
    have h2 := cfg.upper.eta_pos
    have h3 := cfg.vac.mu0_pos
    unfold spectralMagneticScale
    positivity
  rw [spectralDirectCost, opNorm_electricBlock_locus, opNorm_magneticBlock_locus]
  have hs : 0 ≤ Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2| := by positivity
  have hmax : max (spectralElectricScale cfg * (Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2|))
      (spectralMagneticScale cfg * (Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2|))
      = max (spectralElectricScale cfg) (spectralMagneticScale cfg)
        * (Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2|) := by
    by_cases h : spectralElectricScale cfg ≤ spectralMagneticScale cfg
    · have h1 : spectralElectricScale cfg
          * (Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2|)
          ≤ spectralMagneticScale cfg
          * (Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2|) :=
        mul_le_mul_of_nonneg_right h hs
      rw [max_eq_right h1, max_eq_right h]
    · have h2 : spectralMagneticScale cfg
          * (Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2|)
          ≤ spectralElectricScale cfg
          * (Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2|) :=
        mul_le_mul_of_nonneg_right (le_of_not_ge h) hs
      rw [max_eq_left h2, max_eq_left (le_of_not_ge h)]
  rw [hmax]

theorem spectralLocus_couplingCost (cfg : Config) (a d : ℝ) (x y : ℝ) :
    spectralCouplingCost (assign (spectralLocusSheet cfg a d x y))
      = spectralChiralScale cfg * |y| := by
  rw [spectralCouplingCost, opNorm_couplingBlock_locus]

theorem spectralLocusBudget_eq (cfg : Config) (a d : ℝ) (x y : ℝ) :
    spectralTotalBudget cfg (assign (spectralLocusSheet cfg a d x y))
      = freeSpaceK0 cfg * max
          (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
            * (Real.sqrt (((a - d) / 2)^2 + x^2) + |(a + d) / 2|))
          (spectralChiralScale cfg * |y|) := by
  rw [spectralTotalBudget_eq]
  unfold spectralCost
  rw [spectralLocus_directCost, spectralLocus_couplingCost]

structure PhaseCoefficients where

  q_c : ℝ

  a_x : ℝ

  a_y : ℝ

  a_z : ℝ

  q_s : ℝ

  b_x : ℝ

  b_y : ℝ

  b_z : ℝ

@[expose] noncomputable def phaseQ (c : PhaseCoefficients) (t : ℝ) : ℝ :=
  c.q_c * Real.cos t + c.q_s * Real.sin t

@[expose] noncomputable def phaseRx (c : PhaseCoefficients) (t : ℝ) : ℝ :=
  c.a_x * Real.cos t + c.b_x * Real.sin t

@[expose] noncomputable def phaseRy (c : PhaseCoefficients) (t : ℝ) : ℝ :=
  c.a_y * Real.cos t + c.b_y * Real.sin t

@[expose] noncomputable def phaseRz (c : PhaseCoefficients) (t : ℝ) : ℝ :=
  c.a_z * Real.cos t + c.b_z * Real.sin t

theorem phaseUnit (c : PhaseCoefficients)
    (h₁ : c.q_c^2 + c.a_x^2 + c.a_y^2 + c.a_z^2 = 1)
    (h₂ : c.q_s^2 + c.b_x^2 + c.b_y^2 + c.b_z^2 = 1)
    (h₃ : c.q_c * c.q_s + c.a_x * c.b_x + c.a_y * c.b_y + c.a_z * c.b_z = 0)
    (t : ℝ) :
    phaseQ c t ^ 2 + phaseRx c t ^ 2 + phaseRy c t ^ 2 + phaseRz c t ^ 2 = 1 := by
  have hcos : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
  unfold phaseQ phaseRx phaseRy phaseRz
  calc _ = (c.q_c^2 + c.a_x^2 + c.a_y^2 + c.a_z^2) * Real.cos t ^ 2
      + (c.q_s^2 + c.b_x^2 + c.b_y^2 + c.b_z^2) * Real.sin t ^ 2
      + 2 * (c.q_c * c.q_s + c.a_x * c.b_x + c.a_y * c.b_y + c.a_z * c.b_z)
        * Real.cos t * Real.sin t := by ring
    _ = _ := by rw [h₁, h₂, h₃]; ring_nf; nlinarith [hcos]

@[expose] noncomputable def phaseMatrix (c : PhaseCoefficients) (t : ℝ) : Ten2 :=
  !![phaseQ c t + Complex.I * phaseRz c t, phaseRy c t + Complex.I * phaseRx c t;
    -phaseRy c t + Complex.I * phaseRx c t, phaseQ c t - Complex.I * phaseRz c t]

@[expose] noncomputable def phaseTransmission (c : PhaseCoefficients) (t α : ℝ) : Ten2 :=
  (Complex.exp (Complex.I * α)) • phaseMatrix c t

theorem phaseTransmission_eq (c : PhaseCoefficients) (t α : ℝ) :
    phaseTransmission c t α
      = ((Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ)) • phaseMatrix c t := by
  have hexp : Complex.exp (Complex.I * α)
      = (Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im]
      rw [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring_nf
      simp
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im,
        Complex.ofReal_re]
      rw [Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring_nf
      simp
  rw [phaseTransmission, hexp]

@[expose] noncomputable def phaseCayleyBlock (c : PhaseCoefficients) (t α : ℝ) : Ten2 :=
  let d : ℝ := Real.cos α + phaseQ c t
  !![((2 * (Real.sin α + phaseRz c t) / d : ℝ) : ℂ),
     (2 * phaseRx c t / d : ℝ) - Complex.I * (2 * phaseRy c t / d : ℝ);
    (2 * phaseRx c t / d : ℝ) + Complex.I * (2 * phaseRy c t / d : ℝ),
    ((2 * (Real.sin α - phaseRz c t) / d : ℝ) : ℂ)]

@[expose] noncomputable def phaseCayleyScale (c : PhaseCoefficients) (t α : ℝ) : ℝ :=
  Real.cos α + phaseQ c t

@[expose] noncomputable def phaseSheet (cfg : Config) (c : PhaseCoefficients)
    (t α : ℝ) : BIParams :=
  spectralLocusSheet cfg
    (2 * (Real.sin α + phaseRz c t) / phaseCayleyScale c t α)
    (2 * (Real.sin α - phaseRz c t) / phaseCayleyScale c t α)
    (2 * phaseRx c t / phaseCayleyScale c t α)
    (2 * phaseRy c t / phaseCayleyScale c t α)

@[expose] noncomputable def phaseMinimum (cfg : Config) (c : PhaseCoefficients)
    (t : ℝ) : ℝ :=
  freeSpaceK0 cfg * 2 *
    max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
          * Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2))
        (spectralChiralScale cfg * |phaseRy c t|) / (1 + |phaseQ c t|)

theorem phaseSheetBudget (cfg : Config) (c : PhaseCoefficients) (t α : ℝ)
    (hα : phaseCayleyScale c t α ≠ 0) :
    spectralTotalBudget cfg (assign (phaseSheet cfg c t α))
      = freeSpaceK0 cfg * 2 / |phaseCayleyScale c t α| *
        max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
              * (Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) + |Real.sin α|))
            (spectralChiralScale cfg * |phaseRy c t|) := by
  have hE : 0 ≤ spectralElectricScale cfg := by
    have h1 := cfg.omega_pos
    have h2 := cfg.upper.eta_pos
    have h3 := cfg.vac.eps0_pos
    unfold spectralElectricScale
    positivity
  have hM : 0 ≤ spectralMagneticScale cfg := by
    have h1 := cfg.omega_pos
    have h2 := cfg.upper.eta_pos
    have h3 := cfg.vac.mu0_pos
    unfold spectralMagneticScale
    positivity
  have hC : 0 ≤ spectralChiralScale cfg := by
    have h1 := cfg.omega_pos
    have h2 := cfg.vac.c0_pos
    unfold spectralChiralScale
    positivity
  have hk0 : 0 ≤ freeSpaceK0 cfg := by
    have h1 := cfg.omega_pos
    have h2 := cfg.vac.c0_pos
    unfold freeSpaceK0
    positivity
  have hD : 0 < |phaseCayleyScale c t α| := abs_pos.mpr hα
  have hd' : Real.cos α + phaseQ c t ≠ 0 := by
    simpa [phaseCayleyScale] using hα
  have hhalf : ((2 * (Real.sin α + phaseRz c t) / phaseCayleyScale c t α
      - 2 * (Real.sin α - phaseRz c t) / phaseCayleyScale c t α) / 2)
      = 2 * phaseRz c t / phaseCayleyScale c t α := by
    field_simp [hd']
    ring
  have hsum : ((2 * (Real.sin α + phaseRz c t) / phaseCayleyScale c t α
      + 2 * (Real.sin α - phaseRz c t) / phaseCayleyScale c t α) / 2)
      = 2 * Real.sin α / phaseCayleyScale c t α := by
    field_simp [hd']
    ring
  have hsquares : ((2 * phaseRz c t / phaseCayleyScale c t α) ^ 2
      + (2 * phaseRx c t / phaseCayleyScale c t α) ^ 2)
      = (2 / |phaseCayleyScale c t α|) ^ 2
        * (phaseRx c t ^ 2 + phaseRz c t ^ 2) := by
    field_simp [hd']
    rw [sq_abs]
    ring
  have hsq : Real.sqrt (((2 * (Real.sin α + phaseRz c t) / phaseCayleyScale c t α
      - 2 * (Real.sin α - phaseRz c t) / phaseCayleyScale c t α) / 2) ^ 2
      + (2 * phaseRx c t / phaseCayleyScale c t α) ^ 2)
      = (2 / |phaseCayleyScale c t α|)
        * Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) := by
    rw [hhalf, hsquares]
    rw [Real.sqrt_mul
      (show (0 : ℝ) ≤ (2 / |phaseCayleyScale c t α|) ^ 2 from by positivity)
      (phaseRx c t ^ 2 + phaseRz c t ^ 2)]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_pos (show (0 : ℝ) < 2 / |phaseCayleyScale c t α| from by positivity)]
  have habs : |2 * phaseRy c t / phaseCayleyScale c t α|
      = 2 * |phaseRy c t| / |phaseCayleyScale c t α| := by
    rw [abs_div, abs_mul, abs_two]
  have hfac : |2 * Real.sin α / phaseCayleyScale c t α|
      = 2 * |Real.sin α| / |phaseCayleyScale c t α| := by
    rw [abs_div, abs_mul, abs_two]
  rw [phaseSheet, spectralLocusBudget_eq, hsq, hsum, habs, hfac]
  have hk : 0 ≤ 2 / |phaseCayleyScale c t α| := by
    positivity
  have hA : max (spectralElectricScale cfg) (spectralMagneticScale cfg)
      * ((2 / |phaseCayleyScale c t α|)
          * Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2)
        + 2 * |Real.sin α| / |phaseCayleyScale c t α|)
      = (2 / |phaseCayleyScale c t α|)
        * (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
          * (Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) + |Real.sin α|)) := by ring
  have hB : spectralChiralScale cfg
      * (2 * |phaseRy c t| / |phaseCayleyScale c t α|)
      = (2 / |phaseCayleyScale c t α|)
        * (spectralChiralScale cfg * |phaseRy c t|) := by ring
  have hmax : max ((2 / |phaseCayleyScale c t α|)
        * (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
          * (Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) + |Real.sin α|)))
      ((2 / |phaseCayleyScale c t α|) * (spectralChiralScale cfg * |phaseRy c t|))
      = (2 / |phaseCayleyScale c t α|)
        * max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
          * (Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) + |Real.sin α|))
          (spectralChiralScale cfg * |phaseRy c t|) := by
    apply le_antisymm
    · refine max_le ?_ ?_
      · exact mul_le_mul_of_nonneg_left (le_max_left _ _) hk
      · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hk
    · by_cases h :
          max (spectralElectricScale cfg) (spectralMagneticScale cfg)
            * (Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) + |Real.sin α|)
          ≤ spectralChiralScale cfg * |phaseRy c t|
      · rw [max_eq_right h]
        exact le_max_right _ _
      · rw [max_comm, max_eq_right (le_of_not_ge h)]
        exact le_max_left _ _
  rw [hA, hB, hmax]
  ring

end GSTC.Scattering
