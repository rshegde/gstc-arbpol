/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.ElectricOnly

public section

open scoped Matrix
open scoped ComplexConjugate

namespace GSTC.Scattering

theorem couplingWParNormal_magneticOnly (cfg : Config) (s : Side)
    (sus : Susceptibilities) (w : Wave) (hme : chiTT sus.me = 0) :
    couplingWParNormal cfg s sus w
      = ((1 / 2 : ℂ) * ((cfg.vac.mu0 : ℂ)
          * ((PropDir.sign (Wave.dir s w) : ℂ)
              * (1 / ((Wave.medium cfg s w).eta : ℂ))))) • (chiTT sus.mm * ncross) := by
  unfold couplingWParNormal
  rw [hme, smul_zero, zero_add]
  rw [waveY_normal]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]
  simp only [smul_smul_matrix]

theorem couplingWPar_magneticOnly (cfg : Config) (s : Side)
    (sus : Susceptibilities) (w : Wave) (hk : cfg.kPar = 0)
    (hme : chiTT sus.me = 0) :
    couplingWPar cfg s sus w
      = ((1 / 2 : ℂ) * ((cfg.vac.mu0 : ℂ)
          * ((PropDir.sign (Wave.dir s w) : ℂ)
              * (1 / ((Wave.medium cfg s w).eta : ℂ))))) • (chiTT sus.mm * ncross) := by
  rw [couplingWPar_eq_normal cfg s sus w hk]
  exact couplingWParNormal_magneticOnly cfg s sus w hme

theorem magneticOnly_sheetMPar (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) (hme : chiTT sus.me = 0)
    (hmed : identicalMedia cfg s) :
    sheetMPar cfg s sus eI eR eT
      = ((1 / 2 : ℂ) * ((cfg.vac.mu0 : ℂ)
          * ((PropDir.sign (Wave.dir s .incident) : ℂ)
              * (1 / ((Wave.medium cfg s .incident).eta : ℂ)))))
        • ((chiTT sus.mm * ncross) *ᵥ (eI - eR + eT)) := by
  unfold sheetMPar
  have hI := couplingWPar_magneticOnly cfg s sus .incident hk hme
  have hR := couplingWPar_magneticOnly cfg s sus .reflected hk hme
  have hT := couplingWPar_magneticOnly cfg s sus .transmitted hk hme
  rw [hI, hR, hT]

  have hηR : ((Wave.medium cfg s .reflected).eta : ℂ)
      = ((Wave.medium cfg s .incident).eta : ℂ) := by
    rw [medium_reflected_eq]
  have hηT : ((Wave.medium cfg s .transmitted).eta : ℂ)
      = ((Wave.medium cfg s .incident).eta : ℂ) := by
    have h : (Wave.medium cfg s .transmitted).eta = (Wave.medium cfg s .incident).eta := by
      exact hmed.symm
    exact_mod_cast h
  have hσR : (PropDir.sign (Wave.dir s .reflected) : ℂ)
      = -((PropDir.sign (Wave.dir s .incident) : ℂ)) := by
    have h := sign_reflected_neg s
    exact_mod_cast h
  have hσT : (PropDir.sign (Wave.dir s .transmitted) : ℂ)
      = (PropDir.sign (Wave.dir s .incident) : ℂ) := by
    rw [sign_transmitted_eq]
  rw [hηR, hηT, hσR, hσT]

  have hsplit : (chiTT sus.mm * ncross) *ᵥ (eI - eR + eT)
      = (chiTT sus.mm * ncross) *ᵥ eI - (chiTT sus.mm * ncross) *ᵥ eR
        + (chiTT sus.mm * ncross) *ᵥ eT := by
    calc (chiTT sus.mm * ncross) *ᵥ (eI - eR + eT)
        = (chiTT sus.mm * ncross) *ᵥ (eI - eR)
            + (chiTT sus.mm * ncross) *ᵥ eT := Matrix.mulVec_add _ _ _
      _ = ((chiTT sus.mm * ncross) *ᵥ eI - (chiTT sus.mm * ncross) *ᵥ eR)
            + (chiTT sus.mm * ncross) *ᵥ eT := by rw [Matrix.mulVec_sub]
  rw [hsplit]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, mulVec_two, Matrix.smul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply]
  ring

@[expose] noncomputable def moResponseScale (cfg : Config) (eta : ℝ) : ℂ :=
  -((Complex.I * (cfg.omega : ℂ)) * (((cfg.vac.mu0 : ℂ) * (1 / ((eta : ℝ) : ℂ))) / 2))

theorem moResponseScale_star (cfg : Config) (eta : ℝ) :
    star (moResponseScale cfg eta) = -(moResponseScale cfg eta) := by
  have hsI : star Complex.I = -Complex.I := by
    rw [Complex.star_def]
    exact Complex.conj_I
  have hsR (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
    rw [Complex.star_def]
    exact Complex.conj_ofReal r
  have hs2 : star (2 : ℂ) = 2 := by
    rw [Complex.star_def]
    exact Complex.conj_natCast 2
  have hdiv (z : ℂ) : star (z / 2) = star z / 2 := by
    have hc : star ((2 : ℂ)⁻¹) = (star (2 : ℂ))⁻¹ := by
      rw [Complex.star_def, Complex.conj_inv]
    rw [div_eq_mul_inv, star_mul, hc, hs2, div_eq_mul_inv, mul_comm]
  have hinv : star (1 / ((eta : ℝ) : ℂ)) = 1 / ((eta : ℝ) : ℂ) := by
    have h1 : star ((eta : ℝ) : ℂ) = ((eta : ℝ) : ℂ) := by
      rw [Complex.star_def]
      exact Complex.conj_ofReal eta
    calc star (1 / ((eta : ℝ) : ℂ)) = star ((eta : ℝ) : ℂ)⁻¹ := by
          rw [div_eq_mul_inv, one_mul]
      _ = (star ((eta : ℝ) : ℂ))⁻¹ := star_inv₀ _
      _ = ((eta : ℝ) : ℂ)⁻¹ := by rw [h1]
      _ = 1 / ((eta : ℝ) : ℂ) := by rw [div_eq_mul_inv, one_mul]
  rw [moResponseScale, star_neg, star_mul, hdiv, star_mul, star_mul, hsR, hinv, hsR, hsI]
  ring

theorem ncross_mul_hermitian (K : Ten2) (hK : ∀ i j, K i j = star (K j i)) :
    ∀ i j, (ncross * (K * ncross)) i j = star ((ncross * (K * ncross)) j i) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, ncross, Matrix.of_apply,
      Matrix.cons_val', Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, star_add, star_mul, star_neg, star_zero, star_one] <;>
    simp only [← hK] <;>
    ring

theorem moResponseScale_ne_zero (cfg : Config) (eta : ℝ) (heta : (eta : ℂ) ≠ 0) :
    moResponseScale cfg eta ≠ 0 := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hω : (cfg.omega : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt cfg.omega_pos
  have hmu0 : (cfg.vac.mu0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt cfg.vac.mu0_pos
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hinv : (1 / ((eta : ℝ) : ℂ)) ≠ 0 := by
    rw [div_eq_mul_inv]
    simp only [one_mul]
    exact inv_ne_zero heta
  unfold moResponseScale
  refine neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hI hω) ?_)
  rw [div_eq_mul_inv]
  exact mul_ne_zero (mul_ne_zero hmu0 hinv) (inv_ne_zero h2)

end GSTC.Scattering
