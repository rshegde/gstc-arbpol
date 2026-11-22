/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.SheetAlgebra

public section

namespace GSTC.Scattering

open scoped Matrix
open scoped ComplexConjugate

theorem electricOnly_sheetVPar (cfg : Config) (s : Side)
    (sus : Susceptibilities) (eI eR eT : Vec2) (hk : cfg.kPar = 0)
    (hem : chiTT sus.em = 0) :
    sheetVPar cfg s sus eI eR eT
      = ((1 / 2) * (cfg.vac.eps0 : ℂ)) • ((chiTT sus.ee) *ᵥ (eI + eR + eT)) := by
  unfold sheetVPar
  have h1 : couplingVPar cfg s sus .incident
      = ((1 / 2) * (cfg.vac.eps0 : ℂ)) • (chiTT sus.ee) := by
    rw [couplingVPar_eq_normal cfg s sus .incident hk]
    unfold couplingVParNormal
    rw [hem, Matrix.zero_mul, smul_zero, smul_zero, add_zero]
    exact smul_smul_matrix _ _ _
  have h2 : couplingVPar cfg s sus .reflected
      = ((1 / 2) * (cfg.vac.eps0 : ℂ)) • (chiTT sus.ee) := by
    rw [couplingVPar_eq_normal cfg s sus .reflected hk]
    unfold couplingVParNormal
    rw [hem, Matrix.zero_mul, smul_zero, smul_zero, add_zero]
    exact smul_smul_matrix _ _ _
  have h3 : couplingVPar cfg s sus .transmitted
      = ((1 / 2) * (cfg.vac.eps0 : ℂ)) • (chiTT sus.ee) := by
    rw [couplingVPar_eq_normal cfg s sus .transmitted hk]
    unfold couplingVParNormal
    rw [hem, Matrix.zero_mul, smul_zero, smul_zero, add_zero]
    exact smul_smul_matrix _ _ _
  rw [h1, h2, h3]
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  rw [← smul_add, ← smul_add]
  rw [Matrix.mulVec_add, Matrix.mulVec_add]

@[expose] noncomputable def eoResponseScale (cfg : Config) (eta : ℝ) : ℂ :=
  Complex.I * (cfg.omega : ℂ) * (((cfg.vac.eps0 : ℂ) * ((eta : ℝ) : ℂ)) / 2)

theorem eoResponseScale_star (cfg : Config) (eta : ℝ) :
    star (eoResponseScale cfg eta) = -(eoResponseScale cfg eta) := by
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
  rw [eoResponseScale, star_mul, hdiv, star_mul, hsR, hsR, star_mul, hsR, hsI]
  ring

theorem eoResponseScale_ne_zero (cfg : Config) (eta : ℝ) (heta : (eta : ℂ) ≠ 0) :
    eoResponseScale cfg eta ≠ 0 := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hω : (cfg.omega : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt cfg.omega_pos
  have heps : (cfg.vac.eps0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt cfg.vac.eps0_pos
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  unfold eoResponseScale
  refine mul_ne_zero (mul_ne_zero hI hω) ?_
  rw [div_eq_mul_inv]
  exact mul_ne_zero (mul_ne_zero heps heta) (inv_ne_zero h2)

end GSTC.Scattering
