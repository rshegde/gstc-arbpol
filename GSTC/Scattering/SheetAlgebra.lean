/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Efficiency

public section

open scoped Matrix
open scoped ComplexConjugate

namespace GSTC.Scattering

theorem smul_smul_matrix (a b : ℂ) (M : Ten2) : a • (b • M) = (a * b) • M := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem mulVec_two (M : Ten2) (v : Vec2) (i : Fin 2) :
    (M *ᵥ v) i = M i 0 * v 0 + M i 1 * v 1 := by
  rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]

theorem waveY_normal_mulVec (m : Medium) (e : Vec2) :
    waveY m 0 *ᵥ e = (1 / (m.eta : ℂ)) • e := by
  rw [waveY_normal, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem jumpH_normal_E (cfg : Config) (s : Side) (eI eR eT : Vec2) (hk : cfg.kPar = 0) :
    ncross *ᵥ (jumpH cfg s eI eR eT)
      = (1 / ((Wave.medium cfg s .incident).eta : ℂ)) • (eI - eR)
        - (1 / ((Wave.medium cfg s .transmitted).eta : ℂ)) • eT := by
  rw [ncross_jumpH cfg s eI eR eT, waveYsign_incident, waveYsign_reflected,
    waveYsign_transmitted, waveY_reflected_eq_incident cfg s, hk,
    waveY_normal_mulVec, waveY_normal_mulVec, waveY_normal_mulVec]
  ext i
  fin_cases i <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem jumpH_normal_E_identical (cfg : Config) (s : Side) (eI eR eT : Vec2)
    (hk : cfg.kPar = 0) (hmed : identicalMedia cfg s) :
    ncross *ᵥ (jumpH cfg s eI eR eT)
      = (1 / ((Wave.medium cfg s .incident).eta : ℂ)) • (eI - eR - eT) := by
  rw [jumpH_normal_E cfg s eI eR eT hk]
  have hη : ((Wave.medium cfg s .incident).eta : ℂ)
      = ((Wave.medium cfg s .transmitted).eta : ℂ) := by
    exact_mod_cast hmed
  rw [hη]
  ext i
  fin_cases i <;>
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem jonesInner_smul_right (u : Vec2) (α : ℂ) (v : Vec2) :
    jonesInner u (α • v) = α * jonesInner u v := by
  simp only [jonesInner, Pi.smul_apply, smul_eq_mul]
  ring

theorem jonesInner_smul_left (α : ℂ) (u v : Vec2) :
    jonesInner (α • u) v = star α * jonesInner u v := by
  simp only [jonesInner, Pi.smul_apply, smul_eq_mul, star_mul]
  ring

theorem jonesInner_eq_star_hc (u v : Vec2) : jonesInner u v = star (hc u v) := by
  simp only [jonesInner, hc_expand, star_add, star_mul, star_star]
  ring

theorem jonesNormSqR_eq_hc (e : Vec2) : jonesNormSqR e = (hc e e).re := by
  unfold jonesNormSqR jonesNormSq
  rw [jonesInner_eq_star_hc, Complex.star_def, Complex.conj_re]

theorem hc_antiHermitian (X : Ten2) (hanti : ∀ i j, X i j = -star (X j i))
    (u v : Vec2) : hc (X *ᵥ u) v = -hc u (X *ᵥ v) := by
  rw [hc_mulVec', hc_mulVec]
  have e00 : star (X 0 0) = -(X 0 0) := by
    have h := congrArg star (hanti (0 : Fin 2) (0 : Fin 2))
    simpa using h
  have e01 : star (X 0 1) = -(X 1 0) := by
    have h := congrArg star (hanti (0 : Fin 2) (1 : Fin 2))
    simpa using h
  have e10 : star (X 1 0) = -(X 0 1) := by
    have h := congrArg star (hanti (1 : Fin 2) (0 : Fin 2))
    simpa using h
  have e11 : star (X 1 1) = -(X 1 1) := by
    have h := congrArg star (hanti (1 : Fin 2) (1 : Fin 2))
    simpa using h
  simp only [e00, e01, e10, e11]
  ring

theorem hc_add_antiHermitian (X : Ten2) (hanti : ∀ i j, X i j = -star (X j i))
    (w : Vec2) :
    hc (w + X *ᵥ w) (w + X *ᵥ w) = hc w w + hc (X *ᵥ w) (X *ᵥ w) := by
  have hadd : hc (w + X *ᵥ w) (w + X *ᵥ w)
      = (hc w w + hc w (X *ᵥ w)) + (hc (X *ᵥ w) w + hc (X *ᵥ w) (X *ᵥ w)) := by
    rw [hc_add_left, hc_add_right, hc_add_right]
  rw [hadd, hc_antiHermitian X hanti w w]
  ring

theorem jonesNormSqR_add_antiHermitian (X : Ten2) (hanti : ∀ i j, X i j = -star (X j i))
    (w : Vec2) :
    jonesNormSqR (w + X *ᵥ w) = jonesNormSqR w + jonesNormSqR (X *ᵥ w) := by
  rw [jonesNormSqR_eq_hc, jonesNormSqR_eq_hc, jonesNormSqR_eq_hc]
  rw [hc_add_antiHermitian X hanti w, Complex.add_re]

theorem add_antiHermitian_injective (X : Ten2) (hanti : ∀ i j, X i j = -star (X j i))
    {w w' : Vec2} (h : w + X *ᵥ w = w' + X *ᵥ w') : w = w' := by

  have hd : (w - w') + X *ᵥ (w - w') = 0 := by
    have hsub : X *ᵥ (w - w') = X *ᵥ w - X *ᵥ w' := Matrix.mulVec_sub _ _ _
    rw [hsub]
    funext i
    have hi := congrArg (fun z : Vec2 => z i) h
    simp only [Pi.add_apply] at hi
    calc (w - w') i + ((X *ᵥ w) - (X *ᵥ w')) i
        = (w i + (X *ᵥ w) i) - (w' i + (X *ᵥ w') i) := by
          simp only [Pi.sub_apply]
          ring
      _ = 0 := by rw [hi]; ring

  have hid := jonesNormSqR_add_antiHermitian X hanti (w - w')
  rw [hd] at hid
  have hid' : 0 = jonesNormSqR (w - w') + jonesNormSqR (X *ᵥ (w - w')) := by
    simpa [jonesNormSqR_eq] using hid
  have hn0 := jonesNormSqR_nonneg (w - w')
  have hn1 := jonesNormSqR_nonneg (X *ᵥ (w - w'))
  have hz : jonesNormSqR (w - w') = 0 := by linarith
  have hzero : w - w' = 0 := (jonesNormSqR_eq_zero_iff (w - w')).mp hz
  exact sub_eq_zero.mp hzero

end GSTC.Scattering
