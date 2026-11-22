/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.NBCayley

public section
namespace GSTC.Scattering
open scoped Matrix

@[expose] def NBRealizes (cfg : Config) (s : Side) (T : Ten2) : Prop :=
  ∃ sus : Susceptibilities, nbClass sus ∧ sus.Lossless ∧ sus.Reciprocal ∧
    ∃ R : Ten2, ∀ a : Vec2, gstcSatisfied cfg s sus a (R *ᵥ a) (T *ᵥ a)

theorem nb_scaled_hermitian_skew (c : ℂ) (A : Ten2) (hc : star c = -c)
    (hA : ∀ i j, A i j = star (A j i)) :
    (c • A).conjTranspose = -(c • A) := by
  ext i j
  change star (c * A j i) = -(c * A i j)
  rw [star_mul, hc, ← hA i j]
  ring

theorem nb_scaled_skew_hermitian (c : ℂ) (A : Ten2) (hc : star c = -c)
    (hA : A.conjTranspose = -A) :
    ∀ i j, (c • A) i j = star ((c • A) j i) := by
  intro i j
  have ha := congrArg (fun M : Ten2 => M i j) hA
  change star (A j i) = -A i j at ha
  change c * A i j = star (c * A j i)
  rw [star_mul, hc, ha]
  ring

theorem nb_double_cross_skew (F : Ten2) (hF : F.conjTranspose = -F) :
    (ncross * (F * ncross)).conjTranspose = -(ncross * (F * ncross)) := by
  have hJ : ncross.conjTranspose = -ncross := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ncross, Matrix.conjTranspose_apply]
  simp only [Matrix.conjTranspose_mul, hJ, hF]
  noncomm_ring

theorem nb_reciprocal_TT_symmetric (sus : Susceptibilities) (h : sus.Reciprocal) :
    (chiTT sus.ee).transpose = chiTT sus.ee ∧
      (chiTT sus.mm).transpose = chiTT sus.mm := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.transpose_apply, chiTT]
    all_goals exact h.1 _ _
  · ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.transpose_apply, chiTT]
    all_goals exact h.2.1 _ _

theorem nb_parity_action (E U : Ten2) (h : (1 + E) * U = 1 - E) (a : Vec2) :
    a - U *ᵥ a = E *ᵥ (a + U *ᵥ a) := by
  have hh := congrArg (fun M : Ten2 => M *ᵥ a) h
  simp only [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec] at hh
  rw [Matrix.mulVec_add]
  ext i
  have hi := congrArg (fun v : Vec2 => v i) hh
  simp only [Pi.add_apply, Pi.sub_apply] at hi ⊢
  linear_combination -hi

theorem nb_parity_equation (E U : Ten2)
    (h : ∀ a : Vec2, a - U *ᵥ a = E *ᵥ (a + U *ᵥ a)) :
    (1 + E) * U = 1 - E := by
  apply Matrix.ext_iff_mulVec.mpr
  intro a
  have hh := h a
  simp only [Matrix.mulVec_add] at hh
  simp only [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec]
  ext i
  have hi := congrArg (fun v : Vec2 => v i) hh
  simp only [Pi.add_apply, Pi.sub_apply] at hi ⊢
  linear_combination -hi

@[expose] noncomputable def nbParitySheet (cfg : Config) (eta : ℝ) (E F : Ten2) :
    Susceptibilities :=
  nbSheet ((eoResponseScale cfg eta)⁻¹ • E)
    ((moResponseScale cfg eta)⁻¹ • (ncross * (F * ncross)))

theorem nbParitySheet_nbClass (cfg : Config) (eta : ℝ) (E F : Ten2) :
    nbClass (nbParitySheet cfg eta E F) := nbSheet_nbClass _ _

theorem nbParitySheet_lossless (cfg : Config) (eta : ℝ) (E F : Ten2)
    (hE : E.conjTranspose = -E) (hF : F.conjTranspose = -F) :
    (nbParitySheet cfg eta E F).Lossless := by
  apply nbSheet_lossless
  · apply nb_scaled_skew_hermitian _ E _ hE
    rw [star_inv₀, eoResponseScale_star, inv_neg]
  · apply nb_scaled_skew_hermitian _ _ _ (nb_double_cross_skew F hF)
    rw [star_inv₀, moResponseScale_star, inv_neg]

theorem nbParitySheet_reciprocal (cfg : Config) (eta : ℝ) (E F : Ten2)
    (hE : E.transpose = E) (hF : F.transpose = F) :
    (nbParitySheet cfg eta E F).Reciprocal := by
  have he : ∀ i j, E i j = E j i := by
    intro i j
    exact (congrArg (fun M : Ten2 => M i j) hE).symm
  have hf : ∀ i j, F i j = F j i := by
    intro i j
    exact (congrArg (fun M : Ten2 => M i j) hF).symm
  apply nbSheet_reciprocal
  · intro i j
    change (eoResponseScale cfg eta)⁻¹ * E i j = (eoResponseScale cfg eta)⁻¹ * E j i
    rw [he i j]
  · intro i j
    change (moResponseScale cfg eta)⁻¹ * (ncross * (F * ncross)) i j =
      (moResponseScale cfg eta)⁻¹ * (ncross * (F * ncross)) j i
    rw [ncross_mul_ncross_symmetric F hf i j]

theorem nbParitySheet_responses (cfg : Config) (eta : ℝ) (E F : Ten2)
    (heta : (eta : ℂ) ≠ 0) :
    eoResponseScale cfg eta • chiTT (nbParitySheet cfg eta E F).ee = E ∧
    moResponseScale cfg eta • (ncross * (chiTT (nbParitySheet cfg eta E F).mm * ncross)) = F := by
  have he := eoResponseScale_ne_zero cfg eta heta
  have hf := moResponseScale_ne_zero cfg eta heta
  constructor
  · rw [nbParitySheet, nbSheet_chiTT_ee, smul_smul, mul_inv_cancel₀ he, one_smul]
  · rw [nbParitySheet, nbSheet_chiTT_mm, Matrix.smul_mul, Matrix.mul_smul]
    have hJJ : ncross * ((ncross * (F * ncross)) * ncross) = F := by
      have h := ncross_mul_neg_ncross_mul F
      simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_inj] using h
    rw [hJJ, smul_smul, mul_inv_cancel₀ hf, one_smul]

theorem nb_realizes_iff_poleFreeMidpoint (cfg : Config) (s : Side)
    (T : Ten2) (hk : cfg.kPar = 0) (hmed : identicalMedia cfg s) :
    NBRealizes cfg s T ↔ PoleFreeSymmetricMidpoint T := by
  rw [poleFreeSymmetricMidpoint_iff_responses]
  constructor
  · rintro ⟨sus, hclass, hloss, hrecip, R, hG⟩
    let eta := (Wave.medium cfg s .incident).eta
    let E := eoResponseScale cfg eta • chiTT sus.ee
    let F := moResponseScale cfg eta • (ncross * (chiTT sus.mm * ncross))
    have hS := nb_reciprocal_TT_symmetric sus hrecip
    have hH := hloss.chiTT_hermitian
    have hE : E.conjTranspose = -E :=
      nb_scaled_hermitian_skew _ _ (eoResponseScale_star cfg eta) hH.1
    have hF : F.conjTranspose = -F :=
      nb_scaled_hermitian_skew _ _ (moResponseScale_star cfg eta)
        (ncross_mul_hermitian _ hH.2.1)
    have hES : E.transpose = E := by
      simp only [E, Matrix.transpose_smul, hS.1]
    have hFS : F.transpose = F := by
      ext i j
      change moResponseScale cfg eta * (ncross * (chiTT sus.mm * ncross)) j i =
        moResponseScale cfg eta * (ncross * (chiTT sus.mm * ncross)) i j
      rw [ncross_mul_ncross_symmetric _ (fun i j =>
        (congrArg (fun M : Ten2 => M i j) hS.2).symm) j i]
    have hactions := fun a => nb_action cfg s sus a (R *ᵥ a) (T *ᵥ a)
      hk hclass.1 hclass.2 hmed (hG a)
    have hp : (1 + E) * (R + T) = 1 - E := by
      apply nb_parity_equation
      intro a
      have h := (hactions a).1
      simpa only [E, eta, Matrix.smul_mulVec, Matrix.add_mulVec, sub_sub, add_assoc] using h
    have hm : (1 + F) * (T - R) = 1 - F := by
      apply nb_parity_equation
      intro a
      have h := (hactions a).2
      simp only [Matrix.sub_mulVec]
      simpa only [F, eta, Matrix.smul_mulVec, sub_sub, sub_eq_add_neg,
        add_assoc, neg_add_rev, neg_neg, add_comm, add_left_comm] using h
    have hRp : R + T = nbCayley E := by
      apply nb_mul_cancel_left (1 + E) _ _ (nb_one_add_skew_det_ne_zero E hE)
      rw [hp, nbCayley_equation _ (nb_one_add_skew_det_ne_zero E hE)]
    have hRm : T - R = nbCayley F := by
      apply nb_mul_cancel_left (1 + F) _ _ (nb_one_add_skew_det_ne_zero F hF)
      rw [hm, nbCayley_equation _ (nb_one_add_skew_det_ne_zero F hF)]
    refine ⟨E, F, hES, hFS, hE, hF, ?_⟩
    rw [← hRp, ← hRm]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  · rintro ⟨E, F, hES, hFS, hE, hF, hT⟩
    let eta := (Wave.medium cfg s .incident).eta
    let sus := nbParitySheet cfg eta E F
    let R := (1 / 2 : ℂ) • (nbCayley E - nbCayley F)
    have hc := nbParitySheet_nbClass cfg eta E F
    have hr := nbParitySheet_responses cfg eta E F (by
      exact_mod_cast (Wave.medium cfg s .incident).eta_pos.ne')
    refine ⟨sus, hc, nbParitySheet_lossless cfg eta E F hE hF,
      nbParitySheet_reciprocal cfg eta E F hES hFS, R, ?_⟩
    intro a
    have hs : R + T = nbCayley E := by
      rw [hT]
      ext i j
      simp only [R, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    have hd : T - R = nbCayley F := by
      rw [hT]
      ext i j
      simp only [R, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    apply nb_action_implies_gstc cfg s sus a (R *ᵥ a) (T *ᵥ a) hk hc.1 hc.2 hmed
    · rw [← Matrix.smul_mulVec, hr.1]
      have h := nb_parity_action E (nbCayley E)
        (nbCayley_equation E (nb_one_add_skew_det_ne_zero E hE)) a
      rw [← hs, Matrix.add_mulVec] at h
      simpa only [sub_sub, add_assoc] using h
    · rw [← Matrix.smul_mulVec, hr.2]
      have h := nb_parity_action F (nbCayley F)
        (nbCayley_equation F (nb_one_add_skew_det_ne_zero F hF)) a
      rw [← hd, Matrix.sub_mulVec] at h
      simpa only [sub_eq_add_neg, add_assoc, neg_add_rev, neg_neg,
        add_comm, add_left_comm] using h

end GSTC.Scattering
