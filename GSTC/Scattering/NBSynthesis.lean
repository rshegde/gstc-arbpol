/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.NBRealizability

public section
namespace GSTC.Scattering
open scoped Matrix

@[expose] noncomputable def nbSynthesizeParity (cfg : Config) (side : Side)
    (X Y : Ten2) : Susceptibilities :=
  nbParitySheet cfg (Wave.medium cfg side .incident).eta (nbInvCayley X) (nbInvCayley Y)

theorem nb_synthesis_from_parity (cfg : Config) (side : Side)
    (X Y : Ten2) (hk : cfg.kPar=0) (hmed : identicalMedia cfg side)
    (hxs : X.transpose=X) (hys : Y.transpose=Y)
    (hx : X ∈ unitary Ten2) (hy : Y ∈ unitary Ten2)
    (hpx : (1+X).det ≠ 0) (hpy : (1+Y).det ≠ 0) :
    let sus := nbSynthesizeParity cfg side X Y
    let R := (1/2 : ℂ) • (X-Y)
    let T := (1/2 : ℂ) • (X+Y)
    nbClass sus ∧ sus.Lossless ∧ sus.Reciprocal ∧
      (∀ a, gstcSatisfied cfg side sus a (R *ᵥ a) (T *ᵥ a)) ∧
      ∀ a r t, gstcSatisfied cfg side sus a r t → r=R *ᵥ a ∧ t=T *ᵥ a := by
  let E := nbInvCayley X
  let F := nbInvCayley Y
  let eta := (Wave.medium cfg side .incident).eta
  let sus := nbSynthesizeParity cfg side X Y
  let R := (1/2 : ℂ) • (X-Y)
  let T := (1/2 : ℂ) • (X+Y)
  have hES : E.transpose=E := nbInvCayley_symmetric X hxs hpx
  have hFS : F.transpose=F := nbInvCayley_symmetric Y hys hpy
  have hE : E.conjTranspose = -E := nbInvCayley_skew X hx hpx
  have hF : F.conjTranspose = -F := nbInvCayley_skew Y hy hpy
  have hc : nbClass sus := nbParitySheet_nbClass cfg eta E F
  have hl : sus.Lossless := nbParitySheet_lossless cfg eta E F hE hF
  have hr : sus.Reciprocal := nbParitySheet_reciprocal cfg eta E F hES hFS
  have hresp : eoResponseScale cfg eta • chiTT sus.ee=E ∧
      moResponseScale cfg eta • (ncross*(chiTT sus.mm*ncross))=F :=
    nbParitySheet_responses cfg eta E F (by
    exact_mod_cast (Wave.medium cfg side .incident).eta_pos.ne')
  have hce : nbCayley E=X := nbCayley_nbInvCayley X hx hpx
  have hcf : nbCayley F=Y := nbCayley_nbInvCayley Y hy hpy
  have hg : ∀ a, gstcSatisfied cfg side sus a (R *ᵥ a) (T *ᵥ a) := by
    intro a
    have hs : R+T=X := by dsimp [R,T]; module
    have hd : T-R=Y := by dsimp [R,T]; module
    apply nb_action_implies_gstc cfg side sus a (R *ᵥ a) (T *ᵥ a) hk hc.1 hc.2 hmed
    · rw [← Matrix.smul_mulVec, hresp.1]
      have he := nb_parity_action E (nbCayley E)
        (nbCayley_equation E (nb_one_add_skew_det_ne_zero E hE)) a
      rw [hce, ← hs, Matrix.add_mulVec] at he
      simpa only [sub_sub, add_assoc] using he
    · rw [← Matrix.smul_mulVec, hresp.2]
      have he := nb_parity_action F (nbCayley F)
        (nbCayley_equation F (nb_one_add_skew_det_ne_zero F hF)) a
      rw [hcf, ← hd, Matrix.sub_mulVec] at he
      simpa only [sub_eq_add_neg, add_assoc, neg_add_rev, neg_neg,
        add_comm, add_left_comm] using he
  refine ⟨hc,hl,hr,hg,?_⟩
  intro a r t hsol
  exact lossless_outgoing_unique cfg side sus a r t (R *ᵥ a) (T *ᵥ a)
    hk hl hc.1 hc.2 hmed hsol (hg a)

end GSTC.Scattering
