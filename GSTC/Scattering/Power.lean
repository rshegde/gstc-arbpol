/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Losslessness
public import GSTC.Scattering.NormalIncidence

public section

open scoped Matrix

namespace GSTC.Scattering

@[expose] def conjV (v : Vec2) : Vec2 := fun i => star (v i)

@[expose] def det2 (u v : Vec2) : ℂ := u 0 * v 1 - u 1 * v 0

@[expose] def fluxC (e h : Vec2) : ℂ := det2 e (conjV h)

@[expose] noncomputable def fluxZ (e h : Vec2) : ℝ := (fluxC e h).re / 2

@[expose] noncomputable def wavePower (m : Medium) (kPar : ℝ) (e : Vec2) : ℝ :=
  (1 / 2) * (Complex.normSq (e 0) / zTM m kPar + Complex.normSq (e 1) / zTE m kPar)

@[expose] def hc (u v : Vec2) : ℂ := dot2 u (conjV v)

theorem conjV_add (u v : Vec2) : conjV (u + v) = conjV u + conjV v := by
  funext i
  simp [conjV, star_add]

theorem conjV_smul (c : ℂ) (u : Vec2) : conjV (c • u) = star c • conjV u := by
  funext i
  simp [conjV, star_mul]
  ring

theorem det2_add_left (u v w : Vec2) :
    det2 (u + v) w = det2 u w + det2 v w := by
  simp [det2]
  ring

theorem det2_smul_left (c : ℂ) (u v : Vec2) :
    det2 (c • u) v = c * det2 u v := by
  simp [det2]
  ring

theorem det2_ncross (u v : Vec2) : det2 u (ncross *ᵥ v) = dot2 u v := by
  rw [ncross_apply]
  simp [det2, dot2]

theorem det2_ncross' (u v : Vec2) : det2 (ncross *ᵥ u) v = -dot2 u v := by
  rw [ncross_apply]
  simp [det2, dot2]
  ring

theorem det2_add_right (u v w : Vec2) :
    det2 u (v + w) = det2 u v + det2 u w := by
  simp [det2]
  ring

theorem det2_smul_right (c : ℂ) (u v : Vec2) :
    det2 u (c • v) = c * det2 u v := by
  simp [det2, Pi.smul_apply, smul_eq_mul]
  ring

theorem star_re (z : ℂ) : (star z).re = z.re := by
  rw [Complex.star_def]
  exact Complex.conj_re z

theorem star_im (z : ℂ) : (star z).im = -z.im := by
  rw [Complex.star_def]
  exact Complex.conj_im z

theorem star_ofReal (r : ℝ) : star (r : ℂ) = r := by
  rw [Complex.star_def, Complex.conj_ofReal]

theorem hc_expand (u v : Vec2) :
    hc u v = u 0 * star (v 0) + u 1 * star (v 1) := by
  simp [hc, dot2, conjV]

theorem hc_swap (u v : Vec2) : hc v u = star (hc u v) := by
  rw [hc_expand, hc_expand]
  simp only [star_add, star_mul, star_star]

theorem hc_self_re (u : Vec2) :
    (hc u u).re = Complex.normSq (u 0) + Complex.normSq (u 1) := by
  rw [hc_expand]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]

theorem hc_mulVec (u : Vec2) (A : Ten2) (v : Vec2) :
    hc u (A *ᵥ v)
      = u 0 * star (A 0 0) * star (v 0) + u 0 * star (A 0 1) * star (v 1)
        + u 1 * star (A 1 0) * star (v 0) + u 1 * star (A 1 1) * star (v 1) := by
  simp only [hc, dot2, conjV, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two,
    star_add, star_mul]
  ring

theorem hc_mulVec' (A : Ten2) (u v : Vec2) :
    hc (A *ᵥ u) v
      = A 0 0 * u 0 * star (v 0) + A 0 1 * u 1 * star (v 0)
        + A 1 0 * u 0 * star (v 1) + A 1 1 * u 1 * star (v 1) := by
  simp only [hc, dot2, conjV, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  ring

theorem hc_hermitian (A : Ten2) (hA : ∀ i j, A i j = star (A j i))
    (u v : Vec2) : hc u (A *ᵥ v) = hc (A *ᵥ u) v := by
  rw [hc_mulVec, hc_mulVec']
  have e00 : star (A 0 0) = A 0 0 := (hA 0 0).symm
  have e01 : star (A 0 1) = A 1 0 := (hA 1 0).symm
  have e10 : star (A 1 0) = A 0 1 := (hA 0 1).symm
  have e11 : star (A 1 1) = A 1 1 := (hA 1 1).symm
  simp only [e00, e01, e10, e11]
  ring

theorem hc_cross (B C : Ten2) (hBC : ∀ i j, B i j = star (C j i))
    (u v : Vec2) : hc u (B *ᵥ v) = hc (C *ᵥ u) v := by
  rw [hc_mulVec, hc_mulVec']
  have e00 : star (B 0 0) = C 0 0 := by rw [hBC, star_star]
  have e01 : star (B 0 1) = C 1 0 := by rw [hBC, star_star]
  have e10 : star (B 1 0) = C 0 1 := by rw [hBC, star_star]
  have e11 : star (B 1 1) = C 1 1 := by rw [hBC, star_star]
  simp only [e00, e01, e10, e11]
  ring

theorem cFactor_normal (m : Medium) : cFactor m 0 = 1 := by
  simp [cFactor]

theorem zTM_normal (m : Medium) : zTM m 0 = m.eta := by
  rw [zTM, cFactor_normal]
  ring

theorem zTE_normal (m : Medium) : zTE m 0 = m.eta := by
  rw [zTE, cFactor_normal]
  ring

theorem wavePower_normal (m : Medium) (e : Vec2) :
    wavePower m 0 e = (Complex.normSq (e 0) + Complex.normSq (e 1)) / (2 * m.eta) := by
  rw [wavePower, zTM_normal, zTE_normal]
  ring

theorem waveY_normal_matrix (m : Medium) :
    waveY m 0 = !![(1 : ℂ) / (m.eta : ℂ), 0; 0, (1 : ℂ) / (m.eta : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [waveY, zTM_normal, zTE_normal, Matrix.of_apply,
      Matrix.cons_val', Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one]

theorem ncross_waveY_normal (m : Medium) :
    ncross * waveY m 0 = ((1 : ℂ) / (m.eta : ℂ)) • ncross := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [waveY_normal_matrix, Matrix.mul_apply, Fin.sum_univ_two, ncross,
      Matrix.of_apply, Matrix.cons_val', Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.smul_apply]
  all_goals ring

@[expose] noncomputable def waveYfacC (s : Side) (w : Wave) (m : Medium) : ℂ :=
  ((PropDir.sign (Wave.dir s w) / m.eta : ℝ) : ℂ)

theorem star_waveYfacC (s : Side) (w : Wave) (m : Medium) :
    star (waveYfacC s w m) = waveYfacC s w m := by
  unfold waveYfacC
  exact star_ofReal _

theorem hPar_normal (cfg : Config) (s : Side) (w : Wave) (e : Vec2)
    (hk : cfg.kPar = 0) :
    hPar cfg s w e = waveYfacC s w (Wave.medium cfg s w) • (ncross *ᵥ e) := by
  rw [hPar, hk, ncross_waveY_normal, Matrix.smul_mulVec, smul_smul]
  congr 1
  unfold waveYfacC
  rw [Complex.ofReal_div]
  congr 1
  field_simp

theorem sign_reflected_neg (s : Side) :
    PropDir.sign (Wave.dir s .reflected) = -PropDir.sign (Wave.dir s .incident) := by
  cases s <;> simp only [PropDir.sign, Wave.dir]; ring

theorem sign_transmitted_eq (s : Side) :
    PropDir.sign (Wave.dir s .transmitted) = PropDir.sign (Wave.dir s .incident) := by
  cases s <;> rfl

theorem medium_reflected_eq (cfg : Config) (s : Side) :
    Wave.medium cfg s .reflected = Wave.medium cfg s .incident := by
  cases s <;> rfl

theorem fluxC_add_left (u v w : Vec2) : fluxC (u + v) w = fluxC u w + fluxC v w := by
  unfold fluxC
  rw [det2_add_left]

theorem fluxC_add_right (u v w : Vec2) : fluxC u (v + w) = fluxC u v + fluxC u w := by
  unfold fluxC
  rw [conjV_add, det2_add_right]

theorem fluxC_smul_right (c : ℂ) (u v : Vec2) : fluxC u (c • v) = star c • fluxC u v := by
  unfold fluxC
  rw [conjV_smul, det2_smul_right]
  simp only [smul_eq_mul]

theorem hc_add_right (u v w : Vec2) : hc u (v + w) = hc u v + hc u w := by
  rw [hc_expand, hc_expand, hc_expand]
  simp only [Pi.add_apply, star_add]
  ring

theorem hc_smul_right (c : ℂ) (u v : Vec2) : hc u (c • v) = star c • hc u v := by
  rw [hc_expand, hc_expand]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul]
  ring

theorem re_hc_swap (u v : Vec2) : (hc u v).re = (hc v u).re := by
  rw [hc_swap, star_re]

theorem conjV_ncross_mulVec (v : Vec2) : conjV (ncross *ᵥ v) = ncross *ᵥ (conjV v) := by
  rw [ncross_apply, ncross_apply]
  funext i
  fin_cases i
  · simp [conjV]
  · simp [conjV]

theorem fluxC_ncross_mulVec (u v : Vec2) : fluxC u (ncross *ᵥ v) = hc u v := by
  unfold fluxC
  rw [conjV_ncross_mulVec, det2_ncross]
  rfl

theorem fluxC_ncross_mulVec' (u v : Vec2) : fluxC (ncross *ᵥ u) v = -(hc u v) := by
  unfold fluxC
  rw [det2_ncross']
  rfl

theorem fluxC_smul_left (c : ℂ) (u v : Vec2) : fluxC (c • u) v = c * fluxC u v := by
  unfold fluxC
  rw [det2_smul_left]

theorem fluxC_neg_right (u v : Vec2) : fluxC u (-v) = -fluxC u v := by
  rw [show (-v) = (-1 : ℂ) • v by simp, fluxC_smul_right]
  simp

theorem fluxZ_wave (cfg : Config) (s : Side) (w : Wave) (e : Vec2)
    (hk : cfg.kPar = 0) :
    fluxZ e (hPar cfg s w e)
      = PropDir.sign (Wave.dir s w) * wavePower (Wave.medium cfg s w) 0 e := by
  have hη : (Wave.medium cfg s w).eta ≠ 0 := (Wave.medium cfg s w).eta_pos.ne'
  unfold fluxZ
  rw [hPar_normal cfg s w e hk, fluxC_smul_right, fluxC_ncross_mulVec, star_waveYfacC]
  rw [show waveYfacC s w (Wave.medium cfg s w) • (hc e e)
      = ((PropDir.sign (Wave.dir s w) / (Wave.medium cfg s w).eta : ℝ) : ℂ) * (hc e e) by
        simp [waveYfacC, smul_eq_mul]]
  rw [Complex.re_ofReal_mul, hc_self_re, wavePower_normal]
  ring

@[expose] noncomputable def eMid (eI eR eT : Vec2) : Vec2 :=
  (1 / 2 : ℂ) • (eI + eR + eT)

@[expose] noncomputable def hMid (cfg : Config) (s : Side) (eI eR eT : Vec2) : Vec2 :=
  (1 / 2 : ℂ) • (hPar cfg s .incident eI + hPar cfg s .reflected eR
    + hPar cfg s .transmitted eT)

theorem eMid_total (eI eR eT : Vec2) :
    eI + eR = eMid eI eR eT + (1 / 2 : ℂ) • (eI + eR - eT) := by
  funext i
  fin_cases i <;>
    simp only [eMid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem eMid_transmitted (eI eR eT : Vec2) :
    eT = eMid eI eR eT - (1 / 2 : ℂ) • (eI + eR - eT) := by
  funext i
  fin_cases i <;>
    simp only [eMid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem hMid_total (cfg : Config) (s : Side) (eI eR eT : Vec2) :
    hPar cfg s .incident eI + hPar cfg s .reflected eR
      = hMid cfg s eI eR eT
        + (1 / 2 : ℂ) • (hPar cfg s .incident eI + hPar cfg s .reflected eR
            - hPar cfg s .transmitted eT) := by
  funext i
  fin_cases i <;>
    simp only [hMid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem hMid_transmitted (cfg : Config) (s : Side) (eI eR eT : Vec2) :
    hPar cfg s .transmitted eT
      = hMid cfg s eI eR eT
        - (1 / 2 : ℂ) • (hPar cfg s .incident eI + hPar cfg s .reflected eR
            - hPar cfg s .transmitted eT) := by
  funext i
  fin_cases i <;>
    simp only [hMid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem three_regroup (a b c : ℂ) (x1 x2 x3 y1 y2 y3 : Vec2) :
    a • (b • x1 + c • y1) + a • (b • x2 + c • y2) + a • (b • x3 + c • y3)
      = a • (b • (x1 + x2 + x3) + c • (y1 + y2 + y3)) := by
  simp only [smul_add]
  ac_rfl

theorem waveYfacC_smul (s : Side) (w : Wave) (m : Medium) (v : Vec2) :
    (PropDir.sign (Wave.dir s w) : ℂ) • (((1 : ℂ) / (m.eta : ℂ)) • v)
      = waveYfacC s w m • v := by
  rw [smul_smul]
  have hscalar : (PropDir.sign (Wave.dir s w) : ℂ) * ((1 : ℂ) / (m.eta : ℂ))
      = ((PropDir.sign (Wave.dir s w) / m.eta : ℝ) : ℂ) := by
    rw [Complex.ofReal_div]
    ring
  unfold waveYfacC
  rw [hscalar]

theorem couplingVParNormal_mulVec (cfg : Config) (s : Side) (sus : Susceptibilities)
    (w : Wave) (e : Vec2) :
    couplingVParNormal cfg s sus w *ᵥ e
      = (1 / 2 : ℂ) • ((cfg.vac.eps0 : ℂ) • (chiTT sus.ee *ᵥ e)
          + (1 / (cfg.vac.c0 : ℂ)) • (waveYfacC s w (Wave.medium cfg s w)
              • (chiTT sus.em *ᵥ (ncross *ᵥ e)))) := by
  unfold couplingVParNormal
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, ncross_waveY_normal, Matrix.mul_smul, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec,
    waveYfacC_smul s w (Wave.medium cfg s w) (chiTT sus.em *ᵥ (ncross *ᵥ e))]

theorem couplingWParNormal_mulVec (cfg : Config) (s : Side) (sus : Susceptibilities)
    (w : Wave) (e : Vec2) :
    couplingWParNormal cfg s sus w *ᵥ e
      = (1 / 2 : ℂ) • ((1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.me *ᵥ e)
          + (cfg.vac.mu0 : ℂ) • (waveYfacC s w (Wave.medium cfg s w)
              • (chiTT sus.mm *ᵥ (ncross *ᵥ e)))) := by
  unfold couplingWParNormal
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, ncross_waveY_normal, Matrix.mul_smul, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec,
    waveYfacC_smul s w (Wave.medium cfg s w) (chiTT sus.mm *ᵥ (ncross *ᵥ e))]

theorem couplingVParNormal_mulVec_h (cfg : Config) (s : Side) (sus : Susceptibilities)
    (w : Wave) (e : Vec2) (hk : cfg.kPar = 0) :
    couplingVParNormal cfg s sus w *ᵥ e
      = (1 / 2 : ℂ) • ((cfg.vac.eps0 : ℂ) • (chiTT sus.ee *ᵥ e)
          + (1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.em *ᵥ (hPar cfg s w e))) := by
  rw [couplingVParNormal_mulVec, hPar_normal cfg s w e hk]
  rw [Matrix.mulVec_smul]

theorem couplingWParNormal_mulVec_h (cfg : Config) (s : Side) (sus : Susceptibilities)
    (w : Wave) (e : Vec2) (hk : cfg.kPar = 0) :
    couplingWParNormal cfg s sus w *ᵥ e
      = (1 / 2 : ℂ) • ((1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.me *ᵥ e)
          + (cfg.vac.mu0 : ℂ) • (chiTT sus.mm *ᵥ (hPar cfg s w e))) := by
  rw [couplingWParNormal_mulVec, hPar_normal cfg s w e hk]
  rw [Matrix.mulVec_smul]

theorem half_smul_add (a b : ℂ) (u v : Vec2) :
    (1 / 2 : ℂ) • (a • u + b • v) = a • ((1 / 2 : ℂ) • u) + b • ((1 / 2 : ℂ) • v) := by
  funext i
  fin_cases i <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem sheetVPar_mid (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) :
    sheetVPar cfg s sus eI eR eT
      = (cfg.vac.eps0 : ℂ) • (chiTT sus.ee *ᵥ eMid eI eR eT)
        + (1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.em *ᵥ hMid cfg s eI eR eT) := by
  unfold sheetVPar
  rw [couplingVPar_eq_normal cfg s sus .incident hk,
    couplingVPar_eq_normal cfg s sus .reflected hk,
    couplingVPar_eq_normal cfg s sus .transmitted hk,
    couplingVParNormal_mulVec_h cfg s sus .incident eI hk,
    couplingVParNormal_mulVec_h cfg s sus .reflected eR hk,
    couplingVParNormal_mulVec_h cfg s sus .transmitted eT hk]
  rw [three_regroup]
  rw [← Matrix.mulVec_add, ← Matrix.mulVec_add, ← Matrix.mulVec_add, ← Matrix.mulVec_add]
  unfold eMid hMid
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
  exact half_smul_add (cfg.vac.eps0 : ℂ) (1 / (cfg.vac.c0 : ℂ))
    (chiTT sus.ee *ᵥ (eI + eR + eT))
    (chiTT sus.em *ᵥ (hPar cfg s .incident eI + hPar cfg s .reflected eR
      + hPar cfg s .transmitted eT))

theorem sheetMPar_mid (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) :
    sheetMPar cfg s sus eI eR eT
      = (1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.me *ᵥ eMid eI eR eT)
        + (cfg.vac.mu0 : ℂ) • (chiTT sus.mm *ᵥ hMid cfg s eI eR eT) := by
  unfold sheetMPar
  rw [couplingWPar_eq_normal cfg s sus .incident hk,
    couplingWPar_eq_normal cfg s sus .reflected hk,
    couplingWPar_eq_normal cfg s sus .transmitted hk,
    couplingWParNormal_mulVec_h cfg s sus .incident eI hk,
    couplingWParNormal_mulVec_h cfg s sus .reflected eR hk,
    couplingWParNormal_mulVec_h cfg s sus .transmitted eT hk]
  rw [three_regroup]
  rw [← Matrix.mulVec_add, ← Matrix.mulVec_add, ← Matrix.mulVec_add, ← Matrix.mulVec_add]
  unfold eMid hMid
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
  exact half_smul_add (1 / (cfg.vac.c0 : ℂ)) (cfg.vac.mu0 : ℂ)
    (chiTT sus.me *ᵥ (eI + eR + eT))
    (chiTT sus.mm *ᵥ (hPar cfg s .incident eI + hPar cfg s .reflected eR
      + hPar cfg s .transmitted eT))

theorem jumpSign_sq (s : Side) : (Side.jumpSign s) * (Side.jumpSign s) = 1 := by
  cases s <;> simp [Side.jumpSign]

theorem star_jumpSign (s : Side) : star (Side.jumpSign s) = Side.jumpSign s := by
  cases s <;> simp [Side.jumpSign]

theorem jumpSign_im (s : Side) : (Side.jumpSign s).im = 0 := by
  cases s <;> simp [Side.jumpSign]

theorem star_half : star (1 / 2 : ℂ) = 1 / 2 := by
  rw [Complex.star_def]
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]

@[expose] def eJumpRaw (eI eR eT : Vec2) : Vec2 := eI + eR - eT

@[expose] noncomputable def hJumpRaw (cfg : Config) (s : Side) (eI eR eT : Vec2) : Vec2 :=
  hPar cfg s .incident eI + hPar cfg s .reflected eR - hPar cfg s .transmitted eT

theorem jumpE_eq (s : Side) (eI eR eT : Vec2) :
    jumpE s eI eR eT = Side.jumpSign s • eJumpRaw eI eR eT := rfl

theorem jumpH_eq (cfg : Config) (s : Side) (eI eR eT : Vec2) :
    jumpH cfg s eI eR eT = Side.jumpSign s • hJumpRaw cfg s eI eR eT := rfl

theorem fluxC_neg_left (u v : Vec2) : fluxC (-u) v = -(fluxC u v) := by
  rw [show (-u) = (-1 : ℂ) • u by simp, fluxC_smul_left]
  simp

theorem fluxC_sub_left (u v w : Vec2) : fluxC (u - v) w = fluxC u w - fluxC v w := by
  have h : u - v = u + (-v) := by abel
  rw [h, fluxC_add_left, fluxC_neg_left]
  abel

theorem fluxC_sub_right (u v w : Vec2) : fluxC u (v - w) = fluxC u v - fluxC u w := by
  have h : v - w = v + (-w) := by abel
  rw [h, fluxC_add_right, fluxC_neg_right]
  abel

theorem fluxC_half_left (u w : Vec2) :
    fluxC ((1 / 2 : ℂ) • u) w = (1 / 2 : ℂ) * fluxC u w :=
  fluxC_smul_left (1 / 2) u w

theorem fluxC_half_right (u w : Vec2) :
    fluxC u ((1 / 2 : ℂ) • w) = (1 / 2 : ℂ) * fluxC u w := by
  rw [fluxC_smul_right, star_half, smul_eq_mul]

theorem fluxC_mid_split (e h de dh : Vec2) :
    fluxC (e - (1 / 2 : ℂ) • de) (h - (1 / 2 : ℂ) • dh)
      - fluxC (e + (1 / 2 : ℂ) • de) (h + (1 / 2 : ℂ) • dh)
    = -(fluxC e dh + fluxC de h) := by
  simp only [fluxC_add_right, fluxC_add_left, fluxC_sub_right, fluxC_sub_left,
    fluxC_half_right, fluxC_half_left]
  ring

theorem ncross_mulVec_ncross (v : Vec2) : ncross *ᵥ (ncross *ᵥ v) = -v := by
  rw [ncross_apply, ncross_apply]
  funext i
  fin_cases i <;> simp

theorem star_omega (cfg : Config) :
    star (Complex.I * (cfg.omega : ℂ)) = -(Complex.I * (cfg.omega : ℂ)) := by
  rw [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

@[expose] noncomputable def powerTerm (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) : ℂ :=
  hc (eMid eI eR eT) (sheetVPar cfg s sus eI eR eT)
    - hc (sheetMPar cfg s sus eI eR eT) (hMid cfg s eI eR eT)

theorem hJumpRaw_gstc (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2)
    (hH : ncross *ᵥ (jumpH cfg s eI eR eT)
      = (Complex.I * (cfg.omega : ℂ)) • (sheetVPar cfg s sus eI eR eT)) :
    hJumpRaw cfg s eI eR eT
      = -(Side.jumpSign s) • (ncross *ᵥ ((Complex.I * (cfg.omega : ℂ))
          • (sheetVPar cfg s sus eI eR eT))) := by
  have h1 : ncross *ᵥ (hJumpRaw cfg s eI eR eT)
      = Side.jumpSign s • ((Complex.I * (cfg.omega : ℂ))
          • (sheetVPar cfg s sus eI eR eT)) := by
    calc ncross *ᵥ (hJumpRaw cfg s eI eR eT)
        = Side.jumpSign s • (Side.jumpSign s
            • (ncross *ᵥ (hJumpRaw cfg s eI eR eT))) := by
          rw [smul_smul, jumpSign_sq, one_smul]
      _ = Side.jumpSign s
          • (ncross *ᵥ (Side.jumpSign s • (hJumpRaw cfg s eI eR eT))) := by
          rw [Matrix.mulVec_smul]
      _ = Side.jumpSign s • (ncross *ᵥ (jumpH cfg s eI eR eT)) := by
          rw [jumpH_eq]
      _ = Side.jumpSign s • ((Complex.I * (cfg.omega : ℂ))
          • (sheetVPar cfg s sus eI eR eT)) := by
          rw [hH]
  calc hJumpRaw cfg s eI eR eT
      = -(ncross *ᵥ (ncross *ᵥ (hJumpRaw cfg s eI eR eT))) := by
        rw [ncross_mulVec_ncross]
        simp
    _ = -(ncross *ᵥ (Side.jumpSign s • ((Complex.I * (cfg.omega : ℂ))
        • (sheetVPar cfg s sus eI eR eT)))) := by
        rw [h1]
    _ = -(Side.jumpSign s) • (ncross *ᵥ ((Complex.I * (cfg.omega : ℂ))
        • (sheetVPar cfg s sus eI eR eT))) := by
        rw [Matrix.mulVec_smul, neg_smul]

theorem eJumpRaw_gstc (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2)
    (hE : jumpE s eI eR eT
      = (Complex.I * (cfg.omega : ℂ)) • (ncross *ᵥ (sheetMPar cfg s sus eI eR eT))) :
    eJumpRaw eI eR eT
      = Side.jumpSign s • ((Complex.I * (cfg.omega : ℂ))
          • (ncross *ᵥ (sheetMPar cfg s sus eI eR eT))) := by
  calc eJumpRaw eI eR eT
      = Side.jumpSign s • (Side.jumpSign s • eJumpRaw eI eR eT) := by
        rw [smul_smul, jumpSign_sq, one_smul]
    _ = Side.jumpSign s • (jumpE s eI eR eT) := by
        rw [jumpE_eq]
    _ = Side.jumpSign s • ((Complex.I * (cfg.omega : ℂ))
          • (ncross *ᵥ (sheetMPar cfg s sus eI eR eT))) := by
        rw [hE]

theorem hc_smul_left (c : ℂ) (u v : Vec2) : hc (c • u) v = c • hc u v := by
  rw [hc_expand, hc_expand]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem fluxC_mid_split_of (e h de dh et ht etot htot : Vec2)
    (h1 : et = e - (1 / 2 : ℂ) • de)
    (h2 : etot = e + (1 / 2 : ℂ) • de)
    (h3 : ht = h - (1 / 2 : ℂ) • dh)
    (h4 : htot = h + (1 / 2 : ℂ) • dh) :
    fluxC et ht - fluxC etot htot = -(fluxC e dh + fluxC de h) := by
  rw [h1, h2, h3, h4]
  exact fluxC_mid_split e h de dh

theorem fluxC_eMid_hJump (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2)
    (hH : ncross *ᵥ (jumpH cfg s eI eR eT)
      = (Complex.I * (cfg.omega : ℂ)) • (sheetVPar cfg s sus eI eR eT)) :
    fluxC (eMid eI eR eT) (hJumpRaw cfg s eI eR eT)
      = Side.jumpSign s • ((Complex.I * (cfg.omega : ℂ))
          • (hc (eMid eI eR eT) (sheetVPar cfg s sus eI eR eT))) := by
  rw [hJumpRaw_gstc cfg s sus eI eR eT hH, fluxC_smul_right,
    fluxC_ncross_mulVec, hc_smul_right, star_neg, star_jumpSign, star_omega]
  simp only [smul_eq_mul]
  ring

theorem fluxC_eJump_hMid (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2)
    (hE : jumpE s eI eR eT
      = (Complex.I * (cfg.omega : ℂ)) • (ncross *ᵥ (sheetMPar cfg s sus eI eR eT))) :
    fluxC (eJumpRaw eI eR eT) (hMid cfg s eI eR eT)
      = -(Side.jumpSign s) • ((Complex.I * (cfg.omega : ℂ))
          • (hc (sheetMPar cfg s sus eI eR eT) (hMid cfg s eI eR eT))) := by
  rw [eJumpRaw_gstc cfg s sus eI eR eT hE, fluxC_smul_left, fluxC_smul_left,
    fluxC_ncross_mulVec']
  simp only [smul_eq_mul]
  ring

theorem fluxC_gstc (cfg : Config) (s : Side) (sus : Susceptibilities) (eI eR eT : Vec2)
    (hE : jumpE s eI eR eT
      = (Complex.I * (cfg.omega : ℂ)) • (ncross *ᵥ (sheetMPar cfg s sus eI eR eT)))
    (hH : ncross *ᵥ (jumpH cfg s eI eR eT)
      = (Complex.I * (cfg.omega : ℂ)) • (sheetVPar cfg s sus eI eR eT)) :
    fluxC eT (hPar cfg s .transmitted eT)
        - fluxC (eI + eR) (hPar cfg s .incident eI + hPar cfg s .reflected eR)
      = -(Side.jumpSign s) • ((Complex.I * (cfg.omega : ℂ))
          • powerTerm cfg s sus eI eR eT) := by
  calc fluxC eT (hPar cfg s .transmitted eT)
        - fluxC (eI + eR) (hPar cfg s .incident eI + hPar cfg s .reflected eR)
      = -(fluxC (eMid eI eR eT) (hJumpRaw cfg s eI eR eT)
          + fluxC (eJumpRaw eI eR eT) (hMid cfg s eI eR eT)) :=
        fluxC_mid_split_of (eMid eI eR eT) (hMid cfg s eI eR eT)
          (eJumpRaw eI eR eT) (hJumpRaw cfg s eI eR eT)
          eT (hPar cfg s .transmitted eT) (eI + eR)
          (hPar cfg s .incident eI + hPar cfg s .reflected eR)
          (eMid_transmitted eI eR eT) (eMid_total eI eR eT)
          (hMid_transmitted cfg s eI eR eT) (hMid_total cfg s eI eR eT)
    _ = -(Side.jumpSign s) • ((Complex.I * (cfg.omega : ℂ))
          • powerTerm cfg s sus eI eR eT) := by
        rw [fluxC_eMid_hJump cfg s sus eI eR eT hH,
          fluxC_eJump_hMid cfg s sus eI eR eT hE]
        unfold powerTerm
        simp only [smul_eq_mul]
        ring

theorem star_inv_ofReal (r : ℝ) : star (1 / (r : ℂ)) = 1 / (r : ℂ) := by
  have h : (1 / (r : ℂ)) = (1 : ℂ) * (r : ℂ)⁻¹ := by rfl
  rw [h, Complex.star_def, map_mul, map_inv₀, map_one, Complex.conj_ofReal]

theorem hc_add_left (u v w : Vec2) : hc (u + v) w = hc u w + hc v w := by
  rw [hc_expand, hc_expand, hc_expand]
  simp only [Pi.add_apply]
  ring

theorem star_hc_hermitian (A : Ten2) (hA : ∀ i j, A i j = star (A j i))
    (u : Vec2) : star (hc u (A *ᵥ u)) = hc u (A *ᵥ u) := by
  rw [← hc_swap u (A *ᵥ u)]
  exact (hc_hermitian A hA u u).symm

theorem powerTerm_mid (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) :
    powerTerm cfg s sus eI eR eT
      = (cfg.vac.eps0 : ℂ) • hc (eMid eI eR eT) (chiTT sus.ee *ᵥ eMid eI eR eT)
        + (1 / (cfg.vac.c0 : ℂ))
            • hc (eMid eI eR eT) (chiTT sus.em *ᵥ hMid cfg s eI eR eT)
        - (1 / (cfg.vac.c0 : ℂ))
            • hc (chiTT sus.me *ᵥ eMid eI eR eT) (hMid cfg s eI eR eT)
        - (cfg.vac.mu0 : ℂ)
            • hc (chiTT sus.mm *ᵥ hMid cfg s eI eR eT) (hMid cfg s eI eR eT) := by
  rw [powerTerm, sheetVPar_mid cfg s sus eI eR eT hk,
    sheetMPar_mid cfg s sus eI eR eT hk]
  simp only [hc_add_right, hc_smul_right, hc_add_left, hc_smul_left,
    star_ofReal, star_inv_ofReal]
  ring

theorem powerTerm_star (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) (hloss : sus.Lossless) :
    star (powerTerm cfg s sus eI eR eT) = powerTerm cfg s sus eI eR eT := by
  have hherm := Susceptibilities.Lossless.chiTT_hermitian sus hloss
  have hcross : hc (eMid eI eR eT) (chiTT sus.em *ᵥ hMid cfg s eI eR eT)
      = hc (chiTT sus.me *ᵥ eMid eI eR eT) (hMid cfg s eI eR eT) :=
    hc_cross (chiTT sus.em) (chiTT sus.me) hherm.2.2 (eMid eI eR eT)
      (hMid cfg s eI eR eT)
  have hcross' : star (hc (eMid eI eR eT) (chiTT sus.em *ᵥ hMid cfg s eI eR eT))
      = star (hc (chiTT sus.me *ᵥ eMid eI eR eT) (hMid cfg s eI eR eT)) :=
    congrArg star hcross
  rw [powerTerm_mid cfg s sus eI eR eT hk]
  simp only [star_sub, star_add, star_smul, star_ofReal, star_inv_ofReal]
  rw [star_hc_hermitian (chiTT sus.ee) hherm.1 (eMid eI eR eT)]
  rw [← hc_hermitian (chiTT sus.mm) hherm.2.1 (hMid cfg s eI eR eT)
    (hMid cfg s eI eR eT)]
  rw [star_hc_hermitian (chiTT sus.mm) hherm.2.1 (hMid cfg s eI eR eT)]
  rw [hcross']
  rw [hcross]
  ring

theorem powerTerm_im (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) (hloss : sus.Lossless) :
    (powerTerm cfg s sus eI eR eT).im = 0 := by
  have h := powerTerm_star cfg s sus eI eR eT hk hloss
  have h' : (star (powerTerm cfg s sus eI eR eT)).im
      = (powerTerm cfg s sus eI eR eT).im := congrArg Complex.im h
  have h2 := star_im (powerTerm cfg s sus eI eR eT)
  linarith

theorem I_omega_re (cfg : Config) : (Complex.I * (cfg.omega : ℂ)).re = 0 := by
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
  ring

theorem re_mul_real_imag_real (a b c : ℂ) (ha : a.im = 0) (hb : b.re = 0) (hc : c.im = 0) :
    (a * b * c).re = 0 := by
  rw [Complex.mul_re, Complex.mul_re, Complex.mul_im]
  rw [ha, hb, hc]
  ring

theorem fluxC_gstc_re (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hgstc : gstcSatisfied cfg s sus eI eR eT) :
    (fluxC eT (hPar cfg s .transmitted eT)
      - fluxC (eI + eR) (hPar cfg s .incident eI + hPar cfg s .reflected eR)).re = 0 := by
  have hg := (gstc_normal cfg s sus eI eR eT hk).mp hgstc
  rw [fluxC_gstc cfg s sus eI eR eT hg.1 hg.2]
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  refine re_mul_real_imag_real _ _ _ ?_ (I_omega_re cfg)
    (powerTerm_im cfg s sus eI eR eT hk hloss)
  rw [Complex.neg_im, jumpSign_im]
  ring

theorem fluxZ_gstc (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hgstc : gstcSatisfied cfg s sus eI eR eT) :
    fluxZ eT (hPar cfg s .transmitted eT)
      = fluxZ (eI + eR) (hPar cfg s .incident eI + hPar cfg s .reflected eR) := by
  have h := fluxC_gstc_re cfg s sus eI eR eT hk hloss hgstc
  unfold fluxZ
  rw [Complex.sub_re] at h
  linarith

theorem fluxZ_add_left (u v w : Vec2) : fluxZ (u + v) w = fluxZ u w + fluxZ v w := by
  unfold fluxZ
  rw [fluxC_add_left, Complex.add_re]
  ring

theorem fluxZ_add_right (u v w : Vec2) : fluxZ u (v + w) = fluxZ u v + fluxZ u w := by
  unfold fluxZ
  rw [fluxC_add_right, Complex.add_re]
  ring

theorem fluxZ_wave_mixed (cfg : Config) (s : Side) (w : Wave) (e f : Vec2)
    (hk : cfg.kPar = 0) :
    fluxZ e (hPar cfg s w f)
      = (PropDir.sign (Wave.dir s w) / (Wave.medium cfg s w).eta)
        * (hc e f).re / 2 := by
  have hη : (Wave.medium cfg s w).eta ≠ 0 := (Wave.medium cfg s w).eta_pos.ne'
  unfold fluxZ
  rw [hPar_normal cfg s w f hk, fluxC_smul_right, fluxC_ncross_mulVec, star_waveYfacC]
  rw [show waveYfacC s w (Wave.medium cfg s w) • (hc e f)
      = ((PropDir.sign (Wave.dir s w) / (Wave.medium cfg s w).eta : ℝ) : ℂ) * (hc e f) by
        simp [waveYfacC, smul_eq_mul]]
  rw [Complex.re_ofReal_mul]

theorem fluxZ_cross_cancel (cfg : Config) (s : Side) (eI eR : Vec2) (hk : cfg.kPar = 0) :
    fluxZ eI (hPar cfg s .reflected eR) + fluxZ eR (hPar cfg s .incident eI) = 0 := by
  rw [fluxZ_wave_mixed cfg s .reflected eI eR hk, fluxZ_wave_mixed cfg s .incident eR eI hk]
  rw [re_hc_swap eR eI]
  rw [sign_reflected_neg, medium_reflected_eq]
  ring

theorem power_balance_normal (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hgstc : gstcSatisfied cfg s sus eI eR eT) :
    wavePower (Wave.medium cfg s .incident) 0 eI
      = wavePower (Wave.medium cfg s .reflected) 0 eR
        + wavePower (Wave.medium cfg s .transmitted) 0 eT := by
  have hbal := fluxZ_gstc cfg s sus eI eR eT hk hloss hgstc
  have hcross : fluxZ eI (hPar cfg s .reflected eR) + fluxZ eR (hPar cfg s .incident eI) = 0 :=
    fluxZ_cross_cancel cfg s eI eR hk
  have hI : fluxZ eI (hPar cfg s .incident eI)
      = PropDir.sign (Wave.dir s .incident) * wavePower (Wave.medium cfg s .incident) 0 eI :=
    fluxZ_wave cfg s .incident eI hk
  have hR : fluxZ eR (hPar cfg s .reflected eR)
      = PropDir.sign (Wave.dir s .reflected) * wavePower (Wave.medium cfg s .reflected) 0 eR :=
    fluxZ_wave cfg s .reflected eR hk
  have hT : fluxZ eT (hPar cfg s .transmitted eT)
      = PropDir.sign (Wave.dir s .transmitted) * wavePower (Wave.medium cfg s .transmitted) 0 eT :=
    fluxZ_wave cfg s .transmitted eT hk
  have hbal2 : fluxZ eT (hPar cfg s .transmitted eT)
      = fluxZ eI (hPar cfg s .incident eI) + fluxZ eR (hPar cfg s .reflected eR) := by
    rw [hbal]
    rw [fluxZ_add_right, fluxZ_add_left, fluxZ_add_left]
    linear_combination hcross
  rw [hT, hI, hR] at hbal2
  rw [sign_transmitted_eq, sign_reflected_neg] at hbal2
  have h3 : PropDir.sign (Wave.dir s .incident)
      * (wavePower (Wave.medium cfg s .transmitted) 0 eT
        - wavePower (Wave.medium cfg s .incident) 0 eI
        + wavePower (Wave.medium cfg s .reflected) 0 eR) = 0 := by
    linear_combination hbal2
  have hsign : PropDir.sign (Wave.dir s .incident) ≠ 0 := by
    cases s <;> simp [PropDir.sign, Wave.dir]
  have h4 : wavePower (Wave.medium cfg s .transmitted) 0 eT
      - wavePower (Wave.medium cfg s .incident) 0 eI
      + wavePower (Wave.medium cfg s .reflected) 0 eR = 0 :=
    Or.resolve_left (mul_eq_zero.mp h3) (fun h => hsign h)
  linarith

end GSTC.Scattering
