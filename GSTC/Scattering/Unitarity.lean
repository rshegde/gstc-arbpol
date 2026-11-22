/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Admittance
public import GSTC.Scattering.BIParameterization
public import GSTC.Scattering.ScatteringMatrix

public section

open scoped Matrix

namespace GSTC.Scattering

@[expose] def eAbove (a1 b1 : Vec2) : Vec2 := a1 + b1

@[expose] def eBelow (a2 b2 : Vec2) : Vec2 := a2 + b2

@[expose] noncomputable def hAbove (cfg : Config) (a1 b1 : Vec2) : Vec2 :=
  hPar cfg .above .incident a1 + hPar cfg .above .reflected b1

@[expose] noncomputable def hBelow (cfg : Config) (a2 b2 : Vec2) : Vec2 :=
  hPar cfg .below .incident a2 + hPar cfg .below .reflected b2

@[expose] noncomputable def eMid4 (a1 b1 a2 b2 : Vec2) : Vec2 :=
  (1 / 2 : ℂ) • (a1 + b1 + a2 + b2)

@[expose] noncomputable def hMid4 (cfg : Config) (a1 b1 a2 b2 : Vec2) : Vec2 :=
  (1 / 2 : ℂ) • (hPar cfg .above .incident a1 + hPar cfg .above .reflected b1
    + hPar cfg .below .incident a2 + hPar cfg .below .reflected b2)

@[expose] def eJump4 (a1 b1 a2 b2 : Vec2) : Vec2 := eAbove a1 b1 - eBelow a2 b2

@[expose] noncomputable def hJump4 (cfg : Config) (a1 b1 a2 b2 : Vec2) : Vec2 :=
  hAbove cfg a1 b1 - hBelow cfg a2 b2

theorem eBelow_mid (a1 b1 a2 b2 : Vec2) :
    eBelow a2 b2 = eMid4 a1 b1 a2 b2 - (1 / 2 : ℂ) • (eJump4 a1 b1 a2 b2) := by
  funext i
  fin_cases i <;>
    simp only [eBelow, eMid4, eJump4, eAbove, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem eAbove_mid (a1 b1 a2 b2 : Vec2) :
    eAbove a1 b1 = eMid4 a1 b1 a2 b2 + (1 / 2 : ℂ) • (eJump4 a1 b1 a2 b2) := by
  funext i
  fin_cases i <;>
    simp only [eAbove, eMid4, eJump4, eBelow, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem hBelow_mid (cfg : Config) (a1 b1 a2 b2 : Vec2) :
    hBelow cfg a2 b2 = hMid4 cfg a1 b1 a2 b2
      - (1 / 2 : ℂ) • (hJump4 cfg a1 b1 a2 b2) := by
  funext i
  fin_cases i <;>
    simp only [hBelow, hMid4, hJump4, hAbove, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem hAbove_mid (cfg : Config) (a1 b1 a2 b2 : Vec2) :
    hAbove cfg a1 b1 = hMid4 cfg a1 b1 a2 b2
      + (1 / 2 : ℂ) • (hJump4 cfg a1 b1 a2 b2) := by
  funext i
  fin_cases i <;>
    simp only [hAbove, hMid4, hJump4, hBelow, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] <;>
    ring

@[expose] noncomputable def sheetVPar4 (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) : Vec2 :=
  couplingVPar cfg .above sus .incident *ᵥ a1 + couplingVPar cfg .above sus .reflected *ᵥ b1
    + couplingVPar cfg .below sus .incident *ᵥ a2 + couplingVPar cfg .below sus .reflected *ᵥ b2

@[expose] noncomputable def sheetMPar4 (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) : Vec2 :=
  couplingWPar cfg .above sus .incident *ᵥ a1 + couplingWPar cfg .above sus .reflected *ᵥ b1
    + couplingWPar cfg .below sus .incident *ᵥ a2 + couplingWPar cfg .below sus .reflected *ᵥ b2

theorem four_regroup (a b c : ℂ) (x1 x2 x3 x4 : Vec2) (y1 y2 y3 y4 : Vec2) :
    a • (b • x1 + c • y1) + a • (b • x2 + c • y2)
        + a • (b • x3 + c • y3) + a • (b • x4 + c • y4)
      = a • (b • (x1 + x2 + x3 + x4) + c • (y1 + y2 + y3 + y4)) := by
  simp only [smul_add]
  ac_rfl

theorem mulVec4 (M : Ten2) (v1 v2 v3 v4 : Vec2) :
    M *ᵥ (v1 + v2 + v3 + v4) = M *ᵥ v1 + M *ᵥ v2 + M *ᵥ v3 + M *ᵥ v4 := by
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add]

theorem sheetVPar4_mid (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) (hk : cfg.kPar = 0) :
    sheetVPar4 cfg sus a1 b1 a2 b2
      = (cfg.vac.eps0 : ℂ) • (chiTT sus.ee *ᵥ eMid4 a1 b1 a2 b2)
        + (1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.em *ᵥ hMid4 cfg a1 b1 a2 b2) := by
  unfold sheetVPar4
  calc sheetVPar4 cfg sus a1 b1 a2 b2
      = (1 / 2 : ℂ) • ((cfg.vac.eps0 : ℂ)
            • (chiTT sus.ee *ᵥ a1 + chiTT sus.ee *ᵥ b1
                + chiTT sus.ee *ᵥ a2 + chiTT sus.ee *ᵥ b2)
          + (1 / (cfg.vac.c0 : ℂ))
            • (chiTT sus.em *ᵥ (hPar cfg .above .incident a1)
                + chiTT sus.em *ᵥ (hPar cfg .above .reflected b1)
                + chiTT sus.em *ᵥ (hPar cfg .below .incident a2)
                + chiTT sus.em *ᵥ (hPar cfg .below .reflected b2))) := by
        unfold sheetVPar4
        rw [couplingVPar_eq_normal cfg .above sus .incident hk,
          couplingVPar_eq_normal cfg .above sus .reflected hk,
          couplingVPar_eq_normal cfg .below sus .incident hk,
          couplingVPar_eq_normal cfg .below sus .reflected hk]
        rw [couplingVParNormal_mulVec_h cfg .above sus .incident a1 hk,
          couplingVParNormal_mulVec_h cfg .above sus .reflected b1 hk,
          couplingVParNormal_mulVec_h cfg .below sus .incident a2 hk,
          couplingVParNormal_mulVec_h cfg .below sus .reflected b2 hk]
        exact four_regroup (1 / 2 : ℂ) (cfg.vac.eps0 : ℂ) (1 / (cfg.vac.c0 : ℂ))
          (chiTT sus.ee *ᵥ a1) (chiTT sus.ee *ᵥ b1) (chiTT sus.ee *ᵥ a2)
          (chiTT sus.ee *ᵥ b2)
          (chiTT sus.em *ᵥ (hPar cfg .above .incident a1))
          (chiTT sus.em *ᵥ (hPar cfg .above .reflected b1))
          (chiTT sus.em *ᵥ (hPar cfg .below .incident a2))
          (chiTT sus.em *ᵥ (hPar cfg .below .reflected b2))
    _ = (1 / 2 : ℂ) • ((cfg.vac.eps0 : ℂ) • (chiTT sus.ee *ᵥ (a1 + b1 + a2 + b2))
          + (1 / (cfg.vac.c0 : ℂ))
            • (chiTT sus.em *ᵥ (hPar cfg .above .incident a1
                + hPar cfg .above .reflected b1 + hPar cfg .below .incident a2
                + hPar cfg .below .reflected b2))) := by
        rw [← mulVec4 (chiTT sus.ee) a1 b1 a2 b2,
          ← mulVec4 (chiTT sus.em) (hPar cfg .above .incident a1)
            (hPar cfg .above .reflected b1) (hPar cfg .below .incident a2)
            (hPar cfg .below .reflected b2)]
    _ = (cfg.vac.eps0 : ℂ) • (chiTT sus.ee *ᵥ eMid4 a1 b1 a2 b2)
        + (1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.em *ᵥ hMid4 cfg a1 b1 a2 b2) := by
        unfold eMid4 hMid4
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← half_smul_add]

theorem sheetMPar4_mid (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) (hk : cfg.kPar = 0) :
    sheetMPar4 cfg sus a1 b1 a2 b2
      = (1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.me *ᵥ eMid4 a1 b1 a2 b2)
        + (cfg.vac.mu0 : ℂ) • (chiTT sus.mm *ᵥ hMid4 cfg a1 b1 a2 b2) := by
  calc sheetMPar4 cfg sus a1 b1 a2 b2
      = (1 / 2 : ℂ) • ((1 / (cfg.vac.c0 : ℂ))
            • (chiTT sus.me *ᵥ a1 + chiTT sus.me *ᵥ b1
                + chiTT sus.me *ᵥ a2 + chiTT sus.me *ᵥ b2)
          + (cfg.vac.mu0 : ℂ)
            • (chiTT sus.mm *ᵥ (hPar cfg .above .incident a1)
                + chiTT sus.mm *ᵥ (hPar cfg .above .reflected b1)
                + chiTT sus.mm *ᵥ (hPar cfg .below .incident a2)
                + chiTT sus.mm *ᵥ (hPar cfg .below .reflected b2))) := by
        unfold sheetMPar4
        rw [couplingWPar_eq_normal cfg .above sus .incident hk,
          couplingWPar_eq_normal cfg .above sus .reflected hk,
          couplingWPar_eq_normal cfg .below sus .incident hk,
          couplingWPar_eq_normal cfg .below sus .reflected hk]
        rw [couplingWParNormal_mulVec_h cfg .above sus .incident a1 hk,
          couplingWParNormal_mulVec_h cfg .above sus .reflected b1 hk,
          couplingWParNormal_mulVec_h cfg .below sus .incident a2 hk,
          couplingWParNormal_mulVec_h cfg .below sus .reflected b2 hk]
        exact four_regroup (1 / 2 : ℂ) (1 / (cfg.vac.c0 : ℂ)) (cfg.vac.mu0 : ℂ)
          (chiTT sus.me *ᵥ a1) (chiTT sus.me *ᵥ b1) (chiTT sus.me *ᵥ a2)
          (chiTT sus.me *ᵥ b2)
          (chiTT sus.mm *ᵥ (hPar cfg .above .incident a1))
          (chiTT sus.mm *ᵥ (hPar cfg .above .reflected b1))
          (chiTT sus.mm *ᵥ (hPar cfg .below .incident a2))
          (chiTT sus.mm *ᵥ (hPar cfg .below .reflected b2))
    _ = (1 / 2 : ℂ) • ((1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.me *ᵥ (a1 + b1 + a2 + b2))
          + (cfg.vac.mu0 : ℂ)
            • (chiTT sus.mm *ᵥ (hPar cfg .above .incident a1
                + hPar cfg .above .reflected b1 + hPar cfg .below .incident a2
                + hPar cfg .below .reflected b2))) := by
        rw [← mulVec4 (chiTT sus.me) a1 b1 a2 b2,
          ← mulVec4 (chiTT sus.mm) (hPar cfg .above .incident a1)
            (hPar cfg .above .reflected b1) (hPar cfg .below .incident a2)
            (hPar cfg .below .reflected b2)]
    _ = (1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.me *ᵥ eMid4 a1 b1 a2 b2)
        + (cfg.vac.mu0 : ℂ) • (chiTT sus.mm *ᵥ hMid4 cfg a1 b1 a2 b2) := by
        unfold eMid4 hMid4
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← half_smul_add]

@[expose] noncomputable def powerTerm4 (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) : ℂ :=
  hc (eMid4 a1 b1 a2 b2) (sheetVPar4 cfg sus a1 b1 a2 b2)
    - hc (sheetMPar4 cfg sus a1 b1 a2 b2) (hMid4 cfg a1 b1 a2 b2)

theorem powerTerm4_eq_powerPairing (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) (hk : cfg.kPar = 0) :
    powerTerm4 cfg sus a1 b1 a2 b2
      = powerPairing ⟨eMid4 a1 b1 a2 b2, hMid4 cfg a1 b1 a2 b2⟩
        ((sheetResponse cfg sus).act ⟨eMid4 a1 b1 a2 b2, hMid4 cfg a1 b1 a2 b2⟩) := by
  rw [powerTerm4, sheetVPar4_mid cfg sus a1 b1 a2 b2 hk,
    sheetMPar4_mid cfg sus a1 b1 a2 b2 hk]
  unfold powerPairing SheetResponse.act SheetResponse.electric SheetResponse.magnetic
  simp only [sheetResponse, Matrix.smul_mulVec]

theorem powerTerm4_star (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) (hk : cfg.kPar = 0) (hloss : sus.Lossless) :
    star (powerTerm4 cfg sus a1 b1 a2 b2) = powerTerm4 cfg sus a1 b1 a2 b2 := by
  rw [powerTerm4_eq_powerPairing cfg sus a1 b1 a2 b2 hk]
  exact SheetResponse.power_real (sheetResponse cfg sus)
    (sheetResponse_hermitian cfg sus hloss) ⟨eMid4 a1 b1 a2 b2, hMid4 cfg a1 b1 a2 b2⟩

theorem powerTerm4_im (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) (hk : cfg.kPar = 0) (hloss : sus.Lossless) :
    (powerTerm4 cfg sus a1 b1 a2 b2).im = 0 := by
  have h := powerTerm4_star cfg sus a1 b1 a2 b2 hk hloss
  have h' : (star (powerTerm4 cfg sus a1 b1 a2 b2)).im
      = (powerTerm4 cfg sus a1 b1 a2 b2).im := congrArg Complex.im h
  have h2 := star_im (powerTerm4 cfg sus a1 b1 a2 b2)
  linarith

@[expose] noncomputable def gstcSatisfied4 (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) : Prop :=
  eJump4 a1 b1 a2 b2
      = (Complex.I * (cfg.omega : ℂ)) • (ncross *ᵥ (sheetMPar4 cfg sus a1 b1 a2 b2))
    ∧ ncross *ᵥ (hJump4 cfg a1 b1 a2 b2)
      = (Complex.I * (cfg.omega : ℂ)) • (sheetVPar4 cfg sus a1 b1 a2 b2)

theorem hJump4_gstc (cfg : Config) (sus : Susceptibilities) (a1 b1 a2 b2 : Vec2)
    (hH : ncross *ᵥ (hJump4 cfg a1 b1 a2 b2)
      = (Complex.I * (cfg.omega : ℂ)) • (sheetVPar4 cfg sus a1 b1 a2 b2)) :
    hJump4 cfg a1 b1 a2 b2
      = -(ncross *ᵥ ((Complex.I * (cfg.omega : ℂ))
          • (sheetVPar4 cfg sus a1 b1 a2 b2))) := by
  calc hJump4 cfg a1 b1 a2 b2
      = -(ncross *ᵥ (ncross *ᵥ (hJump4 cfg a1 b1 a2 b2))) := by
        rw [ncross_mulVec_ncross]
        simp
    _ = -(ncross *ᵥ ((Complex.I * (cfg.omega : ℂ))
        • (sheetVPar4 cfg sus a1 b1 a2 b2))) := by
        rw [hH]

theorem fluxC_eMid_hJump4 (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2)
    (hH : ncross *ᵥ (hJump4 cfg a1 b1 a2 b2)
      = (Complex.I * (cfg.omega : ℂ)) • (sheetVPar4 cfg sus a1 b1 a2 b2)) :
    fluxC (eMid4 a1 b1 a2 b2) (hJump4 cfg a1 b1 a2 b2)
      = (Complex.I * (cfg.omega : ℂ))
          • (hc (eMid4 a1 b1 a2 b2) (sheetVPar4 cfg sus a1 b1 a2 b2)) := by
  rw [hJump4_gstc cfg sus a1 b1 a2 b2 hH, fluxC_neg_right,
    fluxC_ncross_mulVec, hc_smul_right, star_omega]
  simp only [smul_eq_mul]
  ring

theorem fluxC_eJump_hMid4 (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2)
    (hE : eJump4 a1 b1 a2 b2
      = (Complex.I * (cfg.omega : ℂ)) • (ncross *ᵥ (sheetMPar4 cfg sus a1 b1 a2 b2))) :
    fluxC (eJump4 a1 b1 a2 b2) (hMid4 cfg a1 b1 a2 b2)
      = -((Complex.I * (cfg.omega : ℂ))
          • (hc (sheetMPar4 cfg sus a1 b1 a2 b2) (hMid4 cfg a1 b1 a2 b2))) := by
  rw [hE, fluxC_smul_left, fluxC_ncross_mulVec']
  simp only [smul_eq_mul]
  ring

theorem fluxC_gstc4 (cfg : Config) (sus : Susceptibilities) (a1 b1 a2 b2 : Vec2)
    (hE : eJump4 a1 b1 a2 b2
      = (Complex.I * (cfg.omega : ℂ)) • (ncross *ᵥ (sheetMPar4 cfg sus a1 b1 a2 b2)))
    (hH : ncross *ᵥ (hJump4 cfg a1 b1 a2 b2)
      = (Complex.I * (cfg.omega : ℂ)) • (sheetVPar4 cfg sus a1 b1 a2 b2)) :
    fluxC (eBelow a2 b2) (hBelow cfg a2 b2)
      - fluxC (eAbove a1 b1) (hAbove cfg a1 b1)
      = -((Complex.I * (cfg.omega : ℂ)) • (powerTerm4 cfg sus a1 b1 a2 b2)) := by
  calc fluxC (eBelow a2 b2) (hBelow cfg a2 b2)
        - fluxC (eAbove a1 b1) (hAbove cfg a1 b1)
      = -(fluxC (eMid4 a1 b1 a2 b2) (hJump4 cfg a1 b1 a2 b2)
          + fluxC (eJump4 a1 b1 a2 b2) (hMid4 cfg a1 b1 a2 b2)) :=
        fluxC_mid_split_of (eMid4 a1 b1 a2 b2) (hMid4 cfg a1 b1 a2 b2)
          (eJump4 a1 b1 a2 b2) (hJump4 cfg a1 b1 a2 b2)
          (eBelow a2 b2) (hBelow cfg a2 b2) (eAbove a1 b1) (hAbove cfg a1 b1)
          (eBelow_mid a1 b1 a2 b2) (eAbove_mid a1 b1 a2 b2)
          (hBelow_mid cfg a1 b1 a2 b2) (hAbove_mid cfg a1 b1 a2 b2)
    _ = -((Complex.I * (cfg.omega : ℂ))
          • (hc (eMid4 a1 b1 a2 b2) (sheetVPar4 cfg sus a1 b1 a2 b2)
            - hc (sheetMPar4 cfg sus a1 b1 a2 b2) (hMid4 cfg a1 b1 a2 b2))) := by
        rw [fluxC_eMid_hJump4 cfg sus a1 b1 a2 b2 hH,
          fluxC_eJump_hMid4 cfg sus a1 b1 a2 b2 hE]
        simp only [smul_eq_mul]
        ring
    _ = -((Complex.I * (cfg.omega : ℂ)) • (powerTerm4 cfg sus a1 b1 a2 b2)) := by
        rw [powerTerm4]

theorem re_I_omega_mul (cfg : Config) (p : ℂ) (hp : p.im = 0) :
    ((Complex.I * (cfg.omega : ℂ)) • p).re = 0 := by
  simp only [smul_eq_mul]
  rw [Complex.mul_re, I_omega_re cfg, hp]
  ring

theorem fluxZ_gstc4 (cfg : Config) (sus : Susceptibilities) (a1 b1 a2 b2 : Vec2)
    (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hgstc : gstcSatisfied4 cfg sus a1 b1 a2 b2) :
    fluxZ (eBelow a2 b2) (hBelow cfg a2 b2)
      = fluxZ (eAbove a1 b1) (hAbove cfg a1 b1) := by
  have h := fluxC_gstc4 cfg sus a1 b1 a2 b2 hgstc.1 hgstc.2
  have hp : (powerTerm4 cfg sus a1 b1 a2 b2).im = 0 :=
    powerTerm4_im cfg sus a1 b1 a2 b2 hk hloss
  have hre : ((Complex.I * (cfg.omega : ℂ)) • (powerTerm4 cfg sus a1 b1 a2 b2)).re = 0 :=
    re_I_omega_mul cfg _ hp
  have hre2 : (fluxC (eBelow a2 b2) (hBelow cfg a2 b2)
      - fluxC (eAbove a1 b1) (hAbove cfg a1 b1)).re = 0 := by
    have h' := congrArg Complex.re h
    rw [Complex.neg_re, hre] at h'
    linarith
  unfold fluxZ
  rw [Complex.sub_re] at hre2
  linarith

theorem fluxZ_below_total (cfg : Config) (a2 b2 : Vec2) (hk : cfg.kPar = 0) :
    fluxZ (eBelow a2 b2) (hBelow cfg a2 b2)
      = wavePower cfg.lower 0 a2 - wavePower cfg.lower 0 b2 := by
  unfold eBelow hBelow
  rw [fluxZ_add_left, fluxZ_add_right, fluxZ_add_right]
  have hcross : fluxZ a2 (hPar cfg .below .reflected b2)
      + fluxZ b2 (hPar cfg .below .incident a2) = 0 :=
    fluxZ_cross_cancel cfg .below a2 b2 hk
  rw [fluxZ_wave cfg .below .incident a2 hk, fluxZ_wave cfg .below .reflected b2 hk]
  rw [show PropDir.sign (Wave.dir .below .incident) = 1 by rfl,
    show PropDir.sign (Wave.dir .below .reflected) = -1 by rfl,
    show Wave.medium cfg .below .incident = cfg.lower by rfl,
    show Wave.medium cfg .below .reflected = cfg.lower by rfl]
  linarith

theorem fluxZ_above_total (cfg : Config) (a1 b1 : Vec2) (hk : cfg.kPar = 0) :
    fluxZ (eAbove a1 b1) (hAbove cfg a1 b1)
      = wavePower cfg.upper 0 b1 - wavePower cfg.upper 0 a1 := by
  unfold eAbove hAbove
  rw [fluxZ_add_left, fluxZ_add_right, fluxZ_add_right]
  have hcross : fluxZ a1 (hPar cfg .above .reflected b1)
      + fluxZ b1 (hPar cfg .above .incident a1) = 0 :=
    fluxZ_cross_cancel cfg .above a1 b1 hk
  rw [fluxZ_wave cfg .above .incident a1 hk, fluxZ_wave cfg .above .reflected b1 hk]
  rw [show PropDir.sign (Wave.dir .above .incident) = -1 by rfl,
    show PropDir.sign (Wave.dir .above .reflected) = 1 by rfl,
    show Wave.medium cfg .above .incident = cfg.upper by rfl,
    show Wave.medium cfg .above .reflected = cfg.upper by rfl]
  linarith

theorem two_port_power_balance (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hgstc : gstcSatisfied4 cfg sus a1 b1 a2 b2) :
    wavePower cfg.upper 0 a1 + wavePower cfg.lower 0 a2
      = wavePower cfg.upper 0 b1 + wavePower cfg.lower 0 b2 := by
  have hflux := fluxZ_gstc4 cfg sus a1 b1 a2 b2 hk hloss hgstc
  have hb := fluxZ_below_total cfg a2 b2 hk
  have ha := fluxZ_above_total cfg a1 b1 hk
  rw [hb, ha] at hflux
  linarith

theorem colRow_kVec_zero (cfg : Config) (s : Side) (sus : Susceptibilities)
    (w : Wave) (hk : cfg.kPar = 0) :
    colRow (kVec cfg.kPar) (couplingVN cfg s sus w) = 0 := by
  rw [hk, kVec_zero, colRow_zero_left]

theorem colRow_lVec_zero (cfg : Config) (s : Side) (sus : Susceptibilities)
    (w : Wave) (hk : cfg.kPar = 0) :
    colRow (lVec cfg.kPar) (couplingWN cfg s sus w) = 0 := by
  rw [hk, lVec_zero, colRow_zero_left]

theorem sheetMPar4_eq (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) :
    sheetMPar4 cfg sus a1 b1 a2 b2
      = sheetMPar cfg .above sus a1 b1 b2
        + couplingWPar cfg .below sus .incident *ᵥ a2 := by
  unfold sheetMPar4 sheetMPar
  rw [← couplingWPar_transmitted_eq_reflected cfg sus]
  abel

theorem sheetVPar4_eq (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) :
    sheetVPar4 cfg sus a1 b1 a2 b2
      = sheetVPar cfg .above sus a1 b1 b2
        + couplingVPar cfg .below sus .incident *ᵥ a2 := by
  unfold sheetVPar4 sheetVPar
  rw [← couplingVPar_transmitted_eq_reflected cfg sus]
  abel

theorem jumpE_above (a1 b1 b2 : Vec2) : jumpE .above a1 b1 b2 = a1 + b1 - b2 := by
  unfold jumpE
  rw [show Side.jumpSign .above = 1 by rfl]
  funext i
  fin_cases i <;> simp

theorem twoPort_electric_eq_gstc4 (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) (hk : cfg.kPar = 0) :
    (boundaryCoeffs cfg .above sus).beI *ᵥ a1
      + (boundaryCoeffs cfg .above sus).beR *ᵥ b1
      + (boundaryCoeffs cfg .below sus).beI *ᵥ a2
      + (boundaryCoeffs cfg .above sus).beT *ᵥ b2
      = eJump4 a1 b1 a2 b2
        - (Complex.I * (cfg.omega : ℂ)) • (ncross *ᵥ (sheetMPar4 cfg sus a1 b1 a2 b2)) := by
  have hidE := boundaryCoeffs_electric cfg .above sus a1 b1 b2
  have hnorm : (Complex.I • ![(cfg.kPar : ℂ)
      * (sheetPNoverEps0 cfg .above sus a1 b1 b2), 0]) = 0 := by
    have hk' : (cfg.kPar : ℂ) = 0 := by exact_mod_cast hk
    rw [hk', zero_mul]
    funext i
    fin_cases i <;> simp
  have hbeI : (boundaryCoeffs cfg .below sus).beI
      = -(iPar)
        - (Complex.I * (cfg.omega : ℂ)) • (ncross * couplingWPar cfg .below sus .incident) := by
    unfold boundaryCoeffs
    rw [show Side.jumpSign .below = -1 by rfl, neg_one_smul_ten2]
    have hn := colRow_kVec_zero cfg .below sus .incident hk
    rw [hn]
    simp
  have hbeI_app : (boundaryCoeffs cfg .below sus).beI *ᵥ a2
      = -(a2)
        - (Complex.I * (cfg.omega : ℂ))
          • (ncross *ᵥ (couplingWPar cfg .below sus .incident *ᵥ a2)) := by
    rw [hbeI, Matrix.sub_mulVec, Matrix.neg_mulVec, smul_mulVec, iPar_mulVec,
      ← Matrix.mulVec_mulVec]
  calc
    (boundaryCoeffs cfg .above sus).beI *ᵥ a1
        + (boundaryCoeffs cfg .above sus).beR *ᵥ b1
        + (boundaryCoeffs cfg .below sus).beI *ᵥ a2
        + (boundaryCoeffs cfg .above sus).beT *ᵥ b2
      = ((boundaryCoeffs cfg .above sus).beI *ᵥ a1
          + (boundaryCoeffs cfg .above sus).beR *ᵥ b1
          + (boundaryCoeffs cfg .above sus).beT *ᵥ b2)
        + (boundaryCoeffs cfg .below sus).beI *ᵥ a2 := by abel
    _ = (jumpE .above a1 b1 b2
          - (Complex.I * (cfg.omega : ℂ))
            • (ncross *ᵥ (sheetMPar cfg .above sus a1 b1 b2)))
        + (-(a2)
          - (Complex.I * (cfg.omega : ℂ))
            • (ncross *ᵥ (couplingWPar cfg .below sus .incident *ᵥ a2))) := by
        rw [hidE, hnorm, hbeI_app]
        abel
    _ = eJump4 a1 b1 a2 b2
        - (Complex.I * (cfg.omega : ℂ))
          • (ncross *ᵥ (sheetMPar4 cfg sus a1 b1 a2 b2)) := by
        rw [sheetMPar4_eq cfg sus a1 b1 a2 b2]
        simp only [Matrix.mulVec_add]
        funext i
        fin_cases i <;>
          simp only [jumpE_above, eJump4, eAbove, eBelow, Pi.add_apply,
            Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] <;>
          ring

theorem twoPort_magnetic_eq_gstc4 (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) (hk : cfg.kPar = 0) :
    (boundaryCoeffs cfg .above sus).bhI *ᵥ a1
      + (boundaryCoeffs cfg .above sus).bhR *ᵥ b1
      + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2
      + (boundaryCoeffs cfg .above sus).bhT *ᵥ b2
      = ncross *ᵥ (hJump4 cfg a1 b1 a2 b2)
        - (Complex.I * (cfg.omega : ℂ)) • (sheetVPar4 cfg sus a1 b1 a2 b2) := by
  have hidM := boundaryCoeffs_magnetic cfg .above sus a1 b1 b2
  have hnorm : (Complex.I • ![0, (cfg.kPar : ℂ)
      * (sheetWNoverMu0 cfg .above sus a1 b1 b2)]) = 0 := by
    have hk' : (cfg.kPar : ℂ) = 0 := by exact_mod_cast hk
    rw [hk', zero_mul]
    funext i
    fin_cases i <;> simp
  have hY := boundaryCoeffs_magnetic_Ysign cfg .below sus
  have hbhI : (boundaryCoeffs cfg .below sus).bhI
      = waveY cfg.lower cfg.kPar
        - (Complex.I * (cfg.omega : ℂ)) • (couplingVPar cfg .below sus .incident) := by
    rw [hY.1, waveYsign_incident .below, one_smul_ten2]
    rw [show Wave.medium cfg .below .incident = cfg.lower by rfl]
    have hn := colRow_lVec_zero cfg .below sus .incident hk
    rw [hn]
    simp
  have hbhI_app : (boundaryCoeffs cfg .below sus).bhI *ᵥ a2
      = waveY cfg.lower cfg.kPar *ᵥ a2
        - (Complex.I * (cfg.omega : ℂ))
          • (couplingVPar cfg .below sus .incident *ᵥ a2) := by
    rw [hbhI, Matrix.sub_mulVec, smul_mulVec]
  have hhtrans : hPar cfg .above .transmitted b2 = hPar cfg .below .reflected b2 := by
    unfold hPar
    have hdir := wave_below_reflected_eq_above_transmitted cfg
    rw [hdir.1, hdir.2]
  have hjh : jumpH cfg .above a1 b1 b2
      = hJump4 cfg a1 b1 a2 b2 + hPar cfg .below .incident a2 := by
    unfold jumpH hJump4 hAbove hBelow
    rw [show Side.jumpSign .above = 1 by rfl]
    rw [hhtrans]
    funext i
    fin_cases i <;> simp <;> ring
  have hncross : ncross *ᵥ (hPar cfg .below .incident a2)
      = -(waveY cfg.lower cfg.kPar *ᵥ a2) := by
    rw [ncross_hPar cfg .below .incident a2]
    rw [show PropDir.sign (Wave.dir .below .incident) = 1 by rfl]
    rw [show Wave.medium cfg .below .incident = cfg.lower by rfl]
    simp
  calc
    (boundaryCoeffs cfg .above sus).bhI *ᵥ a1
        + (boundaryCoeffs cfg .above sus).bhR *ᵥ b1
        + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2
        + (boundaryCoeffs cfg .above sus).bhT *ᵥ b2
      = ((boundaryCoeffs cfg .above sus).bhI *ᵥ a1
          + (boundaryCoeffs cfg .above sus).bhR *ᵥ b1
          + (boundaryCoeffs cfg .above sus).bhT *ᵥ b2)
        + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2 := by abel
    _ = (ncross *ᵥ (jumpH cfg .above a1 b1 b2)
          - (Complex.I * (cfg.omega : ℂ))
            • (sheetVPar cfg .above sus a1 b1 b2))
        + (waveY cfg.lower cfg.kPar *ᵥ a2
          - (Complex.I * (cfg.omega : ℂ))
            • (couplingVPar cfg .below sus .incident *ᵥ a2)) := by
        rw [hidM, hnorm, hbhI_app]
        abel
    _ = (ncross *ᵥ (hJump4 cfg a1 b1 a2 b2 + hPar cfg .below .incident a2)
          - (Complex.I * (cfg.omega : ℂ))
            • (sheetVPar cfg .above sus a1 b1 b2))
        + (waveY cfg.lower cfg.kPar *ᵥ a2
          - (Complex.I * (cfg.omega : ℂ))
            • (couplingVPar cfg .below sus .incident *ᵥ a2)) := by
        rw [hjh]
    _ = (ncross *ᵥ (hJump4 cfg a1 b1 a2 b2)
          + ncross *ᵥ (hPar cfg .below .incident a2)
          - (Complex.I * (cfg.omega : ℂ))
            • (sheetVPar cfg .above sus a1 b1 b2))
        + (waveY cfg.lower cfg.kPar *ᵥ a2
          - (Complex.I * (cfg.omega : ℂ))
            • (couplingVPar cfg .below sus .incident *ᵥ a2)) := by
        rw [Matrix.mulVec_add]
    _ = (ncross *ᵥ (hJump4 cfg a1 b1 a2 b2)
          - waveY cfg.lower cfg.kPar *ᵥ a2
          - (Complex.I * (cfg.omega : ℂ))
            • (sheetVPar cfg .above sus a1 b1 b2))
        + (waveY cfg.lower cfg.kPar *ᵥ a2
          - (Complex.I * (cfg.omega : ℂ))
            • (couplingVPar cfg .below sus .incident *ᵥ a2)) := by
        rw [hncross]
        abel
    _ = ncross *ᵥ (hJump4 cfg a1 b1 a2 b2)
        - (Complex.I * (cfg.omega : ℂ))
          • (sheetVPar cfg .above sus a1 b1 b2
            + couplingVPar cfg .below sus .incident *ᵥ a2) := by
        rw [smul_add]
        abel
    _ = ncross *ᵥ (hJump4 cfg a1 b1 a2 b2)
        - (Complex.I * (cfg.omega : ℂ)) • (sheetVPar4 cfg sus a1 b1 a2 b2) := by
        rw [sheetVPar4_eq cfg sus a1 b1 a2 b2]

theorem twoPortSystem_iff_gstcSatisfied4 (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) (hk : cfg.kPar = 0) :
    twoPortSystem cfg sus a1 b1 a2 b2 ↔ gstcSatisfied4 cfg sus a1 b1 a2 b2 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have he := twoPort_electric_eq_gstc4 cfg sus a1 b1 a2 b2 hk
      have h1 := h.1
      rw [he] at h1
      exact eq_of_sub_eq_zero h1
    · have hm := twoPort_magnetic_eq_gstc4 cfg sus a1 b1 a2 b2 hk
      have h2 := h.2
      rw [hm] at h2
      exact eq_of_sub_eq_zero h2
  · intro h
    refine ⟨?_, ?_⟩
    · have he := twoPort_electric_eq_gstc4 cfg sus a1 b1 a2 b2 hk
      calc
        (boundaryCoeffs cfg .above sus).beI *ᵥ a1
            + (boundaryCoeffs cfg .above sus).beR *ᵥ b1
            + (boundaryCoeffs cfg .below sus).beI *ᵥ a2
            + (boundaryCoeffs cfg .above sus).beT *ᵥ b2
          = eJump4 a1 b1 a2 b2
              - (Complex.I * (cfg.omega : ℂ))
                • (ncross *ᵥ (sheetMPar4 cfg sus a1 b1 a2 b2)) := he
        _ = 0 := by rw [h.1]; ring
    · have hm := twoPort_magnetic_eq_gstc4 cfg sus a1 b1 a2 b2 hk
      calc
        (boundaryCoeffs cfg .above sus).bhI *ᵥ a1
            + (boundaryCoeffs cfg .above sus).bhR *ᵥ b1
            + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2
            + (boundaryCoeffs cfg .above sus).bhT *ᵥ b2
          = ncross *ᵥ (hJump4 cfg a1 b1 a2 b2)
              - (Complex.I * (cfg.omega : ℂ)) • (sheetVPar4 cfg sus a1 b1 a2 b2) := hm
        _ = 0 := by rw [h.2]; ring

theorem hc_self (u : Vec2) :
    hc u u = ((Complex.normSq (u 0) + Complex.normSq (u 1) : ℝ) : ℂ) := by
  rw [hc_expand]
  have e0 : u 0 * star (u 0) = ((Complex.normSq (u 0) : ℝ) : ℂ) := by
    calc u 0 * star (u 0) = star (u 0) * u 0 := by ring
      _ = ((Complex.normSq (u 0) : ℝ) : ℂ) :=
        Complex.normSq_eq_conj_mul_self (z := u 0).symm
  have e1 : u 1 * star (u 1) = ((Complex.normSq (u 1) : ℝ) : ℂ) := by
    calc u 1 * star (u 1) = star (u 1) * u 1 := by ring
      _ = ((Complex.normSq (u 1) : ℝ) : ℂ) :=
        Complex.normSq_eq_conj_mul_self (z := u 1).symm
  rw [e0, e1, Complex.ofReal_add]

@[expose] noncomputable def powerDefect (cfg : Config) (a1 b1 a2 b2 : Vec2) : ℂ :=
  ((1 / cfg.upper.eta : ℝ) : ℂ) * (hc a1 a1 - hc b1 b1)
    + ((1 / cfg.lower.eta : ℝ) : ℂ) * (hc a2 a2 - hc b2 b2)

@[expose] noncomputable def powerDefectCross (cfg : Config)
    (a1 b1 a2 b2 a1' b1' a2' b2' : Vec2) : ℂ :=
  ((1 / cfg.upper.eta : ℝ) : ℂ) * (hc a1 a1' - hc b1 b1')
    + ((1 / cfg.lower.eta : ℝ) : ℂ) * (hc a2 a2' - hc b2 b2')

theorem powerDefect_add (cfg : Config)
    (a1 b1 a2 b2 a1' b1' a2' b2' : Vec2) :
    powerDefect cfg (a1 + a1') (b1 + b1') (a2 + a2') (b2 + b2')
      = powerDefect cfg a1 b1 a2 b2 + powerDefect cfg a1' b1' a2' b2'
        + powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2'
        + powerDefectCross cfg a1' b1' a2' b2' a1 b1 a2 b2 := by
  unfold powerDefect powerDefectCross
  simp only [hc_add_right, hc_add_left]
  ring

theorem hc_add_smul_I (u v : Vec2) :
    hc (u + Complex.I • v) (u + Complex.I • v)
      = hc u u + hc v v + Complex.I • (hc v u - hc u v) := by
  simp only [hc_add_right, hc_add_left, hc_smul_left, hc_smul_right, smul_eq_mul]
  rw [star_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem powerDefect_smul_I (cfg : Config)
    (a1 b1 a2 b2 a1' b1' a2' b2' : Vec2) :
    powerDefect cfg (a1 + Complex.I • a1') (b1 + Complex.I • b1')
        (a2 + Complex.I • a2') (b2 + Complex.I • b2')
      = powerDefect cfg a1 b1 a2 b2 + powerDefect cfg a1' b1' a2' b2'
        + (-(Complex.I)) • powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2'
        + Complex.I • powerDefectCross cfg a1' b1' a2' b2' a1 b1 a2 b2 := by
  unfold powerDefect powerDefectCross
  rw [hc_add_smul_I, hc_add_smul_I, hc_add_smul_I, hc_add_smul_I]
  simp only [smul_eq_mul]
  ring

theorem powerDefect_eq_zero (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hgstc : gstcSatisfied4 cfg sus a1 b1 a2 b2) :
    powerDefect cfg a1 b1 a2 b2 = 0 := by
  have hbal := two_port_power_balance cfg sus a1 b1 a2 b2 hk hloss hgstc
  have hηu : cfg.upper.eta ≠ 0 := cfg.upper.eta_pos.ne'
  have hηl : cfg.lower.eta ≠ 0 := cfg.lower.eta_pos.ne'
  have hbal' : (Complex.normSq (a1 0) + Complex.normSq (a1 1)) / cfg.upper.eta
      + (Complex.normSq (a2 0) + Complex.normSq (a2 1)) / cfg.lower.eta
      = (Complex.normSq (b1 0) + Complex.normSq (b1 1)) / cfg.upper.eta
      + (Complex.normSq (b2 0) + Complex.normSq (b2 1)) / cfg.lower.eta := by
    rw [wavePower_normal cfg.upper a1, wavePower_normal cfg.lower a2,
      wavePower_normal cfg.upper b1, wavePower_normal cfg.lower b2] at hbal
    have h2 := congrArg (fun t : ℝ => 2 * t) hbal
    rw [← div_div, ← div_div, ← div_div, ← div_div] at h2
    rw [mul_add, mul_add] at h2
    rw [mul_div_assoc', mul_div_assoc', mul_div_assoc', mul_div_assoc'] at h2
    field_simp [hηu, hηl] at h2 ⊢
    exact h2
  have hre : ((Complex.normSq (a1 0) + Complex.normSq (a1 1)
      - Complex.normSq (b1 0) - Complex.normSq (b1 1)) / cfg.upper.eta
      + (Complex.normSq (a2 0) + Complex.normSq (a2 1)
      - Complex.normSq (b2 0) - Complex.normSq (b2 1)) / cfg.lower.eta) = 0 := by
    simp only [div_eq_mul_inv] at hbal' ⊢
    linarith
  have hdefect : powerDefect cfg a1 b1 a2 b2
      = ((Complex.normSq (a1 0) + Complex.normSq (a1 1)
          - Complex.normSq (b1 0) - Complex.normSq (b1 1)) / cfg.upper.eta
        + (Complex.normSq (a2 0) + Complex.normSq (a2 1)
          - Complex.normSq (b2 0) - Complex.normSq (b2 1)) / cfg.lower.eta : ℂ) := by
    unfold powerDefect
    rw [hc_self, hc_self, hc_self, hc_self]
    push_cast
    ring
  rw [hdefect]
  exact_mod_cast hre

theorem powerDefect_polarization (cfg : Config)
    (a1 b1 a2 b2 a1' b1' a2' b2' : Vec2)
    (h1 : powerDefect cfg a1 b1 a2 b2 = 0)
    (h2 : powerDefect cfg a1' b1' a2' b2' = 0)
    (h3 : powerDefect cfg (a1 + a1') (b1 + b1') (a2 + a2') (b2 + b2') = 0)
    (h4 : powerDefect cfg (a1 + Complex.I • a1') (b1 + Complex.I • b1')
        (a2 + Complex.I • a2') (b2 + Complex.I • b2') = 0) :
    powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2' = 0 := by
  have hadd := powerDefect_add cfg a1 b1 a2 b2 a1' b1' a2' b2'
  have hsmul := powerDefect_smul_I cfg a1 b1 a2 b2 a1' b1' a2' b2'
  have e1 : powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2'
      + powerDefectCross cfg a1' b1' a2' b2' a1 b1 a2 b2 = 0 := by
    calc powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2'
        + powerDefectCross cfg a1' b1' a2' b2' a1 b1 a2 b2
        = powerDefect cfg (a1 + a1') (b1 + b1') (a2 + a2') (b2 + b2')
          - powerDefect cfg a1 b1 a2 b2 - powerDefect cfg a1' b1' a2' b2' := by
            rw [hadd]; ring
      _ = 0 - 0 - 0 := by rw [h3, h1, h2]
      _ = 0 := by ring
  have e2 : (-(Complex.I)) • powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2'
      + Complex.I • powerDefectCross cfg a1' b1' a2' b2' a1 b1 a2 b2 = 0 := by
    calc (-(Complex.I)) • powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2'
        + Complex.I • powerDefectCross cfg a1' b1' a2' b2' a1 b1 a2 b2
        = powerDefect cfg (a1 + Complex.I • a1') (b1 + Complex.I • b1')
            (a2 + Complex.I • a2') (b2 + Complex.I • b2')
          - powerDefect cfg a1 b1 a2 b2 - powerDefect cfg a1' b1' a2' b2' := by
            rw [hsmul]; simp only [smul_eq_mul]; ring
      _ = 0 - 0 - 0 := by rw [h4, h1, h2]
      _ = 0 := by ring
  have e2' : powerDefectCross cfg a1' b1' a2' b2' a1 b1 a2 b2
      - powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2' = 0 := by
    simp only [smul_eq_mul] at e2
    have h : Complex.I * (powerDefectCross cfg a1' b1' a2' b2' a1 b1 a2 b2
        - powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2') = 0 := by
      calc Complex.I * (powerDefectCross cfg a1' b1' a2' b2' a1 b1 a2 b2
          - powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2')
          = (-(Complex.I)) * powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2'
            + Complex.I * powerDefectCross cfg a1' b1' a2' b2' a1 b1 a2 b2 := by ring
        _ = 0 := e2
    rcases mul_eq_zero.mp h with hI | h
    · simp at hI
    · exact h
  rw [sub_eq_zero.mp e2'] at e1
  have h2 : (2 : ℂ) * powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2' = 0 := by
    calc (2 : ℂ) * powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2'
        = powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2'
          + powerDefectCross cfg a1 b1 a2 b2 a1' b1' a2' b2' := by ring
      _ = 0 := e1
  rcases mul_eq_zero.mp h2 with hz | h
  · norm_num at hz
  · exact h

@[expose] def ScatteringMatrix.Conservative (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) : Prop :=
  ∀ a1 a2 : Vec2, gstcSatisfied4 cfg sus a1 (S.out1 a1 a2) a2 (S.out2 a1 a2)

theorem powerDefectCross_eq_zero_of_conservative (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hcons : S.Conservative cfg sus) (a1 a2 a1' a2' : Vec2) :
    powerDefectCross cfg a1 (S.out1 a1 a2) a2 (S.out2 a1 a2)
      a1' (S.out1 a1' a2') a2' (S.out2 a1' a2') = 0 := by
  have hx := hcons a1 a2
  have hy := hcons a1' a2'
  have hxy := hcons (a1 + a1') (a2 + a2')
  have hIy := hcons (a1 + Complex.I • a1') (a2 + Complex.I • a2')
  have hdx : powerDefect cfg a1 (S.out1 a1 a2) a2 (S.out2 a1 a2) = 0 :=
    powerDefect_eq_zero cfg sus a1 (S.out1 a1 a2) a2 (S.out2 a1 a2) hk hloss hx
  have hdy : powerDefect cfg a1' (S.out1 a1' a2') a2' (S.out2 a1' a2') = 0 :=
    powerDefect_eq_zero cfg sus a1' (S.out1 a1' a2') a2' (S.out2 a1' a2') hk hloss hy
  have hdxy : powerDefect cfg (a1 + a1') (S.out1 (a1 + a1') (a2 + a2'))
      (a2 + a2') (S.out2 (a1 + a1') (a2 + a2')) = 0 :=
    powerDefect_eq_zero cfg sus (a1 + a1') (S.out1 (a1 + a1') (a2 + a2'))
      (a2 + a2') (S.out2 (a1 + a1') (a2 + a2')) hk hloss hxy
  have hdIy : powerDefect cfg (a1 + Complex.I • a1')
      (S.out1 (a1 + Complex.I • a1') (a2 + Complex.I • a2'))
      (a2 + Complex.I • a2')
      (S.out2 (a1 + Complex.I • a1') (a2 + Complex.I • a2')) = 0 :=
    powerDefect_eq_zero cfg sus (a1 + Complex.I • a1')
      (S.out1 (a1 + Complex.I • a1') (a2 + Complex.I • a2'))
      (a2 + Complex.I • a2')
      (S.out2 (a1 + Complex.I • a1') (a2 + Complex.I • a2')) hk hloss hIy
  rw [S.out1_add a1 a2 a1' a2', S.out2_add a1 a2 a1' a2'] at hdxy
  rw [S.out1_smul Complex.I a1 a2 a1' a2',
    S.out2_smul Complex.I a1 a2 a1' a2'] at hdIy
  exact powerDefect_polarization cfg a1 (S.out1 a1 a2) a2 (S.out2 a1 a2)
    a1' (S.out1 a1' a2') a2' (S.out2 a1' a2') hdx hdy hdxy hdIy

@[expose] noncomputable def powerWeight (m : Medium) : ℂ := ((1 / m.eta : ℝ) : ℂ)

theorem powerWeight_eq (m : Medium) : ((1 / m.eta : ℝ) : ℂ) = powerWeight m := rfl

theorem star_powerWeight (m : Medium) : star (powerWeight m) = powerWeight m := by
  unfold powerWeight
  exact star_ofReal _

theorem hc_mulVec_basis (A : Ten2) (i j : Fin 2) :
    hc (Pi.single i 1) (A *ᵥ (Pi.single j 1)) = star (A i j) := by
  simp [hc_expand, Pi.single_apply]
  fin_cases i <;> simp

theorem ten2_ext_of_hc (A B : Ten2)
    (h : ∀ u v : Vec2, hc u (A *ᵥ v) = hc u (B *ᵥ v)) : A = B := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  rw [hc_mulVec_basis, hc_mulVec_basis] at h1
  simp only [Complex.star_def] at h1
  exact star_injective h1

theorem hc_zero_left (v : Vec2) : hc (0 : Vec2) v = 0 := by
  simp [hc_expand]

theorem hc_zero_right (u : Vec2) : hc u (0 : Vec2) = 0 := by
  simp [hc_expand]

theorem hc_smul_mulVec (c : ℂ) (hcstar : star c = c) (u : Vec2) (M : Ten2) (v : Vec2) :
    c * hc u (M *ᵥ v) = hc u ((c • M) *ᵥ v) := by
  rw [Matrix.smul_mulVec, hc_smul_right, hcstar]
  simp only [smul_eq_mul]

theorem hc_mulVec_mulVec_sum (A B : Ten2) (u u' v v' : Vec2) :
    hc (A *ᵥ u + B *ᵥ v) (A *ᵥ u' + B *ᵥ v')
      = hc u ((ten2Adjoint A * A) *ᵥ u')
        + hc u ((ten2Adjoint A * B) *ᵥ v')
        + hc v ((ten2Adjoint B * A) *ᵥ u')
        + hc v ((ten2Adjoint B * B) *ᵥ v') := by
  rw [hc_add_left, hc_add_right, hc_add_right]
  rw [← hc_ten2Adjoint, ← hc_ten2Adjoint, ← hc_ten2Adjoint, ← hc_ten2Adjoint]
  simp only [Matrix.mulVec_mulVec]
  ring

theorem hc_out1_blocks (S : ScatteringMatrix) (a1 a2 a1' a2' : Vec2) :
    hc (S.out1 a1 a2) (S.out1 a1' a2')
      = hc a1 ((ten2Adjoint S.r1 * S.r1) *ᵥ a1')
        + hc a1 ((ten2Adjoint S.r1 * S.t12) *ᵥ a2')
        + hc a2 ((ten2Adjoint S.t12 * S.r1) *ᵥ a1')
        + hc a2 ((ten2Adjoint S.t12 * S.t12) *ᵥ a2') := by
  simpa only [ScatteringMatrix.out1] using
    hc_mulVec_mulVec_sum S.r1 S.t12 a1 a1' a2 a2'

theorem hc_out2_blocks (S : ScatteringMatrix) (a1 a2 a1' a2' : Vec2) :
    hc (S.out2 a1 a2) (S.out2 a1' a2')
      = hc a1 ((ten2Adjoint S.t21 * S.t21) *ᵥ a1')
        + hc a1 ((ten2Adjoint S.t21 * S.r2) *ᵥ a2')
        + hc a2 ((ten2Adjoint S.r2 * S.t21) *ᵥ a1')
        + hc a2 ((ten2Adjoint S.r2 * S.r2) *ᵥ a2') := by
  simpa only [ScatteringMatrix.out2] using
    hc_mulVec_mulVec_sum S.t21 S.r2 a1 a1' a2 a2'

theorem two_port_isometry_of_conservative (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hcons : S.Conservative cfg sus) (a1 a2 a1' a2' : Vec2) :
    powerWeight cfg.upper * hc a1 a1' + powerWeight cfg.lower * hc a2 a2'
      = powerWeight cfg.upper * hc (S.out1 a1 a2) (S.out1 a1' a2')
        + powerWeight cfg.lower * hc (S.out2 a1 a2) (S.out2 a1' a2') := by
  have h := powerDefectCross_eq_zero_of_conservative cfg sus S hk hloss hcons a1 a2 a1' a2'
  unfold powerDefectCross at h
  rw [powerWeight_eq cfg.upper, powerWeight_eq cfg.lower] at h
  calc powerWeight cfg.upper * hc a1 a1' + powerWeight cfg.lower * hc a2 a2'
      = (powerWeight cfg.upper
            * (hc a1 a1' - hc (S.out1 a1 a2) (S.out1 a1' a2'))
          + powerWeight cfg.lower
            * (hc a2 a2' - hc (S.out2 a1 a2) (S.out2 a1' a2')))
        + powerWeight cfg.upper * hc (S.out1 a1 a2) (S.out1 a1' a2')
        + powerWeight cfg.lower * hc (S.out2 a1 a2) (S.out2 a1' a2') := by ring
    _ = 0 + powerWeight cfg.upper * hc (S.out1 a1 a2) (S.out1 a1' a2')
        + powerWeight cfg.lower * hc (S.out2 a1 a2) (S.out2 a1' a2') := by rw [h]
    _ = powerWeight cfg.upper * hc (S.out1 a1 a2) (S.out1 a1' a2')
        + powerWeight cfg.lower * hc (S.out2 a1 a2) (S.out2 a1' a2') := by ring

theorem two_port_block_11 (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hcons : S.Conservative cfg sus) :
    (powerWeight cfg.upper) • (ten2Adjoint S.r1 * S.r1)
      + (powerWeight cfg.lower) • (ten2Adjoint S.t21 * S.t21)
      = (powerWeight cfg.upper) • 1 := by
  have hwu : star (powerWeight cfg.upper) = powerWeight cfg.upper := star_powerWeight _
  have hwl : star (powerWeight cfg.lower) = powerWeight cfg.lower := star_powerWeight _
  have hkey : ∀ u v : Vec2,
      hc u ((powerWeight cfg.upper • 1) *ᵥ v)
        = hc u ((powerWeight cfg.upper • (ten2Adjoint S.r1 * S.r1)
              + powerWeight cfg.lower • (ten2Adjoint S.t21 * S.t21)) *ᵥ v) := by
    intro u v
    have h := two_port_isometry_of_conservative cfg sus S hk hloss hcons
      u (0 : Vec2) v (0 : Vec2)
    rw [hc_out1_blocks S u 0 v 0, hc_out2_blocks S u 0 v 0] at h
    simp only [hc_zero_left, hc_zero_right, Matrix.mulVec_zero, add_zero, mul_zero] at h
    calc hc u ((powerWeight cfg.upper • 1) *ᵥ v)
        = powerWeight cfg.upper * hc u v := by
          simpa only [Matrix.one_mulVec] using
            (hc_smul_mulVec (powerWeight cfg.upper) hwu u (1 : Ten2) v).symm
      _ = powerWeight cfg.upper * hc u ((ten2Adjoint S.r1 * S.r1) *ᵥ v)
          + powerWeight cfg.lower * hc u ((ten2Adjoint S.t21 * S.t21) *ᵥ v) := h
      _ = hc u ((powerWeight cfg.upper • (ten2Adjoint S.r1 * S.r1)) *ᵥ v)
          + hc u ((powerWeight cfg.lower • (ten2Adjoint S.t21 * S.t21)) *ᵥ v) := by
          rw [hc_smul_mulVec (powerWeight cfg.upper) hwu u (ten2Adjoint S.r1 * S.r1) v,
            hc_smul_mulVec (powerWeight cfg.lower) hwl u (ten2Adjoint S.t21 * S.t21) v]
      _ = hc u ((powerWeight cfg.upper • (ten2Adjoint S.r1 * S.r1)
              + powerWeight cfg.lower • (ten2Adjoint S.t21 * S.t21)) *ᵥ v) := by
          rw [Matrix.add_mulVec, hc_add_right]
  exact (ten2_ext_of_hc _ _ hkey).symm

theorem two_port_block_12 (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hcons : S.Conservative cfg sus) :
    (powerWeight cfg.upper) • (ten2Adjoint S.r1 * S.t12)
      + (powerWeight cfg.lower) • (ten2Adjoint S.t21 * S.r2) = 0 := by
  have hwu : star (powerWeight cfg.upper) = powerWeight cfg.upper := star_powerWeight _
  have hwl : star (powerWeight cfg.lower) = powerWeight cfg.lower := star_powerWeight _
  have hkey : ∀ u v : Vec2,
      hc u ((powerWeight cfg.upper • (ten2Adjoint S.r1 * S.t12)
            + powerWeight cfg.lower • (ten2Adjoint S.t21 * S.r2)) *ᵥ v) = 0 := by
    intro u v
    have h := two_port_isometry_of_conservative cfg sus S hk hloss hcons
      u (0 : Vec2) (0 : Vec2) v
    rw [hc_out1_blocks S u 0 0 v, hc_out2_blocks S u 0 0 v] at h
    simp only [hc_zero_left, hc_zero_right, Matrix.mulVec_zero, add_zero, zero_add,
      mul_zero] at h
    calc hc u ((powerWeight cfg.upper • (ten2Adjoint S.r1 * S.t12)
            + powerWeight cfg.lower • (ten2Adjoint S.t21 * S.r2)) *ᵥ v)
        = hc u ((powerWeight cfg.upper • (ten2Adjoint S.r1 * S.t12)) *ᵥ v)
          + hc u ((powerWeight cfg.lower • (ten2Adjoint S.t21 * S.r2)) *ᵥ v) := by
          rw [Matrix.add_mulVec, hc_add_right]
      _ = powerWeight cfg.upper * hc u ((ten2Adjoint S.r1 * S.t12) *ᵥ v)
          + powerWeight cfg.lower * hc u ((ten2Adjoint S.t21 * S.r2) *ᵥ v) := by
          rw [← hc_smul_mulVec (powerWeight cfg.upper) hwu u (ten2Adjoint S.r1 * S.t12) v,
            ← hc_smul_mulVec (powerWeight cfg.lower) hwl u (ten2Adjoint S.t21 * S.r2) v]
      _ = 0 := h.symm
  have hz : ∀ u v : Vec2,
      hc u ((powerWeight cfg.upper • (ten2Adjoint S.r1 * S.t12)
            + powerWeight cfg.lower • (ten2Adjoint S.t21 * S.r2)) *ᵥ v)
        = hc u ((0 : Ten2) *ᵥ v) := by
    intro u v
    rw [hkey u v, Matrix.zero_mulVec, hc_zero_right]
  exact ten2_ext_of_hc
    (powerWeight cfg.upper • (ten2Adjoint S.r1 * S.t12)
      + powerWeight cfg.lower • (ten2Adjoint S.t21 * S.r2)) (0 : Ten2) hz

theorem two_port_block_21 (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hcons : S.Conservative cfg sus) :
    (powerWeight cfg.upper) • (ten2Adjoint S.t12 * S.r1)
      + (powerWeight cfg.lower) • (ten2Adjoint S.r2 * S.t21) = 0 := by
  have hwu : star (powerWeight cfg.upper) = powerWeight cfg.upper := star_powerWeight _
  have hwl : star (powerWeight cfg.lower) = powerWeight cfg.lower := star_powerWeight _
  have hkey : ∀ u v : Vec2,
      hc u ((powerWeight cfg.upper • (ten2Adjoint S.t12 * S.r1)
            + powerWeight cfg.lower • (ten2Adjoint S.r2 * S.t21)) *ᵥ v) = 0 := by
    intro u v
    have h := two_port_isometry_of_conservative cfg sus S hk hloss hcons
      (0 : Vec2) u v (0 : Vec2)
    rw [hc_out1_blocks S 0 u v 0, hc_out2_blocks S 0 u v 0] at h
    simp only [hc_zero_left, hc_zero_right, Matrix.mulVec_zero, add_zero, zero_add,
      mul_zero] at h
    calc hc u ((powerWeight cfg.upper • (ten2Adjoint S.t12 * S.r1)
            + powerWeight cfg.lower • (ten2Adjoint S.r2 * S.t21)) *ᵥ v)
        = hc u ((powerWeight cfg.upper • (ten2Adjoint S.t12 * S.r1)) *ᵥ v)
          + hc u ((powerWeight cfg.lower • (ten2Adjoint S.r2 * S.t21)) *ᵥ v) := by
          rw [Matrix.add_mulVec, hc_add_right]
      _ = powerWeight cfg.upper * hc u ((ten2Adjoint S.t12 * S.r1) *ᵥ v)
          + powerWeight cfg.lower * hc u ((ten2Adjoint S.r2 * S.t21) *ᵥ v) := by
          rw [← hc_smul_mulVec (powerWeight cfg.upper) hwu u (ten2Adjoint S.t12 * S.r1) v,
            ← hc_smul_mulVec (powerWeight cfg.lower) hwl u (ten2Adjoint S.r2 * S.t21) v]
      _ = 0 := h.symm
  have hz : ∀ u v : Vec2,
      hc u ((powerWeight cfg.upper • (ten2Adjoint S.t12 * S.r1)
            + powerWeight cfg.lower • (ten2Adjoint S.r2 * S.t21)) *ᵥ v)
        = hc u ((0 : Ten2) *ᵥ v) := by
    intro u v
    rw [hkey u v, Matrix.zero_mulVec, hc_zero_right]
  exact ten2_ext_of_hc
    (powerWeight cfg.upper • (ten2Adjoint S.t12 * S.r1)
      + powerWeight cfg.lower • (ten2Adjoint S.r2 * S.t21)) (0 : Ten2) hz

theorem two_port_block_22 (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hcons : S.Conservative cfg sus) :
    (powerWeight cfg.upper) • (ten2Adjoint S.t12 * S.t12)
      + (powerWeight cfg.lower) • (ten2Adjoint S.r2 * S.r2)
      = (powerWeight cfg.lower) • 1 := by
  have hwu : star (powerWeight cfg.upper) = powerWeight cfg.upper := star_powerWeight _
  have hwl : star (powerWeight cfg.lower) = powerWeight cfg.lower := star_powerWeight _
  have hkey : ∀ u v : Vec2,
      hc u ((powerWeight cfg.lower • 1) *ᵥ v)
        = hc u ((powerWeight cfg.upper • (ten2Adjoint S.t12 * S.t12)
              + powerWeight cfg.lower • (ten2Adjoint S.r2 * S.r2)) *ᵥ v) := by
    intro u v
    have h := two_port_isometry_of_conservative cfg sus S hk hloss hcons
      (0 : Vec2) u (0 : Vec2) v
    rw [hc_out1_blocks S 0 u 0 v, hc_out2_blocks S 0 u 0 v] at h
    simp only [hc_zero_left, hc_zero_right, Matrix.mulVec_zero, add_zero, zero_add,
      mul_zero] at h
    calc hc u ((powerWeight cfg.lower • 1) *ᵥ v)
        = powerWeight cfg.lower * hc u v := by
          simpa only [Matrix.one_mulVec] using
            (hc_smul_mulVec (powerWeight cfg.lower) hwl u (1 : Ten2) v).symm
      _ = powerWeight cfg.upper * hc u ((ten2Adjoint S.t12 * S.t12) *ᵥ v)
          + powerWeight cfg.lower * hc u ((ten2Adjoint S.r2 * S.r2) *ᵥ v) := h
      _ = hc u ((powerWeight cfg.upper • (ten2Adjoint S.t12 * S.t12)) *ᵥ v)
          + hc u ((powerWeight cfg.lower • (ten2Adjoint S.r2 * S.r2)) *ᵥ v) := by
          rw [hc_smul_mulVec (powerWeight cfg.upper) hwu u (ten2Adjoint S.t12 * S.t12) v,
            hc_smul_mulVec (powerWeight cfg.lower) hwl u (ten2Adjoint S.r2 * S.r2) v]
      _ = hc u ((powerWeight cfg.upper • (ten2Adjoint S.t12 * S.t12)
              + powerWeight cfg.lower • (ten2Adjoint S.r2 * S.r2)) *ᵥ v) := by
          rw [Matrix.add_mulVec, hc_add_right]
  exact (ten2_ext_of_hc _ _ hkey).symm

theorem ten2Adjoint_smul (c : ℂ) (M : Ten2) :
    ten2Adjoint (c • M) = star c • ten2Adjoint M := by
  ext i j
  simp [ten2Adjoint, Matrix.smul_apply, star_mul, mul_comm]

theorem sqrt_ratio_sq_real (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (Real.sqrt b / Real.sqrt a) ^ 2 = b / a := by
  rw [div_pow, Real.sq_sqrt (le_of_lt hb), Real.sq_sqrt (le_of_lt ha)]

theorem sqrt_ratio_mul_real (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (Real.sqrt b / Real.sqrt a) * (a / b) = Real.sqrt a / Real.sqrt b := by
  field_simp
  rw [Real.sq_sqrt (le_of_lt hb), Real.sq_sqrt (le_of_lt ha)]
  ring

theorem sqrt_ratio_sq_complex (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((Real.sqrt b / Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt b / Real.sqrt a : ℝ) : ℂ)
      = ((b / a : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  apply Complex.ofReal_inj.mpr
  rw [← pow_two, sqrt_ratio_sq_real a b ha hb]

theorem sqrt_ratio_mul_complex (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((Real.sqrt b / Real.sqrt a : ℝ) : ℂ) * ((a / b : ℝ) : ℂ)
      = ((Real.sqrt a / Real.sqrt b : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  apply Complex.ofReal_inj.mpr
  exact sqrt_ratio_mul_real a b ha hb

@[expose] noncomputable def ScatteringMatrix.t21_norm (cfg : Config) (S : ScatteringMatrix) : Ten2 :=
  ((Real.sqrt cfg.upper.eta / Real.sqrt cfg.lower.eta : ℝ) : ℂ) • S.t21

@[expose] noncomputable def ScatteringMatrix.t12_norm (cfg : Config) (S : ScatteringMatrix) : Ten2 :=
  ((Real.sqrt cfg.lower.eta / Real.sqrt cfg.upper.eta : ℝ) : ℂ) • S.t12

theorem etaU_powerWeight_upper (cfg : Config) :
    ((cfg.upper.eta : ℝ) : ℂ) * powerWeight cfg.upper = 1 := by
  unfold powerWeight
  rw [← Complex.ofReal_mul]
  apply Complex.ofReal_inj.mpr
  have hne : cfg.upper.eta ≠ 0 := ne_of_gt cfg.upper.eta_pos
  field_simp [hne]

theorem etaU_powerWeight_lower (cfg : Config) :
    ((cfg.upper.eta : ℝ) : ℂ) * powerWeight cfg.lower
      = ((cfg.upper.eta / cfg.lower.eta : ℝ) : ℂ) := by
  unfold powerWeight
  rw [← Complex.ofReal_mul]
  apply Complex.ofReal_inj.mpr
  have hne : cfg.lower.eta ≠ 0 := ne_of_gt cfg.lower.eta_pos
  field_simp [hne]

theorem etaL_powerWeight_upper (cfg : Config) :
    ((cfg.lower.eta : ℝ) : ℂ) * powerWeight cfg.upper
      = ((cfg.lower.eta / cfg.upper.eta : ℝ) : ℂ) := by
  unfold powerWeight
  rw [← Complex.ofReal_mul]
  apply Complex.ofReal_inj.mpr
  have hne : cfg.upper.eta ≠ 0 := ne_of_gt cfg.upper.eta_pos
  field_simp [hne]

theorem etaL_powerWeight_lower (cfg : Config) :
    ((cfg.lower.eta : ℝ) : ℂ) * powerWeight cfg.lower = 1 := by
  unfold powerWeight
  rw [← Complex.ofReal_mul]
  apply Complex.ofReal_inj.mpr
  have hne : cfg.lower.eta ≠ 0 := ne_of_gt cfg.lower.eta_pos
  field_simp [hne]

theorem rescale_block_upper (cfg : Config) (M N P : Ten2)
    (h : (powerWeight cfg.upper) • M + (powerWeight cfg.lower) • N = P) :
    M + ((cfg.upper.eta / cfg.lower.eta : ℝ) : ℂ) • N = ((cfg.upper.eta : ℝ) : ℂ) • P := by
  have h' := congrArg (fun X : Ten2 => ((cfg.upper.eta : ℝ) : ℂ) • X) h
  rw [smul_add, smul_smul, smul_smul, etaU_powerWeight_upper cfg,
    etaU_powerWeight_lower cfg] at h'
  rw [one_smul] at h'
  exact h'

theorem rescale_block_lower (cfg : Config) (M N P : Ten2)
    (h : (powerWeight cfg.upper) • M + (powerWeight cfg.lower) • N = P) :
    ((cfg.lower.eta / cfg.upper.eta : ℝ) : ℂ) • M + N = ((cfg.lower.eta : ℝ) : ℂ) • P := by
  have h' := congrArg (fun X : Ten2 => ((cfg.lower.eta : ℝ) : ℂ) • X) h
  rw [smul_add, smul_smul, smul_smul, etaL_powerWeight_upper cfg,
    etaL_powerWeight_lower cfg] at h'
  rw [one_smul] at h'
  exact h'

theorem two_port_unitarity_11 (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hcons : S.Conservative cfg sus) :
    ten2Adjoint S.r1 * S.r1
      + ten2Adjoint (ScatteringMatrix.t21_norm cfg S) * (ScatteringMatrix.t21_norm cfg S) = 1 := by
  have hB := two_port_block_11 cfg sus S hk hloss hcons
  have hR := rescale_block_upper cfg (ten2Adjoint S.r1 * S.r1) (ten2Adjoint S.t21 * S.t21)
    ((powerWeight cfg.upper) • 1) hB
  have hnorm : ten2Adjoint (ScatteringMatrix.t21_norm cfg S)
      * (ScatteringMatrix.t21_norm cfg S)
      = ((cfg.upper.eta / cfg.lower.eta : ℝ) : ℂ) • (ten2Adjoint S.t21 * S.t21) := by
    rw [ScatteringMatrix.t21_norm, ten2Adjoint_smul, star_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      sqrt_ratio_sq_complex cfg.lower.eta cfg.upper.eta cfg.lower.eta_pos cfg.upper.eta_pos]
  rw [← hnorm] at hR
  have hRHS : ((cfg.upper.eta : ℝ) : ℂ) • ((powerWeight cfg.upper) • (1 : Ten2))
      = (1 : Ten2) := by
    rw [smul_smul, etaU_powerWeight_upper cfg, one_smul]
  rw [hRHS] at hR
  exact hR

theorem two_port_unitarity_12 (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hcons : S.Conservative cfg sus) :
    ten2Adjoint S.r1 * (ScatteringMatrix.t12_norm cfg S)
      + ten2Adjoint (ScatteringMatrix.t21_norm cfg S) * S.r2 = 0 := by
  have hB := two_port_block_12 cfg sus S hk hloss hcons
  have hR := rescale_block_upper cfg (ten2Adjoint S.r1 * S.t12) (ten2Adjoint S.t21 * S.r2)
    (0 : Ten2) hB
  have hc : ((Real.sqrt cfg.lower.eta / Real.sqrt cfg.upper.eta : ℝ) : ℂ)
      * ((cfg.upper.eta / cfg.lower.eta : ℝ) : ℂ)
      = ((Real.sqrt cfg.upper.eta / Real.sqrt cfg.lower.eta : ℝ) : ℂ) :=
    sqrt_ratio_mul_complex cfg.upper.eta cfg.lower.eta cfg.upper.eta_pos cfg.lower.eta_pos
  have hS := congrArg (fun X : Ten2 =>
      ((Real.sqrt cfg.lower.eta / Real.sqrt cfg.upper.eta : ℝ) : ℂ) • X) hR
  rw [smul_add, smul_smul] at hS
  rw [hc] at hS
  simp only [smul_zero] at hS
  rw [ScatteringMatrix.t12_norm, ScatteringMatrix.t21_norm, Matrix.mul_smul,
    ten2Adjoint_smul, star_ofReal, Matrix.smul_mul]
  exact hS

theorem two_port_unitarity_21 (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hcons : S.Conservative cfg sus) :
    ten2Adjoint (ScatteringMatrix.t12_norm cfg S) * S.r1
      + ten2Adjoint S.r2 * (ScatteringMatrix.t21_norm cfg S) = 0 := by
  have hB := two_port_block_21 cfg sus S hk hloss hcons
  have hR := rescale_block_upper cfg (ten2Adjoint S.t12 * S.r1) (ten2Adjoint S.r2 * S.t21)
    (0 : Ten2) hB
  have hc : ((Real.sqrt cfg.lower.eta / Real.sqrt cfg.upper.eta : ℝ) : ℂ)
      * ((cfg.upper.eta / cfg.lower.eta : ℝ) : ℂ)
      = ((Real.sqrt cfg.upper.eta / Real.sqrt cfg.lower.eta : ℝ) : ℂ) :=
    sqrt_ratio_mul_complex cfg.upper.eta cfg.lower.eta cfg.upper.eta_pos cfg.lower.eta_pos
  have hS := congrArg (fun X : Ten2 =>
      ((Real.sqrt cfg.lower.eta / Real.sqrt cfg.upper.eta : ℝ) : ℂ) • X) hR
  rw [smul_add, smul_smul] at hS
  rw [hc] at hS
  simp only [smul_zero] at hS
  rw [ScatteringMatrix.t12_norm, ScatteringMatrix.t21_norm, ten2Adjoint_smul, star_ofReal,
    Matrix.smul_mul, Matrix.mul_smul]
  exact hS

theorem two_port_unitarity_22 (cfg : Config) (sus : Susceptibilities)
    (S : ScatteringMatrix) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hcons : S.Conservative cfg sus) :
    ten2Adjoint (ScatteringMatrix.t12_norm cfg S) * (ScatteringMatrix.t12_norm cfg S)
      + ten2Adjoint S.r2 * S.r2 = 1 := by
  have hB := two_port_block_22 cfg sus S hk hloss hcons
  have hR := rescale_block_lower cfg (ten2Adjoint S.t12 * S.t12) (ten2Adjoint S.r2 * S.r2)
    ((powerWeight cfg.lower) • 1) hB
  have hnorm : ten2Adjoint (ScatteringMatrix.t12_norm cfg S)
      * (ScatteringMatrix.t12_norm cfg S)
      = ((cfg.lower.eta / cfg.upper.eta : ℝ) : ℂ) • (ten2Adjoint S.t12 * S.t12) := by
    rw [ScatteringMatrix.t12_norm, ten2Adjoint_smul, star_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      sqrt_ratio_sq_complex cfg.upper.eta cfg.lower.eta cfg.upper.eta_pos cfg.lower.eta_pos]
  rw [← hnorm] at hR
  have hRHS : ((cfg.lower.eta : ℝ) : ℂ) • ((powerWeight cfg.lower) • (1 : Ten2))
      = (1 : Ten2) := by
    rw [smul_smul, etaL_powerWeight_lower cfg, one_smul]
  rw [hRHS] at hR
  exact hR

theorem hPar_above_transmitted_eq_below_reflected (cfg : Config) (e : Vec2) :
    hPar cfg .above .transmitted e = hPar cfg .below .reflected e := by
  unfold hPar
  rfl

theorem jumpH_above_eq_hJump4 (cfg : Config) (a1 b1 b2 : Vec2) :
    jumpH cfg .above a1 b1 b2 = hJump4 cfg a1 b1 (0 : Vec2) b2 := by
  unfold jumpH hJump4 hAbove hBelow
  simp only [Side.jumpSign, one_smul]
  rw [hPar_above_transmitted_eq_below_reflected cfg b2]
  unfold hPar
  simp only [Matrix.mulVec_zero, smul_zero]
  abel

theorem eJump4_above (a1 b1 b2 : Vec2) :
    eJump4 a1 b1 (0 : Vec2) b2 = a1 + b1 - b2 := by
  unfold eJump4 eAbove eBelow
  funext i
  fin_cases i <;> simp

theorem gstcSatisfied4_above (cfg : Config) (sus : Susceptibilities)
    (a1 b1 b2 : Vec2) (hk : cfg.kPar = 0)
    (h : gstcSatisfied4 cfg sus a1 b1 (0 : Vec2) b2) :
    gstcSatisfied cfg .above sus a1 b1 b2 := by
  have hk' : (cfg.kPar : ℂ) = 0 := by exact_mod_cast hk
  constructor
  ·
    have h1 := h.1
    rw [eJump4_above a1 b1 b2] at h1
    have hsp : sheetMPar4 cfg sus a1 b1 (0 : Vec2) b2
        = sheetMPar cfg .above sus a1 b1 b2 := by
      rw [sheetMPar4_eq cfg sus a1 b1 (0 : Vec2) b2]
      simp
    rw [hsp] at h1
    rw [jumpE_above, h1]
    have hnorm : (Complex.I • ![(cfg.kPar : ℂ)
        * (sheetPNoverEps0 cfg .above sus a1 b1 b2), 0]) = 0 := by
      rw [hk', zero_mul]
      funext i
      fin_cases i <;> simp
    rw [hnorm]
    abel
  ·
    have h2 := h.2
    have hsp : sheetVPar4 cfg sus a1 b1 (0 : Vec2) b2
        = sheetVPar cfg .above sus a1 b1 b2 := by
      rw [sheetVPar4_eq cfg sus a1 b1 (0 : Vec2) b2]
      simp
    rw [hsp] at h2
    rw [jumpH_above_eq_hJump4 cfg a1 b1 b2, h2]
    have hnorm : (Complex.I • ![0, (cfg.kPar : ℂ)
        * (sheetWNoverMu0 cfg .above sus a1 b1 b2)]) = 0 := by
      rw [hk', zero_mul]
      funext i
      fin_cases i <;> simp
    rw [hnorm]
    abel

end GSTC.Scattering
