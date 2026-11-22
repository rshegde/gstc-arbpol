/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Reduction

open scoped Matrix

public section

namespace GSTC.Scattering

theorem kVec_zero : kVec 0 = 0 := by
  funext i; fin_cases i <;> rfl

theorem lVec_zero : lVec 0 = 0 := by
  funext i; fin_cases i <;> rfl

@[expose] noncomputable def couplingVParNormal (cfg : Config) (s : Side)
    (sus : Susceptibilities) (w : Wave) : Ten2 :=
  (1 / 2 : ℂ) • ((cfg.vac.eps0 : ℂ) • (chiTT sus.ee)
      + (1 / (cfg.vac.c0 : ℂ)) • ((PropDir.sign (Wave.dir s w) : ℂ)
          • (chiTT sus.em * (ncross * waveY (Wave.medium cfg s w) 0))))

@[expose] noncomputable def couplingWParNormal (cfg : Config) (s : Side)
    (sus : Susceptibilities) (w : Wave) : Ten2 :=
  (1 / 2 : ℂ) • ((1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.me)
      + (cfg.vac.mu0 : ℂ) • ((PropDir.sign (Wave.dir s w) : ℂ)
          • (chiTT sus.mm * (ncross * waveY (Wave.medium cfg s w) 0))))

theorem couplingVPar_eq_normal (cfg : Config) (s : Side)
    (sus : Susceptibilities) (w : Wave) (hk : cfg.kPar = 0) :
    couplingVPar cfg s sus w = couplingVParNormal cfg s sus w := by
  unfold couplingVPar couplingVParNormal
  rw [hk]
  rw [kVec_zero, lVec_zero]
  rw [outer_zero_right (chiTN sus.ee), outer_zero_right (chiTN sus.em)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Matrix.zero_apply, mul_zero, add_zero]

theorem couplingWPar_eq_normal (cfg : Config) (s : Side)
    (sus : Susceptibilities) (w : Wave) (hk : cfg.kPar = 0) :
    couplingWPar cfg s sus w = couplingWParNormal cfg s sus w := by
  unfold couplingWPar couplingWParNormal
  rw [hk]
  rw [kVec_zero, lVec_zero]
  rw [outer_zero_right (chiTN sus.me), outer_zero_right (chiTN sus.mm)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Matrix.zero_apply, mul_zero, add_zero]

@[expose] noncomputable def boundaryCoeffsNormal (cfg : Config) (s : Side)
    (sus : Susceptibilities) : BoundaryCoeffs :=
  { beI :=
      Side.jumpSign s • iPar
        - (Complex.I * (cfg.omega : ℂ)) • (ncross * couplingWParNormal cfg s sus .incident)
    beR :=
      Side.jumpSign s • iPar
        - (Complex.I * (cfg.omega : ℂ)) • (ncross * couplingWParNormal cfg s sus .reflected)
    beT :=
      -(Side.jumpSign s) • iPar
        - (Complex.I * (cfg.omega : ℂ)) • (ncross * couplingWParNormal cfg s sus .transmitted)
    bhI :=
      waveY (Wave.medium cfg s .incident) 0
        - (Complex.I * (cfg.omega : ℂ)) • (couplingVParNormal cfg s sus .incident)
    bhR :=
      -(waveY (Wave.medium cfg s .incident) 0)
        - (Complex.I * (cfg.omega : ℂ)) • (couplingVParNormal cfg s sus .reflected)
    bhT :=
      -(waveY (Wave.medium cfg s .transmitted) 0)
        - (Complex.I * (cfg.omega : ℂ)) • (couplingVParNormal cfg s sus .transmitted) }

theorem boundaryCoeffs_eq_normal (cfg : Config) (s : Side)
    (sus : Susceptibilities) (hk : cfg.kPar = 0) :
    boundaryCoeffs cfg s sus = boundaryCoeffsNormal cfg s sus := by
  have hcV := couplingVPar_eq_normal cfg s sus .incident hk
  have hcV' := couplingVPar_eq_normal cfg s sus .reflected hk
  have hcV'' := couplingVPar_eq_normal cfg s sus .transmitted hk
  have hcW := couplingWPar_eq_normal cfg s sus .incident hk
  have hcW' := couplingWPar_eq_normal cfg s sus .reflected hk
  have hcW'' := couplingWPar_eq_normal cfg s sus .transmitted hk
  unfold boundaryCoeffs boundaryCoeffsNormal
  rw [hk]
  rw [kVec_zero, lVec_zero]
  rw [hcV, hcV', hcV'', hcW, hcW', hcW'']
  simp only [colRow_zero_left]
  simp only [BoundaryCoeffs.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (ext i j)
  all_goals (simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply])
  all_goals ring

private theorem fluxP_zero (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) :
    (Complex.I • ![(↑(0 : ℝ) : ℂ) * (sheetPNoverEps0 cfg s sus eI eR eT), 0]) = 0 := by
  funext i
  fin_cases i <;> simp [Pi.smul_apply]

private theorem fluxW_zero (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) :
    (Complex.I • ![0, (↑(0 : ℝ) : ℂ) * (sheetWNoverMu0 cfg s sus eI eR eT)]) = 0 := by
  funext i
  fin_cases i <;> simp [Pi.smul_apply]

theorem gstc_normal (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) :
    gstcSatisfied cfg s sus eI eR eT
      ↔ (jumpE s eI eR eT
            = (Complex.I * (cfg.omega : ℂ)) • (ncross *ᵥ (sheetMPar cfg s sus eI eR eT))
          ∧ ncross *ᵥ (jumpH cfg s eI eR eT)
            = (Complex.I * (cfg.omega : ℂ)) • (sheetVPar cfg s sus eI eR eT)) := by
  simp only [gstcSatisfied]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hk] at h1 h2
    constructor
    · have hz := fluxP_zero cfg s sus eI eR eT
      rw [hz] at h1
      simpa using h1
    · have hz := fluxW_zero cfg s sus eI eR eT
      rw [hz] at h2
      simpa using h2
  · rintro ⟨h1, h2⟩
    rw [hk]
    constructor
    · have hz := fluxP_zero cfg s sus eI eR eT
      rw [hz]
      simpa using h1
    · have hz := fluxW_zero cfg s sus eI eR eT
      rw [hz]
      simpa using h2

@[expose] def ten3OfTT (c : Ten2) : Ten3 :=
  !![c 0 0, c 0 1, 0; c 1 0, c 1 1, 0; 0, 0, 0]

theorem chiTT_ten3OfTT (c : Ten2) : chiTT (ten3OfTT c) = c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ten3OfTT, chiTT, Matrix.cons_val_zero, Matrix.cons_val_one]

end GSTC.Scattering
