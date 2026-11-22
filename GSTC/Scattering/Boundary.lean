/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Coupling

open scoped Matrix

public section

namespace GSTC.Scattering

theorem smul_mulVec (a : ℂ) (M : Ten2) (v : Vec2) : (a • M) *ᵥ v = a • (M *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem colRow_mulVec (u : Vec2) (r : Row2) (v : Vec2) : colRow u r *ᵥ v = rowEval r v • u := by
  funext i
  fin_cases i <;>
    simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, colRow, rowEval,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk,
      Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem smul_vec_smul (a : ℂ) (u : Vec2) (x : ℂ) : a • (x • u) = (a • x) • u := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem smul_vec_add (a : ℂ) (u v : Vec2) : a • (u + v) = a • u + a • v := by
  funext i
  simp only [Pi.smul_apply, Pi.add_apply]
  ring

theorem smul_vec_sub (a : ℂ) (u v : Vec2) : a • (u - v) = a • u - a • v := by
  funext i
  simp only [Pi.smul_apply, Pi.sub_apply]
  ring

theorem neg_smul_vec (a : ℂ) (u : Vec2) : -(a • u) = (-a) • u := by
  funext i
  simp only [Pi.neg_apply, Pi.smul_apply]
  ring

theorem realCast_one : ((1 : ℝ) : ℂ) = 1 := by norm_num

theorem realCast_neg_one : ((-1 : ℝ) : ℂ) = -1 := by norm_num

theorem ncross_mul_ncross (v : Vec2) : ncross *ᵥ (ncross *ᵥ v) = -v := by
  simp only [ncross_apply]
  funext i
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.neg_apply]

theorem ncross_sq' : ncross * ncross = -(1 : Ten2) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [ncross, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.neg_apply, Matrix.one_apply_eq]
  · simp [ncross, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.neg_apply]
  · simp [ncross, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.neg_apply]
  · simp [ncross, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.neg_apply, Matrix.one_apply_eq]

theorem ncross_sq (M : Ten2) : ncross * (ncross * M) = -M := by
  rw [← Matrix.mul_assoc, ncross_sq', Matrix.neg_mul, Matrix.one_mul]

theorem ncross_hPar (cfg : Config) (s : Side) (w : Wave) (e : Vec2) :
    ncross *ᵥ hPar cfg s w e
      = -((PropDir.sign (Wave.dir s w) : ℂ)) • (waveY (Wave.medium cfg s w) cfg.kPar *ᵥ e) := by
  have h1 : ncross *ᵥ (ncross *ᵥ (waveY (Wave.medium cfg s w) cfg.kPar *ᵥ e))
      = -(waveY (Wave.medium cfg s w) cfg.kPar *ᵥ e) := ncross_mul_ncross _
  have h2 : ncross *ᵥ ((ncross * waveY (Wave.medium cfg s w) cfg.kPar) *ᵥ e)
      = ncross *ᵥ (ncross *ᵥ (waveY (Wave.medium cfg s w) cfg.kPar *ᵥ e)) := by
    rw [← Matrix.mulVec_mulVec]
  rw [hPar, Matrix.mulVec_smul, h2, h1, smul_neg, neg_smul]

@[expose] def waveSideSign (s : Side) (w : Wave) : ℂ :=
  match s, w with
  | .above, .incident => 1
  | .above, .reflected => 1
  | .above, .transmitted => -1
  | .below, .incident => -1
  | .below, .reflected => -1
  | .below, .transmitted => 1

theorem waveSideSign_incident (s : Side) : waveSideSign s .incident = Side.jumpSign s := by
  cases s <;> rfl

theorem waveSideSign_reflected (s : Side) : waveSideSign s .reflected = Side.jumpSign s := by
  cases s <;> rfl

theorem waveSideSign_transmitted (s : Side) :
    waveSideSign s .transmitted = -(Side.jumpSign s) := by
  cases s <;> simp [waveSideSign, Side.jumpSign]

@[expose] def waveYsign (s : Side) (w : Wave) : ℂ :=
  waveSideSign s w * (-((PropDir.sign (Wave.dir s w) : ℂ)))

theorem waveYsign_incident (s : Side) : waveYsign s .incident = 1 := by
  cases s <;>
    simp only [waveYsign, waveSideSign, Wave.dir, PropDir.sign,
      realCast_one, realCast_neg_one] <;>
    ring

theorem waveYsign_reflected (s : Side) : waveYsign s .reflected = -1 := by
  cases s <;>
    simp only [waveYsign, waveSideSign, Wave.dir, PropDir.sign,
      realCast_one, realCast_neg_one] <;>
    ring

theorem waveYsign_transmitted (s : Side) : waveYsign s .transmitted = -1 := by
  cases s <;>
    simp only [waveYsign, waveSideSign, Wave.dir, PropDir.sign,
      realCast_one, realCast_neg_one] <;>
    ring

theorem waveYsign_incident_eq (s : Side) :
    (Side.jumpSign s) * (-((PropDir.sign (Wave.dir s .incident) : ℂ))) = waveYsign s .incident := by
  rw [waveYsign, waveSideSign_incident]

theorem waveYsign_reflected_eq (s : Side) :
    (Side.jumpSign s) * (-((PropDir.sign (Wave.dir s .reflected) : ℂ))) = waveYsign s .reflected := by
  rw [waveYsign, waveSideSign_reflected]

theorem waveYsign_transmitted_eq (s : Side) :
    (-(Side.jumpSign s)) * (-((PropDir.sign (Wave.dir s .transmitted) : ℂ)))
      = waveYsign s .transmitted := by
  rw [waveYsign, waveSideSign_transmitted]

@[expose] noncomputable def sheetMPar (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) : Vec2 :=
  couplingWPar cfg s sus .incident *ᵥ eI + couplingWPar cfg s sus .reflected *ᵥ eR
    + couplingWPar cfg s sus .transmitted *ᵥ eT

@[expose] noncomputable def sheetPNoverEps0 (cfg : Config) (s : Side)
    (sus : Susceptibilities) (eI eR eT : Vec2) : ℂ :=
  (1 / (cfg.vac.eps0 : ℂ)) * (rowEval (couplingVN cfg s sus .incident) eI
    + rowEval (couplingVN cfg s sus .reflected) eR
    + rowEval (couplingVN cfg s sus .transmitted) eT)

@[expose] noncomputable def sheetVPar (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) : Vec2 :=
  couplingVPar cfg s sus .incident *ᵥ eI + couplingVPar cfg s sus .reflected *ᵥ eR
    + couplingVPar cfg s sus .transmitted *ᵥ eT

@[expose] noncomputable def sheetWNoverMu0 (cfg : Config) (s : Side)
    (sus : Susceptibilities) (eI eR eT : Vec2) : ℂ :=
  (1 / (cfg.vac.mu0 : ℂ)) * (rowEval (couplingWN cfg s sus .incident) eI
    + rowEval (couplingWN cfg s sus .reflected) eR
    + rowEval (couplingWN cfg s sus .transmitted) eT)

@[expose] def jumpE (s : Side) (eI eR eT : Vec2) : Vec2 :=
  Side.jumpSign s • (eI + eR - eT)

@[expose] noncomputable def jumpH (cfg : Config) (s : Side) (eI eR eT : Vec2) : Vec2 :=
  Side.jumpSign s • (hPar cfg s .incident eI + hPar cfg s .reflected eR
    - hPar cfg s .transmitted eT)

structure BoundaryCoeffs where
  beI : Ten2
  beR : Ten2
  beT : Ten2
  bhI : Ten2
  bhR : Ten2
  bhT : Ten2

@[expose] noncomputable def boundaryCoeffs (cfg : Config) (s : Side)
    (sus : Susceptibilities) : BoundaryCoeffs :=
  { beI :=
      Side.jumpSign s • iPar
        - (Complex.I * (cfg.omega : ℂ)) • (ncross * couplingWPar cfg s sus .incident)
        - (Complex.I • ((1 / (cfg.vac.eps0 : ℂ))
            • colRow (kVec cfg.kPar) (couplingVN cfg s sus .incident)))
    beR :=
      Side.jumpSign s • iPar
        - (Complex.I * (cfg.omega : ℂ)) • (ncross * couplingWPar cfg s sus .reflected)
        - (Complex.I • ((1 / (cfg.vac.eps0 : ℂ))
            • colRow (kVec cfg.kPar) (couplingVN cfg s sus .reflected)))
    beT :=
      -(Side.jumpSign s) • iPar
        - (Complex.I * (cfg.omega : ℂ)) • (ncross * couplingWPar cfg s sus .transmitted)
        - (Complex.I • ((1 / (cfg.vac.eps0 : ℂ))
            • colRow (kVec cfg.kPar) (couplingVN cfg s sus .transmitted)))
    bhI :=
      waveY (Wave.medium cfg s .incident) cfg.kPar
        - (Complex.I * (cfg.omega : ℂ)) • (couplingVPar cfg s sus .incident)
        - (Complex.I • ((1 / (cfg.vac.mu0 : ℂ))
            • colRow (lVec cfg.kPar) (couplingWN cfg s sus .incident)))
    bhR :=
      -(waveY (Wave.medium cfg s .incident) cfg.kPar)
        - (Complex.I * (cfg.omega : ℂ)) • (couplingVPar cfg s sus .reflected)
        - (Complex.I • ((1 / (cfg.vac.mu0 : ℂ))
            • colRow (lVec cfg.kPar) (couplingWN cfg s sus .reflected)))
    bhT :=
      -(waveY (Wave.medium cfg s .transmitted) cfg.kPar)
        - (Complex.I * (cfg.omega : ℂ)) • (couplingVPar cfg s sus .transmitted)
        - (Complex.I • ((1 / (cfg.vac.mu0 : ℂ))
            • colRow (lVec cfg.kPar) (couplingWN cfg s sus .transmitted))) }

@[expose] noncomputable def gstcSatisfied (cfg : Config) (s : Side)
    (sus : Susceptibilities) (eI eR eT : Vec2) : Prop :=
  (jumpE s eI eR eT =
      (Complex.I * (cfg.omega : ℂ)) • (ncross *ᵥ (sheetMPar cfg s sus eI eR eT))
        + (Complex.I • ![(cfg.kPar : ℂ) * (sheetPNoverEps0 cfg s sus eI eR eT), 0]))
  ∧ (ncross *ᵥ (jumpH cfg s eI eR eT) =
      (Complex.I * (cfg.omega : ℂ)) • (sheetVPar cfg s sus eI eR eT)
        + (Complex.I • ![0, (cfg.kPar : ℂ) * (sheetWNoverMu0 cfg s sus eI eR eT)]))

theorem waveY_reflected_eq_incident (cfg : Config) (s : Side) :
    waveY (Wave.medium cfg s .reflected) cfg.kPar = waveY (Wave.medium cfg s .incident) cfg.kPar := by
  cases s <;> rfl

theorem one_smul_ten2 (M : Ten2) : (1 : ℂ) • M = M := by
  ext i j
  simp [Matrix.smul_apply]

theorem neg_one_smul_ten2 (M : Ten2) : (-1 : ℂ) • M = -M := by
  ext i j
  simp [Matrix.smul_apply]

theorem boundaryCoeffs_magnetic_Ysign (cfg : Config) (s : Side) (sus : Susceptibilities) :
    (boundaryCoeffs cfg s sus).bhI
        = waveYsign s .incident • waveY (Wave.medium cfg s .incident) cfg.kPar
          - (Complex.I * (cfg.omega : ℂ)) • couplingVPar cfg s sus .incident
          - (Complex.I • ((1 / (cfg.vac.mu0 : ℂ))
              • colRow (lVec cfg.kPar) (couplingWN cfg s sus .incident)))
    ∧ (boundaryCoeffs cfg s sus).bhR
        = waveYsign s .reflected • waveY (Wave.medium cfg s .reflected) cfg.kPar
          - (Complex.I * (cfg.omega : ℂ)) • couplingVPar cfg s sus .reflected
          - (Complex.I • ((1 / (cfg.vac.mu0 : ℂ))
              • colRow (lVec cfg.kPar) (couplingWN cfg s sus .reflected)))
    ∧ (boundaryCoeffs cfg s sus).bhT
        = waveYsign s .transmitted • waveY (Wave.medium cfg s .transmitted) cfg.kPar
          - (Complex.I * (cfg.omega : ℂ)) • couplingVPar cfg s sus .transmitted
          - (Complex.I • ((1 / (cfg.vac.mu0 : ℂ))
              • colRow (lVec cfg.kPar) (couplingWN cfg s sus .transmitted))) := by
  refine ⟨?_, ?_⟩
  · simp only [boundaryCoeffs]
    rw [waveYsign_incident, one_smul_ten2]
  · refine ⟨?_, ?_⟩
    · simp only [boundaryCoeffs]
      rw [waveYsign_reflected, neg_one_smul_ten2, ← waveY_reflected_eq_incident]
    · simp only [boundaryCoeffs]
      rw [waveYsign_transmitted, neg_one_smul_ten2]

theorem ncross_jumpH (cfg : Config) (s : Side) (eI eR eT : Vec2) :
    ncross *ᵥ (jumpH cfg s eI eR eT)
      = (waveYsign s .incident) • (waveY (Wave.medium cfg s .incident) cfg.kPar *ᵥ eI)
        + (waveYsign s .reflected) • (waveY (Wave.medium cfg s .reflected) cfg.kPar *ᵥ eR)
        + (waveYsign s .transmitted) • (waveY (Wave.medium cfg s .transmitted) cfg.kPar *ᵥ eT) := by
  simp only [jumpH, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_sub,
    ncross_hPar]
  simp only [smul_vec_add, smul_vec_sub]
  rw [sub_eq_add_neg, neg_smul_vec]
  simp only [smul_vec_smul, smul_eq_mul]
  rw [waveYsign_incident_eq, waveYsign_reflected_eq, waveYsign_transmitted_eq]

theorem boundaryCoeffs_electric (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) :
    (boundaryCoeffs cfg s sus).beI *ᵥ eI + (boundaryCoeffs cfg s sus).beR *ᵥ eR
      + (boundaryCoeffs cfg s sus).beT *ᵥ eT
    = jumpE s eI eR eT
      - (Complex.I * (cfg.omega : ℂ)) • (ncross *ᵥ (sheetMPar cfg s sus eI eR eT))
      - (Complex.I • ![(cfg.kPar : ℂ) * (sheetPNoverEps0 cfg s sus eI eR eT), 0]) := by
  simp only [boundaryCoeffs, Matrix.sub_mulVec, smul_mulVec, colRow_mulVec,
    smul_vec_smul, iPar_mulVec, jumpE, sheetMPar, sheetPNoverEps0,
    Matrix.mulVec_add]
  simp only [← Matrix.mulVec_mulVec]
  funext i
  fin_cases i <;>
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, smul_eq_mul, rowEval,
      ncross_apply, kVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.reduceFinMk] <;>
    ring

theorem boundaryCoeffs_magnetic (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) :
    (boundaryCoeffs cfg s sus).bhI *ᵥ eI + (boundaryCoeffs cfg s sus).bhR *ᵥ eR
      + (boundaryCoeffs cfg s sus).bhT *ᵥ eT
    = ncross *ᵥ (jumpH cfg s eI eR eT)
      - (Complex.I * (cfg.omega : ℂ)) • (sheetVPar cfg s sus eI eR eT)
      - (Complex.I • ![0, (cfg.kPar : ℂ) * (sheetWNoverMu0 cfg s sus eI eR eT)]) := by
  have hY := boundaryCoeffs_magnetic_Ysign cfg s sus
  rw [hY.1, hY.2.1, hY.2.2]
  rw [ncross_jumpH]
  simp only [Matrix.sub_mulVec, smul_mulVec, colRow_mulVec, smul_vec_smul,
    sheetVPar, sheetWNoverMu0]
  funext i
  fin_cases i <;>
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, smul_eq_mul, rowEval,
      lVec, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] <;>
    ring

theorem wave_below_reflected_eq_above_transmitted (cfg : Config) :
    Wave.dir .below .reflected = Wave.dir .above .transmitted ∧
      Wave.medium cfg .below .reflected = Wave.medium cfg .above .transmitted :=
  ⟨rfl, rfl⟩

end GSTC.Scattering
