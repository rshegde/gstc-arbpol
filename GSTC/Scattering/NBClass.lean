/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.MagneticOnly
public import GSTC.Scattering.Reciprocity

public section

namespace GSTC.Scattering

open scoped Matrix
open scoped ComplexConjugate

@[expose] def nbClass (sus : Susceptibilities) : Prop :=
  chiTT sus.em = 0 ∧ chiTT sus.me = 0

@[expose] def nbSheet (A B : Ten2) : Susceptibilities where
  ee := ten3OfTT A
  mm := ten3OfTT B
  em := 0
  me := 0

theorem nbSheet_chiTT_ee (A B : Ten2) : chiTT (nbSheet A B).ee = A := by
  rw [nbSheet, chiTT_ten3OfTT]

theorem nbSheet_chiTT_mm (A B : Ten2) : chiTT (nbSheet A B).mm = B := by
  rw [nbSheet, chiTT_ten3OfTT]

theorem nbSheet_chiTT_em (A B : Ten2) : chiTT (nbSheet A B).em = 0 := by
  rw [nbSheet, chiTT_zero]

theorem nbSheet_chiTT_me (A B : Ten2) : chiTT (nbSheet A B).me = 0 := by
  rw [nbSheet, chiTT_zero]

theorem nbSheet_nbClass (A B : Ten2) : nbClass (nbSheet A B) := by
  exact ⟨nbSheet_chiTT_em A B, nbSheet_chiTT_me A B⟩

theorem nbSheet_lossless (A B : Ten2)
    (hA : ∀ i j, A i j = star (A j i)) (hB : ∀ i j, B i j = star (B j i)) :
    (nbSheet A B).Lossless := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [nbSheet, ten3OfTT] <;>
      first
        | exact hA 0 0
        | exact hA 0 1
        | exact hA 1 0
        | exact hA 1 1
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [nbSheet, ten3OfTT] <;>
      first
        | exact hB 0 0
        | exact hB 0 1
        | exact hB 1 0
        | exact hB 1 1
  · intro i j
    rw [nbSheet]
    simp

theorem nbSheet_reciprocal (A B : Ten2)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i) :
    (nbSheet A B).Reciprocal := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [nbSheet, ten3OfTT, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      first
        | exact hA 0 1
        | exact (hA 0 1).symm
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [nbSheet, ten3OfTT, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      first
        | exact hB 0 1
        | exact (hB 0 1).symm
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [nbSheet]

theorem sign_incident_mul_jumpSign (s : Side) :
    (PropDir.sign (Wave.dir s .incident) : ℂ) * (Side.jumpSign s) = -1 := by
  cases s <;> simp [PropDir.sign, Wave.dir, Side.jumpSign]

theorem sign_incident_sq (s : Side) :
    (PropDir.sign (Wave.dir s .incident) : ℂ) * (PropDir.sign (Wave.dir s .incident) : ℂ)
      = 1 := by
  cases s <;> simp [PropDir.sign, Wave.dir]

theorem sign_absorption (σ j ω μ₀ ηinv w x : ℂ)
    (hj : σ * j = -1) (hσ2 : σ * σ = 1)
    (h : j * w = (Complex.I * ω * ((1 / 2) * (μ₀ * (σ * ηinv)))) * x) :
    w = -((Complex.I * ω * ((1 / 2) * (μ₀ * ηinv))) * x) := by
  have h1 : σ * (j * w) = σ * ((Complex.I * ω * ((1 / 2) * (μ₀ * (σ * ηinv)))) * x) := by
    rw [h]
  have h2 : -w = σ * (j * w) := by
    calc -w = (σ * j) * w := by rw [hj]; ring
      _ = σ * (j * w) := by ring
  have h3 : σ * ((Complex.I * ω * ((1 / 2) * (μ₀ * (σ * ηinv)))) * x)
      = (Complex.I * ω * ((1 / 2) * (μ₀ * ηinv))) * x := by
    calc σ * ((Complex.I * ω * ((1 / 2) * (μ₀ * (σ * ηinv)))) * x)
        = (σ * σ) * ((Complex.I * ω * ((1 / 2) * (μ₀ * ηinv))) * x) := by ring
      _ = _ := by simp [hσ2]
  calc w = -(-w) := by ring
    _ = -(σ * (j * w)) := by rw [h2]
    _ = -(σ * ((Complex.I * ω * ((1 / 2) * (μ₀ * (σ * ηinv)))) * x)) := by rw [h1]
    _ = -((Complex.I * ω * ((1 / 2) * (μ₀ * ηinv))) * x) := by rw [h3]

theorem sign_jumpSign_neg (s : Side) :
    Side.jumpSign s = -(PropDir.sign (Wave.dir s .incident) : ℂ) := by
  have h1 := sign_incident_mul_jumpSign s
  have h2 := sign_incident_sq s
  have h1' : (Side.jumpSign s) * (PropDir.sign (Wave.dir s .incident) : ℂ) = -1 := by
    calc (Side.jumpSign s) * (PropDir.sign (Wave.dir s .incident) : ℂ)
        = (PropDir.sign (Wave.dir s .incident) : ℂ) * (Side.jumpSign s) := by ring
      _ = -1 := h1
  calc Side.jumpSign s = Side.jumpSign s * 1 := by ring
    _ = Side.jumpSign s
        * ((PropDir.sign (Wave.dir s .incident) : ℂ)
          * (PropDir.sign (Wave.dir s .incident) : ℂ)) := by rw [h2]
    _ = ((Side.jumpSign s) * (PropDir.sign (Wave.dir s .incident) : ℂ))
        * (PropDir.sign (Wave.dir s .incident) : ℂ) := by ring
    _ = -((PropDir.sign (Wave.dir s .incident) : ℂ)) := by rw [h1']; ring

theorem nb_action (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0)
    (hem : chiTT sus.em = 0) (hme : chiTT sus.me = 0)
    (hmed : identicalMedia cfg s)
    (hgstc : gstcSatisfied cfg s sus eI eR eT) :
    eI - eR - eT
        = eoResponseScale cfg ((Wave.medium cfg s .incident).eta)
          • ((chiTT sus.ee) *ᵥ (eI + eR + eT))
      ∧ eI + eR - eT
        = moResponseScale cfg ((Wave.medium cfg s .incident).eta)
          • ((ncross * (chiTT sus.mm * ncross)) *ᵥ (eI - eR + eT)) := by
  have hconj := (gstc_normal cfg s sus eI eR eT hk).mp hgstc
  constructor
  ·
    have hJ := jumpH_normal_E_identical cfg s eI eR eT hk hmed
    have hV := electricOnly_sheetVPar cfg s sus eI eR eT hk hem
    have h2 := hconj.2
    rw [hJ, hV] at h2
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    have h2i := congrArg (fun v : Vec2 => v i) h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2i
    have hη : ((Wave.medium cfg s .incident).eta : ℂ) ≠ 0 := by
      exact_mod_cast (Wave.medium cfg s .incident).eta_pos.ne'
    calc (eI - eR - eT) i
        = ((Wave.medium cfg s .incident).eta : ℂ)
            * ((1 / ((Wave.medium cfg s .incident).eta : ℂ)) * ((eI - eR - eT) i)) := by
              rw [one_div, ← mul_assoc, mul_inv_cancel₀ hη, one_mul]
        _ = ((Wave.medium cfg s .incident).eta : ℂ)
            * (Complex.I * (cfg.omega : ℂ)
                * (((1 / 2) * (cfg.vac.eps0 : ℂ))
                  * ((chiTT sus.ee) *ᵥ (eI + eR + eT)) i)) := by rw [h2i]
        _ = eoResponseScale cfg ((Wave.medium cfg s .incident).eta)
            * ((chiTT sus.ee) *ᵥ (eI + eR + eT)) i := by
              unfold eoResponseScale
              ring
  ·
    have hM := magneticOnly_sheetMPar cfg s sus eI eR eT hk hme hmed
    have h1 := hconj.1
    rw [jumpE_eq, hM, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at h1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1i := congrArg (fun v : Vec2 => v i) h1
    simp only [Pi.smul_apply, smul_eq_mul, eJumpRaw] at h1i
    have h1i' : s.jumpSign * (eI + eR - eT) i
        = (Complex.I * (cfg.omega : ℂ)
            * ((1 / 2) * ((cfg.vac.mu0 : ℂ)
                * ((PropDir.sign (Wave.dir s .incident) : ℂ)
                  * (1 / ((Wave.medium cfg s .incident).eta : ℂ))))))
          * ((ncross * (chiTT sus.mm * ncross)) *ᵥ (eI - eR + eT)) i := by
      rw [h1i]
      ring
    have h3 := sign_absorption (PropDir.sign (Wave.dir s .incident) : ℂ) (Side.jumpSign s)
      (cfg.omega : ℂ) (cfg.vac.mu0 : ℂ)
      (1 / ((Wave.medium cfg s .incident).eta : ℂ))
      ((eI + eR - eT) i)
      (((ncross * (chiTT sus.mm * ncross)) *ᵥ (eI - eR + eT)) i)
      (sign_incident_mul_jumpSign s) (sign_incident_sq s) h1i'
    rw [h3]
    unfold moResponseScale
    ring

theorem nb_action_implies_gstc (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0)
    (hem : chiTT sus.em = 0) (hme : chiTT sus.me = 0)
    (hmed : identicalMedia cfg s)
    (hR : eI - eR - eT
        = eoResponseScale cfg ((Wave.medium cfg s .incident).eta)
          • ((chiTT sus.ee) *ᵥ (eI + eR + eT)))
    (hM : eI + eR - eT
        = moResponseScale cfg ((Wave.medium cfg s .incident).eta)
          • ((ncross * (chiTT sus.mm * ncross)) *ᵥ (eI - eR + eT))) :
    gstcSatisfied cfg s sus eI eR eT := by
  rw [gstc_normal cfg s sus eI eR eT hk]
  constructor
  ·
    have hMpar := magneticOnly_sheetMPar cfg s sus eI eR eT hk hme hmed
    have hj := sign_jumpSign_neg s
    rw [jumpE_eq, hMpar, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, eJumpRaw]
    have hMi := congrArg (fun v : Vec2 => v i) hM
    simp only [Pi.smul_apply, smul_eq_mul] at hMi
    rw [hMi, hj]
    unfold moResponseScale
    ring
  ·
    have hV := electricOnly_sheetVPar cfg s sus eI eR eT hk hem
    have hJ := jumpH_normal_E_identical cfg s eI eR eT hk hmed
    rw [hJ, hV]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    have hRi := congrArg (fun v : Vec2 => v i) hR
    simp only [Pi.smul_apply, smul_eq_mul] at hRi
    rw [hRi]
    unfold eoResponseScale
    have hη : ((Wave.medium cfg s .incident).eta : ℂ) ≠ 0 := by
      exact_mod_cast (Wave.medium cfg s .incident).eta_pos.ne'
    field_simp [hη]

end GSTC.Scattering
