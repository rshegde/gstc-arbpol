/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.SusceptibilityBudget

public section

set_option autoImplicit false

namespace GSTC.Scattering.RotatedRankOneResources

open SusceptibilityBudget SpectralMatrixSupport MaterialSpace ClassFeasibility
open scoped Matrix

@[expose] noncomputable def rotS (a b : ℝ) : ℝ :=
  Real.sqrt ((1 - a) * (1 + b) / ((1 + a) * (1 - b)))

@[expose] noncomputable def rotR (s : ℝ) : ℝ := Real.sqrt (1 - s ^ 2)

@[expose] def rotF (s c x y : ℝ) : ℝ := (1 + s) * (x + c) ^ 2 - (1 - s) * y ^ 2

structure RotScalars where
  p0 : ℝ
  p1 : ℝ
  t : ℝ
  u : ℝ
  w : ℝ
  q : ℝ

@[expose] noncomputable def rotP0 (s c x y : ℝ) : ℝ :=
  2 * y * (2 * x + (1 + s) * c) / rotF s c x y

@[expose] noncomputable def rotP1 (s c x y : ℝ) : ℝ :=
  2 * (1 - s) * y / rotF s c x y

@[expose] noncomputable def rotT (s r c x y : ℝ) : ℝ :=
  2 * r * (x + c) / rotF s c x y

@[expose] noncomputable def rotU (s r c x y : ℝ) : ℝ :=
  2 * r * (1 + c * x) / rotF s c x y

@[expose] noncomputable def rotW (s r c j x y : ℝ) : ℝ :=
  2 * r * j * y / rotF s c x y

@[expose] noncomputable def rotQ (s c j x y : ℝ) : ℝ :=
  2 * j * (1 + s) * (x + c) / rotF s c x y

@[expose] noncomputable def rotScalars (s r c j x y : ℝ) : RotScalars :=
  { p0 := rotP0 s c x y
    p1 := rotP1 s c x y
    t := rotT s r c x y
    u := rotU s r c x y
    w := rotW s r c j x y
    q := rotQ s c j x y }

@[expose] noncomputable def rotDirect (sc : RotScalars) (v : ℝ) : ℝ :=
  max (|sc.p0 + sc.t * v| + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)))
    (|sc.p0 - sc.t * v| + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)))

@[expose] noncomputable def rotCoupling (sc : RotScalars) (v : ℝ) : ℝ :=
  Real.sqrt (sc.t ^ 2 * (1 - v ^ 2) + sc.q ^ 2) + Real.sqrt (sc.t ^ 2 * (1 - v ^ 2) + sc.w ^ 2)

@[expose] noncomputable def rotElectricBlock (sc : RotScalars) (v : ℝ) : Mat :=
  let z := Real.sqrt (1 - v ^ 2)
  !![-(sc.p0 + sc.t * v) + (sc.p1 + sc.u * v), sc.w * z;
    sc.w * z, -(sc.p0 + sc.t * v) - (sc.p1 + sc.u * v)]

@[expose] noncomputable def rotMagneticBlock (sc : RotScalars) (v : ℝ) : Mat :=
  let z := Real.sqrt (1 - v ^ 2)
  !![-(sc.p0 - sc.t * v) + (sc.p1 - sc.u * v), sc.w * z;
    sc.w * z, -(sc.p0 - sc.t * v) - (sc.p1 - sc.u * v)]

@[expose] noncomputable def rotCouplingBlock (sc : RotScalars) (v : ℝ) : Mat :=
  let z := Real.sqrt (1 - v ^ 2)
  let a := sc.t * z
  let c2 := Real.sqrt (a ^ 2 + sc.w ^ 2)
  !![-sc.q + c2, -a; a, -sc.q - c2]

@[expose] noncomputable def rotSheet (sc : RotScalars) (v : ℝ) : MaterialCoordinates :=
  coordinatesOfBlocks (rotElectricBlock sc v) (rotMagneticBlock sc v) (rotCouplingBlock sc v)

theorem rotElectricBlock_symmetric (sc : RotScalars) (v : ℝ) :
    (rotElectricBlock sc v).transpose = rotElectricBlock sc v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotElectricBlock]

theorem rotMagneticBlock_symmetric (sc : RotScalars) (v : ℝ) :
    (rotMagneticBlock sc v).transpose = rotMagneticBlock sc v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMagneticBlock]

theorem rotSheet_blocks (sc : RotScalars) (v : ℝ) :
    electricBlock (rotSheet sc v) = rotElectricBlock sc v ∧
      magneticBlock (rotSheet sc v) = rotMagneticBlock sc v ∧
      couplingBlock (rotSheet sc v) = rotCouplingBlock sc v :=
  blocks_coordinatesOfBlocks _ _ _
    (rotElectricBlock_symmetric sc v) (rotMagneticBlock_symmetric sc v)

theorem opNorm_coupling_generic (a q w c1 c2 : ℝ)
    (hc1 : c1 = Real.sqrt (a ^ 2 + q ^ 2)) (hc2 : c2 = Real.sqrt (a ^ 2 + w ^ 2)) :
    opNorm (!![-q + c2, -a; a, -q - c2] : Mat) = c1 + c2 := by
  have hsq1 : c1 ^ 2 = a ^ 2 + q ^ 2 := by
    rw [hc1]
    exact Real.sq_sqrt (by nlinarith [sq_nonneg a, sq_nonneg q])
  have hc10 : 0 ≤ c1 := by rw [hc1]; exact Real.sqrt_nonneg _
  have hc20 : 0 ≤ c2 := by rw [hc2]; exact Real.sqrt_nonneg _
  have habs : |q| ≤ c1 := by
    have h1 : |q| ^ 2 ≤ c1 ^ 2 := by
      rw [sq_abs q, hsq1]
      nlinarith [sq_nonneg a]
    exact (sq_le_sq₀ (abs_nonneg q) hc10).mp h1
  have hcp : 0 ≤ c1 + q := by
    have h1 : -q ≤ |q| := neg_le_abs q
    have h2 : -q ≤ c1 := le_trans h1 habs
    linarith
  have hcm : 0 ≤ c1 - q := by
    have h1 : q ≤ |q| := le_abs_self q
    have h2 : q ≤ c1 := le_trans h1 habs
    linarith

  have e00 : (!![-q + c2, -a; a, -q - c2] : Mat) 0 0 = -q + c2 := by
    simp [Matrix.of_apply]
  have e01 : (!![-q + c2, -a; a, -q - c2] : Mat) 0 1 = -a := by
    simp [Matrix.of_apply]
  have e10 : (!![-q + c2, -a; a, -q - c2] : Mat) 1 0 = a := by
    simp [Matrix.of_apply]
  have e11 : (!![-q + c2, -a; a, -q - c2] : Mat) 1 1 = -q - c2 := by
    simp [Matrix.of_apply]
  have hA : (c1 + c2) ^ 2 - ((-q + c2) ^ 2 + a ^ 2) = 2 * c2 * (c1 + q) := by
    nlinarith [hsq1]
  have hB : (c1 + c2) ^ 2 - ((-a) ^ 2 + (-q - c2) ^ 2) = 2 * c2 * (c1 - q) := by
    nlinarith [hsq1]
  have hX : (-q + c2) * (-a) + a * (-q - c2) = -2 * a * c2 := by
    ring
  have hup : opNorm (!![-q + c2, -a; a, -q - c2] : Mat) ≤ c1 + c2 := by
    rw [opNorm_le_iff_polynomial _ _ (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [e00, e10]
      have h1 : 0 ≤ 2 * c2 * (c1 + q) := mul_nonneg (by linarith) hcp
      nlinarith [hsq1, h1]
    · rw [e01, e11]
      have h2 : 0 ≤ 2 * c2 * (c1 - q) := mul_nonneg (by linarith) hcm
      nlinarith [hsq1, h2]
    · rw [e00, e10, e01, e11]
      rw [hA, hB, hX]
      have h3 : (2 * c2 * (c1 + q)) * (2 * c2 * (c1 - q)) - (-2 * a * c2) ^ 2
          = 4 * c2 ^ 2 * (c1 ^ 2 - q ^ 2 - a ^ 2) := by
        ring
      rw [h3, hsq1]
      nlinarith

  apply le_antisymm hup
  by_cases ha : a = 0
  · have hdiag : (!![-q + c2, -a; a, -q - c2] : Mat) = !![c2 - q, 0; 0, -(c2 + q)] := by
      rw [ha]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply] <;> ring
    rw [hdiag, opNorm_diagonal2, abs_neg]
    have hmax : max |c2 - q| |c2 + q| = c2 + |q| := by
      by_cases hq : 0 ≤ q
      · have h1 : |c2 - q| ≤ c2 + q := by
          have hab := abs_add_le c2 (-q)
          have hab' : |c2 - q| ≤ |c2| + |q| := by
            simpa [sub_eq_add_neg, abs_neg] using hab
          rw [abs_of_nonneg hc20, abs_of_nonneg hq] at hab'
          exact hab'
        have h2 : |c2 + q| = c2 + q := abs_of_nonneg (by linarith [hc20, hq])
        have hle : |c2 - q| ≤ |c2 + q| := h1.trans_eq h2.symm
        rw [max_eq_right hle, h2]
        linarith [abs_of_nonneg hq]
      · have h2 : |c2 - q| = c2 - q := abs_of_nonneg (by linarith [hc20, lt_of_not_ge hq])
        have hqn : |q| = -q := abs_of_nonpos (le_of_lt (lt_of_not_ge hq))
        have h1 : |c2 + q| ≤ c2 - q := by
          have hab := abs_add_le c2 q
          rwa [abs_of_nonneg hc20, hqn] at hab
        have hle : |c2 + q| ≤ |c2 - q| := h1.trans (le_of_eq h2.symm)
        rw [max_eq_left hle, h2]
        linarith
    rw [hmax, hc1]
    simp [ha, Real.sqrt_sq_eq_abs, add_comm]
  · set v : Fin 2 → ℝ := ![-a, c1 + q]
    have hq1v : 0 < quadForm 1 v := by
      have hexp : quadForm 1 v = a ^ 2 + (c1 + q) ^ 2 := by
        simp [quadForm, dotProduct, Fin.sum_univ_two, Matrix.mulVec, v]
        ring
      rw [hexp]
      have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
      nlinarith [sq_nonneg (c1 + q)]
    have hqG : quadForm ((!![-q + c2, -a; a, -q - c2] : Mat).transpose
        * (!![-q + c2, -a; a, -q - c2] : Mat)) v = (c1 + c2) ^ 2 * quadForm 1 v := by
      have hexp : quadForm ((!![-q + c2, -a; a, -q - c2] : Mat).transpose
          * (!![-q + c2, -a; a, -q - c2] : Mat)) v
          = ((c2 - q) ^ 2 + a ^ 2) * a ^ 2 + 2 * (-2 * a * c2) * (-a) * (c1 + q)
            + ((c2 + q) ^ 2 + a ^ 2) * (c1 + q) ^ 2 := by
        simp [quadForm, dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.mul_apply,
          Matrix.transpose_apply, v]
        ring
      have hq1 : quadForm 1 v = a ^ 2 + (c1 + q) ^ 2 := by
        simp [quadForm, dotProduct, Fin.sum_univ_two, Matrix.mulVec, v]
        ring
      rw [hexp, hq1]
      have hfac : ((c2 - q) ^ 2 + a ^ 2) * a ^ 2 + 2 * (-2 * a * c2) * (-a) * (c1 + q)
            + ((c2 + q) ^ 2 + a ^ 2) * (c1 + q) ^ 2
          = (c1 + c2) ^ 2 * (a ^ 2 + (c1 + q) ^ 2)
            + (c1 ^ 2 - a ^ 2 - q ^ 2)
              * (-(a ^ 2 + c1 ^ 2 + 2 * c1 * c2 + 2 * c1 * q + 2 * c2 * q + q ^ 2)) := by
        ring
      rw [hfac, hsq1]
      ring
    have hh := (opNorm_le_iff_quad (!![-q + c2, -a; a, -q - c2] : Mat)
      (opNorm (!![-q + c2, -a; a, -q - c2] : Mat)) (opNorm_nonneg _)).mp le_rfl v
    have hcomb : quadForm 1 v * (c1 + c2) ^ 2
        ≤ quadForm 1 v * (opNorm (!![-q + c2, -a; a, -q - c2] : Mat)) ^ 2 := by
      rw [hqG] at hh
      linarith
    have hsq : (c1 + c2) ^ 2
        ≤ (opNorm (!![-q + c2, -a; a, -q - c2] : Mat)) ^ 2 := by
      have h' : (c1 + c2) ^ 2 * quadForm 1 v
          ≤ (opNorm (!![-q + c2, -a; a, -q - c2] : Mat)) ^ 2 * quadForm 1 v := by
        simpa [mul_comm] using hcomb
      exact le_of_mul_le_mul_right h' hq1v
    have h1 : c1 + c2 ≤ opNorm (!![-q + c2, -a; a, -q - c2] : Mat) :=
      (sq_le_sq₀ (by linarith [hc10, hc20]) (opNorm_nonneg _)).mp hsq
    exact h1

theorem opNorm_rotElectricBlock (sc : RotScalars) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    opNorm (rotElectricBlock sc v)
      = |sc.p0 + sc.t * v|
        + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)) := by
  have hsq : (Real.sqrt (1 - v ^ 2)) ^ 2 = 1 - v ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg v])
  have hM : rotElectricBlock sc v
      = (-(sc.p0 + sc.t * v)) • (1 : Mat)
        + !![sc.p1 + sc.u * v, sc.w * Real.sqrt (1 - v ^ 2);
          sc.w * Real.sqrt (1 - v ^ 2), -(sc.p1 + sc.u * v)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotElectricBlock, Matrix.smul_apply, Matrix.add_apply, sub_eq_add_neg]
  rw [hM, opNorm_scalar_tracelessSymm2, abs_neg]
  have h2 : (sc.w * Real.sqrt (1 - v ^ 2)) ^ 2 = sc.w ^ 2 * (1 - v ^ 2) := by
    rw [mul_pow, hsq]
  congr 1
  rw [h2]

theorem opNorm_rotMagneticBlock (sc : RotScalars) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    opNorm (rotMagneticBlock sc v)
      = |sc.p0 - sc.t * v|
        + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)) := by
  have hsq : (Real.sqrt (1 - v ^ 2)) ^ 2 = 1 - v ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg v])
  have hM : rotMagneticBlock sc v
      = (-(sc.p0 - sc.t * v)) • (1 : Mat)
        + !![sc.p1 - sc.u * v, sc.w * Real.sqrt (1 - v ^ 2);
          sc.w * Real.sqrt (1 - v ^ 2), -(sc.p1 - sc.u * v)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotMagneticBlock, Matrix.smul_apply, Matrix.add_apply, sub_eq_add_neg]
  rw [hM, opNorm_scalar_tracelessSymm2, abs_neg]
  have h2 : (sc.w * Real.sqrt (1 - v ^ 2)) ^ 2 = sc.w ^ 2 * (1 - v ^ 2) := by
    rw [mul_pow, hsq]
  congr 1
  rw [h2]

theorem opNorm_rotCouplingBlock (sc : RotScalars) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    opNorm (rotCouplingBlock sc v)
      = Real.sqrt (sc.t ^ 2 * (1 - v ^ 2) + sc.q ^ 2)
        + Real.sqrt (sc.t ^ 2 * (1 - v ^ 2) + sc.w ^ 2) := by
  have hsq : (Real.sqrt (1 - v ^ 2)) ^ 2 = 1 - v ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg v])
  have h2 : (sc.t * Real.sqrt (1 - v ^ 2)) ^ 2 = sc.t ^ 2 * (1 - v ^ 2) := by
    rw [mul_pow, hsq]
  have hblock : rotCouplingBlock sc v
      = !![-sc.q + Real.sqrt ((sc.t * Real.sqrt (1 - v ^ 2)) ^ 2 + sc.w ^ 2),
          -(sc.t * Real.sqrt (1 - v ^ 2));
        sc.t * Real.sqrt (1 - v ^ 2),
        -sc.q - Real.sqrt ((sc.t * Real.sqrt (1 - v ^ 2)) ^ 2 + sc.w ^ 2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotCouplingBlock]
  rw [hblock]
  have hres := opNorm_coupling_generic (sc.t * Real.sqrt (1 - v ^ 2)) sc.q sc.w
    (Real.sqrt ((sc.t * Real.sqrt (1 - v ^ 2)) ^ 2 + sc.q ^ 2))
    (Real.sqrt ((sc.t * Real.sqrt (1 - v ^ 2)) ^ 2 + sc.w ^ 2))
    (by rw [h2]) (by rw [h2])
  rw [hres, h2]

theorem spectralDirectCost_rotSheet (sc : RotScalars) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    spectralDirectCost (rotSheet sc v) = rotDirect sc v := by
  have hb := rotSheet_blocks sc v
  rw [spectralDirectCost, hb.1, hb.2.1]
  rw [opNorm_rotElectricBlock sc v hv0 hv1, opNorm_rotMagneticBlock sc v hv0 hv1]
  rfl

theorem spectralCouplingCost_rotSheet (sc : RotScalars) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    spectralCouplingCost (rotSheet sc v) = rotCoupling sc v := by
  have hb := rotSheet_blocks sc v
  rw [spectralCouplingCost, hb.2.2]
  rw [opNorm_rotCouplingBlock sc v hv0 hv1]
  rfl

theorem spectralDirectBudget_rotSheet (cfg : Config) (sc : RotScalars) (v : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    spectralDirectBudget cfg (rotSheet sc v) = freeSpaceK0 cfg * rotDirect sc v := by
  rw [spectralDirectBudget, spectralDirectCost_rotSheet sc v hv0 hv1]

theorem spectralCouplingBudget_rotSheet (cfg : Config) (sc : RotScalars) (v : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    spectralCouplingBudget cfg (rotSheet sc v) = freeSpaceK0 cfg * rotCoupling sc v := by
  rw [spectralCouplingBudget, spectralCouplingCost_rotSheet sc v hv0 hv1]

@[expose] noncomputable def rotReducedScalars (s r c j x : ℝ) : RotScalars :=
  rotScalars s r c j x (Real.sqrt (1 - x ^ 2))

theorem rotScalars_phase (s r c j φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ Real.pi) :
    rotScalars s r c j (Real.cos φ) (Real.sin φ) = rotReducedScalars s r c j (Real.cos φ) := by
  have hsin0 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc ⟨hφ0, hφ1⟩
  have hsq : Real.sin φ ^ 2 = 1 - (Real.cos φ) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq φ
    linarith
  have hsin : Real.sin φ = Real.sqrt (1 - (Real.cos φ) ^ 2) := by
    rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hsin0]
  simp only [rotScalars, rotReducedScalars]
  congr 1 <;> simp [rotP0, rotP1, rotT, rotU, rotW, rotQ, hsin]

@[expose] def rotDomain (s c x v : ℝ) : Prop :=
  -1 ≤ x ∧ x ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧ rotF s c x (Real.sqrt (1 - x ^ 2)) ≠ 0

theorem rotDomain_v (s c x v : ℝ) (hd : rotDomain s c x v) : 0 ≤ v ∧ v ≤ 1 :=
  ⟨hd.2.2.1, hd.2.2.2.1⟩

theorem rotDomain_surjective (s r c j x v : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ∃ φ β : ℝ, Real.cos φ = x ∧ |Real.cos (Real.pi / 2 + φ - β)| = v ∧
      rotScalars s r c j (Real.cos φ) (Real.sin φ) = rotReducedScalars s r c j x := by
  refine ⟨Real.arccos x, Real.pi / 2 + Real.arccos x - Real.arccos v, ?_, ?_, ?_⟩
  · exact Real.cos_arccos hx0 hx1
  · have harg : Real.pi / 2 + (Real.arccos x)
        - (Real.pi / 2 + Real.arccos x - Real.arccos v) = Real.arccos v := by ring
    rw [harg, Real.cos_arccos (by linarith) hv1]
    exact abs_of_nonneg hv0
  · have hφ0 : 0 ≤ Real.arccos x := Real.arccos_nonneg x
    have hφ1 : Real.arccos x ≤ Real.pi := Real.arccos_le_pi x
    have h := rotScalars_phase s r c j (Real.arccos x) hφ0 hφ1
    simpa [Real.cos_arccos hx0 hx1] using h

@[expose] noncomputable def rotFamilySheet (s r c j x v : ℝ) : MaterialCoordinates :=
  rotSheet (rotReducedScalars s r c j x) v

theorem spectralDirectBudget_family (cfg : Config) (s r c j x v : ℝ)
    (hd : rotDomain s c x v) :
    spectralDirectBudget cfg (rotFamilySheet s r c j x v)
      = freeSpaceK0 cfg * rotDirect (rotReducedScalars s r c j x) v := by
  have hv := rotDomain_v s c x v hd
  exact spectralDirectBudget_rotSheet cfg _ v hv.1 hv.2

theorem spectralCouplingBudget_family (cfg : Config) (s r c j x v : ℝ)
    (hd : rotDomain s c x v) :
    spectralCouplingBudget cfg (rotFamilySheet s r c j x v)
      = freeSpaceK0 cfg * rotCoupling (rotReducedScalars s r c j x) v := by
  have hv := rotDomain_v s c x v hd
  exact spectralCouplingBudget_rotSheet cfg _ v hv.1 hv.2

@[expose] def rotNegate (sc : RotScalars) : RotScalars :=
  { p0 := -sc.p0, p1 := -sc.p1, t := -sc.t, u := -sc.u, w := -sc.w, q := -sc.q }

theorem rotDirect_neg (sc : RotScalars) (v : ℝ) :
    rotDirect (rotNegate sc) v = rotDirect sc v := by
  have h1 : |(-sc.p0) + (-sc.t) * v| = |sc.p0 + sc.t * v| := by
    rw [show (-sc.p0) + (-sc.t) * v = -(sc.p0 + sc.t * v) by ring, abs_neg]
  have h2 : |(-sc.p0) - (-sc.t) * v| = |sc.p0 - sc.t * v| := by
    rw [show (-sc.p0) - (-sc.t) * v = -(sc.p0 - sc.t * v) by ring, abs_neg]
  have h3 : ((-sc.p1) + (-sc.u) * v) ^ 2 + (-sc.w) ^ 2 * (1 - v ^ 2)
      = (sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2) := by ring
  have h4 : ((-sc.p1) - (-sc.u) * v) ^ 2 + (-sc.w) ^ 2 * (1 - v ^ 2)
      = (sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2) := by ring
  simp only [rotDirect, rotNegate]
  rw [h1, h2, h3, h4]

theorem rotCoupling_neg (sc : RotScalars) (v : ℝ) :
    rotCoupling (rotNegate sc) v = rotCoupling sc v := by
  have h1 : (-sc.t) ^ 2 * (1 - v ^ 2) + (-sc.q) ^ 2
      = sc.t ^ 2 * (1 - v ^ 2) + sc.q ^ 2 := by ring
  have h2 : (-sc.t) ^ 2 * (1 - v ^ 2) + (-sc.w) ^ 2
      = sc.t ^ 2 * (1 - v ^ 2) + sc.w ^ 2 := by ring
  simp only [rotCoupling, rotNegate]
  rw [h1, h2]

end GSTC.Scattering.RotatedRankOneResources
