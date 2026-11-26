/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.RotatedRankOneScalarMin

public section

set_option autoImplicit false

namespace GSTC.Scattering.RotatedRankOneRecovery

open scoped Matrix
open RotatedRankOneResources

theorem rotU_abs_ge_w (s r c j x : ℝ) (_hc0 : 0 ≤ c) (_hc1 : c ≤ 1) (_hj0 : 0 ≤ j)
    (hjc : j ^ 2 + c ^ 2 = 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    |(rotReducedScalars s r c j x).u| ≥ |(rotReducedScalars s r c j x).w| := by
  have hx2 : 0 ≤ 1 - x ^ 2 := by
    have hmul : (1 - x) * (1 + x) ≥ 0 := mul_nonneg (by linarith) (by linarith)
    nlinarith [hmul]
  have hid : (1 + c * x) ^ 2 - j ^ 2 * (1 - x ^ 2) = (c + x) ^ 2 := by
    nlinarith [hjc]
  have hbr : j ^ 2 * (1 - x ^ 2) ≤ (1 + c * x) ^ 2 := by
    linarith [hid, sq_nonneg (c + x)]
  simp only [rotReducedScalars, rotScalars, rotU, rotW]
  by_cases hF0 : rotF s c x (Real.sqrt (1 - x ^ 2)) = 0
  · simp [hF0]
  · have hFabs : 0 < |rotF s c x (Real.sqrt (1 - x ^ 2))| :=
      abs_pos.mpr hF0
    have hA : (2 * r * (1 + c * x)) ^ 2 = (2 * r) ^ 2 * (1 + c * x) ^ 2 := by ring
    have hB : (2 * r * j * Real.sqrt (1 - x ^ 2)) ^ 2
        = (2 * r) ^ 2 * (j ^ 2 * (1 - x ^ 2)) := by
      ring_nf
      rw [Real.sq_sqrt hx2]
      ring
    have hsq : (2 * r * j * Real.sqrt (1 - x ^ 2)) ^ 2 ≤ (2 * r * (1 + c * x)) ^ 2 := by
      rw [hB, hA]
      exact mul_le_mul_of_nonneg_left hbr (sq_nonneg (2 * r))
    have habs : |2 * r * j * Real.sqrt (1 - x ^ 2)| ≤ |2 * r * (1 + c * x)| := by
      have h1 : (|2 * r * j * Real.sqrt (1 - x ^ 2)|) ^ 2 ≤ (|2 * r * (1 + c * x)|) ^ 2 := by
        rw [sq_abs, sq_abs]
        exact hsq
      exact (sq_le_sq₀ (abs_nonneg (2 * r * j * Real.sqrt (1 - x ^ 2)))
        (abs_nonneg (2 * r * (1 + c * x)))).mp h1
    have hq : |2 * r * j * Real.sqrt (1 - x ^ 2)| / |rotF s c x (Real.sqrt (1 - x ^ 2))|
        ≤ |2 * r * (1 + c * x)| / |rotF s c x (Real.sqrt (1 - x ^ 2))| :=
      (div_le_div_iff₀ hFabs hFabs).mpr
        (mul_le_mul_of_nonneg_right habs
          (abs_nonneg (rotF s c x (Real.sqrt (1 - x ^ 2)))))
    rw [abs_div, abs_div]
    exact hq

private theorem rotDirect_sq_ge_p1_w_aux (sc : RotScalars) (v : ℝ) (hv2 : 0 ≤ 1 - v ^ 2)
    (huw : |sc.u| ≥ |sc.w|) :
    rotDirect sc v ^ 2 ≥ sc.p1 ^ 2 + sc.w ^ 2 := by
  have hzu : sc.w ^ 2 ≤ sc.u ^ 2 := by
    have h1 : (|sc.w|) ^ 2 ≤ (|sc.u|) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg sc.w) (abs_nonneg sc.u)).mpr huw
    rw [sq_abs, sq_abs] at h1
    exact h1
  have huv : sc.u ^ 2 * v ^ 2 ≥ sc.w ^ 2 * v ^ 2 :=
    (mul_le_mul_of_nonneg_right hzu (sq_nonneg v)).ge
  have hD0 : 0 ≤ rotDirect sc v :=
    ge_trans (rotDirect_ge_radical sc v) (Real.sqrt_nonneg _)
  rcases le_total 0 (sc.p1 * sc.u * v) with hpos | hneg
  · have hrad0 : 0 ≤ (sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2) :=
      add_nonneg (sq_nonneg (sc.p1 + sc.u * v)) (mul_nonneg (sq_nonneg sc.w) hv2)
    have hsq : (Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))) ^ 2
        ≤ rotDirect sc v ^ 2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) hD0).mpr (rotDirect_ge_radical sc v)
    rw [Real.sq_sqrt hrad0] at hsq
    have hid : (sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2) - (sc.p1 ^ 2 + sc.w ^ 2)
        = 2 * (sc.p1 * sc.u * v) + v ^ 2 * (sc.u ^ 2 - sc.w ^ 2) := by ring
    have h1 : 0 ≤ 2 * (sc.p1 * sc.u * v) := by nlinarith [hpos]
    have h2 : 0 ≤ v ^ 2 * (sc.u ^ 2 - sc.w ^ 2) :=
      mul_nonneg (sq_nonneg v) (by linarith [hzu])
    have hrad : 0 ≤ (sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)
        - (sc.p1 ^ 2 + sc.w ^ 2) := by
      rw [hid]
      exact add_nonneg h1 h2
    exact le_trans (by linarith [hrad]) hsq
  · have hrad0 : 0 ≤ (sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2) :=
      add_nonneg (sq_nonneg (sc.p1 - sc.u * v)) (mul_nonneg (sq_nonneg sc.w) hv2)
    have hDm : rotDirect sc v
        ≥ Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)) := by
      simp only [rotDirect]
      have hB : |sc.p0 - sc.t * v|
          + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
          ≥ Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)) := by
        linarith [abs_nonneg (sc.p0 - sc.t * v)]
      have hmax := le_max_right
        (|sc.p0 + sc.t * v| + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)))
        (|sc.p0 - sc.t * v| + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)))
      exact ge_trans hmax hB
    have hsq : (Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))) ^ 2
        ≤ rotDirect sc v ^ 2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) hD0).mpr hDm
    rw [Real.sq_sqrt hrad0] at hsq
    have hid : (sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2) - (sc.p1 ^ 2 + sc.w ^ 2)
        = -2 * (sc.p1 * sc.u * v) + v ^ 2 * (sc.u ^ 2 - sc.w ^ 2) := by ring
    have h1 : 0 ≤ -2 * (sc.p1 * sc.u * v) := by nlinarith [hneg]
    have h2 : 0 ≤ v ^ 2 * (sc.u ^ 2 - sc.w ^ 2) :=
      mul_nonneg (sq_nonneg v) (by linarith [hzu])
    have hrad : 0 ≤ (sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)
        - (sc.p1 ^ 2 + sc.w ^ 2) := by
      rw [hid]
      exact add_nonneg h1 h2
    exact le_trans (by linarith [hrad]) hsq

theorem rotArc_sq_add_ge (s c j v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hm : 0 ≤ rotM s c) :
    (rotM s c * v) ^ 2 + rotArcCoupling s c j v ^ 2 ≥ rotM s c ^ 2 + rotH c j ^ 2 := by
  have hv2 : 0 ≤ 1 - v ^ 2 := arcPhase_nonneg v hv0 hv1
  have hz0 : 0 ≤ Real.sqrt (1 - v ^ 2) := Real.sqrt_nonneg _
  have hz2 : (Real.sqrt (1 - v ^ 2)) ^ 2 = 1 - v ^ 2 := Real.sq_sqrt hv2
  have h4 : 0 ≤ 4 * rotH c j ^ 2 :=
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg (rotH c j))
  have hrad0 : 0 ≤ rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2 :=
    add_nonneg (mul_nonneg (sq_nonneg (rotM s c)) hv2) h4
  have hW2 : (Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)) ^ 2
      = rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2 := Real.sq_sqrt hrad0
  have hWmz : rotM s c * Real.sqrt (1 - v ^ 2)
      ≤ Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2) := by
    have hsq : (rotM s c * Real.sqrt (1 - v ^ 2)) ^ 2
        ≤ rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2 := by
      calc
        (rotM s c * Real.sqrt (1 - v ^ 2)) ^ 2
            = rotM s c ^ 2 * (Real.sqrt (1 - v ^ 2)) ^ 2 := by ring
        _ = rotM s c ^ 2 * (1 - v ^ 2) := by rw [hz2]
        _ ≤ rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2 := by linarith [h4]
    have h1 : Real.sqrt ((rotM s c * Real.sqrt (1 - v ^ 2)) ^ 2)
        ≤ Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2) :=
      Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hm hz0)] at h1
    exact h1
  have hC2 : rotArcCoupling s c j v ^ 2
      = rotM s c ^ 2 * (1 - v ^ 2) / 2 + rotH c j ^ 2
        + (Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
          * rotM s c * Real.sqrt (1 - v ^ 2)) / 2 := by
    rw [rotArcCoupling]
    calc
      ((Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
          + rotM s c * Real.sqrt (1 - v ^ 2)) / 2) ^ 2
          = ((Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)) ^ 2
            + 2 * (Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
              * rotM s c * Real.sqrt (1 - v ^ 2))
            + rotM s c ^ 2 * (Real.sqrt (1 - v ^ 2)) ^ 2) / 4 := by ring
      _ = (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2
            + 2 * (Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
              * rotM s c * Real.sqrt (1 - v ^ 2))
            + rotM s c ^ 2 * (1 - v ^ 2)) / 4 := by rw [hW2, hz2]
      _ = rotM s c ^ 2 * (1 - v ^ 2) / 2 + rotH c j ^ 2
            + (Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
              * rotM s c * Real.sqrt (1 - v ^ 2)) / 2 := by ring
  have hWmz2 : rotM s c ^ 2 * (1 - v ^ 2)
      ≤ Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
        * rotM s c * Real.sqrt (1 - v ^ 2) := by
    have hmm : 0 ≤ rotM s c * Real.sqrt (1 - v ^ 2) := mul_nonneg hm hz0
    have hsq : (rotM s c * Real.sqrt (1 - v ^ 2)) * (rotM s c * Real.sqrt (1 - v ^ 2))
        ≤ Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
          * (rotM s c * Real.sqrt (1 - v ^ 2)) :=
      mul_le_mul_of_nonneg_right hWmz hmm
    have h3 : (rotM s c * Real.sqrt (1 - v ^ 2)) * (rotM s c * Real.sqrt (1 - v ^ 2))
        = rotM s c ^ 2 * (1 - v ^ 2) := by
      calc
        (rotM s c * Real.sqrt (1 - v ^ 2)) * (rotM s c * Real.sqrt (1 - v ^ 2))
            = (rotM s c * Real.sqrt (1 - v ^ 2)) ^ 2 := by ring
        _ = rotM s c ^ 2 * (Real.sqrt (1 - v ^ 2)) ^ 2 := by ring
        _ = rotM s c ^ 2 * (1 - v ^ 2) := by rw [hz2]
    have h4' : Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
        * (rotM s c * Real.sqrt (1 - v ^ 2))
        = Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
          * rotM s c * Real.sqrt (1 - v ^ 2) := by ring
    rw [h3, h4'] at hsq
    exact hsq
  have hid : rotM s c ^ 2 = rotM s c ^ 2 * v ^ 2 + rotM s c ^ 2 * (1 - v ^ 2) := by ring
  have hX0 : 0 ≤ rotM s c ^ 2 * (1 - v ^ 2) :=
    mul_nonneg (sq_nonneg (rotM s c)) hv2
  have hcore : rotM s c ^ 2 ≤ (rotM s c * v) ^ 2 + rotM s c ^ 2 * (1 - v ^ 2) / 2
      + (Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
        * rotM s c * Real.sqrt (1 - v ^ 2)) / 2 := by
    have hmv : (rotM s c * v) ^ 2 = rotM s c ^ 2 * v ^ 2 := by ring
    rw [hmv]
    linarith [hid, hWmz2, hX0]
  rw [hC2]
  linarith [hcore]

theorem rotM_sq_add_rotH_sq_ge (s c j : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (_hj0 : 0 ≤ j) (hjc : j ^ 2 + c ^ 2 = 1) :
    rotM s c ^ 2 + rotH c j ^ 2 ≥ (2 * rotRho s) ^ 2 := by
  have h1s : 0 < 1 + s := by linarith
  have h1c : 0 < 1 + c := by linarith
  have hρ : rotRho s ^ 2 = (1 - s) / (1 + s) := rotRho_sq s hs0 hs1
  have hρ1 : (1 + s) * rotRho s ^ 2 = 1 - s := by
    rw [hρ]
    calc
      (1 + s) * ((1 - s) / (1 + s)) = ((1 - s) / (1 + s)) * (1 + s) := by ring
      _ = 1 - s := div_mul_cancel₀ (1 - s) (ne_of_gt h1s)
  have hjc' : j ^ 2 = 1 - c ^ 2 := by linarith [hjc]
  have hnum : 0 ≤ 16 * (1 - s) + 4 * j ^ 2 * (1 + s) - 4 * (1 - s) * (1 + c) ^ 2 := by
    rw [hjc']
    have hid : 16 * (1 - s) + 4 * (1 - c ^ 2) * (1 + s) - 4 * (1 - s) * (1 + c) ^ 2
        = 8 * (1 - c) * (2 + c - s) := by ring
    rw [hid]
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (by linarith)) (by linarith)
  have hkeyeq : (1 + s) * (16 * rotRho s ^ 2 + 4 * j ^ 2 - 4 * rotRho s ^ 2 * (1 + c) ^ 2)
      = 16 * (1 - s) + 4 * j ^ 2 * (1 + s) - 4 * (1 - s) * (1 + c) ^ 2 := by
    calc
      (1 + s) * (16 * rotRho s ^ 2 + 4 * j ^ 2 - 4 * rotRho s ^ 2 * (1 + c) ^ 2)
          = 16 * ((1 + s) * rotRho s ^ 2) + 4 * ((1 + s) * j ^ 2)
              - 4 * ((1 + s) * rotRho s ^ 2 * (1 + c) ^ 2) := by ring
      _ = 16 * (1 - s) + 4 * j ^ 2 * (1 + s) - 4 * (1 - s) * (1 + c) ^ 2 := by
        rw [hρ1]
        ring
  have hkey : 0 ≤ 16 * rotRho s ^ 2 + 4 * j ^ 2 - 4 * rotRho s ^ 2 * (1 + c) ^ 2 := by
    have hnonneg : 0 ≤ (1 + s)
        * (16 * rotRho s ^ 2 + 4 * j ^ 2 - 4 * rotRho s ^ 2 * (1 + c) ^ 2) := by
      rw [hkeyeq]
      exact hnum
    exact (mul_nonneg_iff_of_pos_left h1s).mp hnonneg
  have hρ2 : (2 * rotRho s) ^ 2 = 4 * rotRho s ^ 2 := by ring
  have hfinal : (16 * rotRho s ^ 2 + 4 * j ^ 2) / (1 + c) ^ 2 ≥ (2 * rotRho s) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos h1c)).mpr
    rw [hρ2]
    linarith [hkey]
  rw [rotM, rotH]
  calc
    (4 * rotRho s / (1 + c)) ^ 2 + (2 * j / (1 + c)) ^ 2
        = (16 * rotRho s ^ 2 + 4 * j ^ 2) / (1 + c) ^ 2 := by
          have hne : (1 + c) ≠ 0 := ne_of_gt h1c
          field_simp
          ring
    _ ≥ (2 * rotRho s) ^ 2 := hfinal

theorem rotDirect_sq_ge_p1_w (s r c j x v : ℝ) (_hs0 : 0 < s) (_hs1 : s < 1) (_hr0 : 0 ≤ r)
    (_hrs : r ^ 2 + s ^ 2 = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hj0 : 0 ≤ j)
    (hjc : j ^ 2 + c ^ 2 = 1) (hd : rotDomain s c x v) :
    rotDirect (rotReducedScalars s r c j x) v ^ 2
      ≥ (rotReducedScalars s r c j x).p1 ^ 2 + (rotReducedScalars s r c j x).w ^ 2 := by
  have hv := rotDomain_v s c x v hd
  have hv2 : 0 ≤ 1 - v ^ 2 := arcPhase_nonneg v hv.1 hv.2
  have huw : |(rotReducedScalars s r c j x).u| ≥ |(rotReducedScalars s r c j x).w| :=
    rotU_abs_ge_w s r c j x hc0 hc1 hj0 hjc hd.1 hd.2.1
  exact rotDirect_sq_ge_p1_w_aux (rotReducedScalars s r c j x) v hv2 huw

theorem rotDirect_sq_add_coupling_sq (s r c j x v : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hj0 : 0 ≤ j)
    (hjc : j ^ 2 + c ^ 2 = 1) (hd : rotDomain s c x v) :
    rotDirect (rotReducedScalars s r c j x) v ^ 2
      + rotCoupling (rotReducedScalars s r c j x) v ^ 2 ≥ (2 * rotRho s) ^ 2 := by
  have hv := rotDomain_v s c x v hd
  have hv0 : 0 ≤ v := hv.1
  have hv1 : v ≤ 1 := hv.2
  have hFne : rotF s c x (Real.sqrt (1 - x ^ 2)) ≠ 0 := hd.2.2.2.2
  rcases rotDenominator_cases s c x hFne with hFpos | hFneg
  · have hm : 0 < rotM s c := rotM_pos s c hs0 hs1 hc0
    have hm0 : 0 ≤ rotM s c := le_of_lt hm
    have hD : rotDirect (rotReducedScalars s r c j x) v
        ≥ 2 * |(rotReducedScalars s r c j x).t| * v :=
      dominance_pos_direct s r c j x v hd hFpos hr0 hc0 hc1
    have hT : 2 * |(rotReducedScalars s r c j x).t| ≥ rotM s c :=
      dominance_pos_t s r c j x v hd hFpos hr0 hrs hs0 hs1 hc0
    have hC : rotCoupling (rotReducedScalars s r c j x) v ≥ rotArcCoupling s c j v :=
      dominance_pos_coupling s r c j x v hd hFpos hr0 hrs hs0 hs1 hc0
    have hDv : rotDirect (rotReducedScalars s r c j x) v ≥ rotM s c * v := by
      have h := mul_le_mul_of_nonneg_right hT hv0
      linarith
    have hD0 : 0 ≤ rotDirect (rotReducedScalars s r c j x) v := by
      have hmv : 0 ≤ rotM s c * v := mul_nonneg hm0 hv0
      linarith
    have hDv2 : (rotM s c * v) ^ 2 ≤ rotDirect (rotReducedScalars s r c j x) v ^ 2 :=
      (sq_le_sq₀ (mul_nonneg hm0 hv0) hD0).mpr hDv
    have hC0 : 0 ≤ rotCoupling (rotReducedScalars s r c j x) v := by
      simp only [rotCoupling]
      exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hArc0 : 0 ≤ rotArcCoupling s c j v := by
      simp only [rotArcCoupling]
      exact div_nonneg
        (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hm0 (Real.sqrt_nonneg _))) (by norm_num)
    have hC2 : rotArcCoupling s c j v ^ 2 ≤ rotCoupling (rotReducedScalars s r c j x) v ^ 2 :=
      (sq_le_sq₀ hArc0 hC0).mpr hC
    have hArc : (rotM s c * v) ^ 2 + rotArcCoupling s c j v ^ 2
        ≥ rotM s c ^ 2 + rotH c j ^ 2 :=
      rotArc_sq_add_ge s c j v hv0 hv1 hm0
    have hB : rotM s c ^ 2 + rotH c j ^ 2 ≥ (2 * rotRho s) ^ 2 :=
      rotM_sq_add_rotH_sq_ge s c j hs0 hs1 hc0 hc1 hj0 hjc
    have h1 : (rotM s c * v) ^ 2 + rotArcCoupling s c j v ^ 2
        ≤ rotDirect (rotReducedScalars s r c j x) v ^ 2
          + rotCoupling (rotReducedScalars s r c j x) v ^ 2 := by
      linarith [hDv2, hC2]
    exact le_trans (le_trans hB hArc) h1
  · have hD : rotDirect (rotReducedScalars s r c j x) v > 2 :=
      rotDirect_gt_two_negF s r c j x v hd hFneg hr0 hrs hs0 hs1 hj0 hjc
    have hD2 : 4 < rotDirect (rotReducedScalars s r c j x) v ^ 2 := by
      have hprod : 0 < (rotDirect (rotReducedScalars s r c j x) v - 2)
          * (rotDirect (rotReducedScalars s r c j x) v + 2) :=
        mul_pos (sub_pos.mpr hD) (by linarith [hD])
      nlinarith [hprod]
    have hρ : rotRho s ^ 2 = (1 - s) / (1 + s) := rotRho_sq s hs0 hs1
    have hρ1 : rotRho s ^ 2 ≤ 1 := by
      rw [hρ]
      apply (div_le_iff₀ (by linarith)).mpr
      linarith
    have hC2 : 0 ≤ rotCoupling (rotReducedScalars s r c j x) v ^ 2 := sq_nonneg _
    have hρ2 : (2 * rotRho s) ^ 2 = 4 * rotRho s ^ 2 := by ring
    rw [hρ2]
    linarith [hD2, hρ1, hC2]

private theorem rotDirect_zero (sc : RotScalars) :
    rotDirect sc 0 = |sc.p0| + Real.sqrt (sc.p1 ^ 2 + sc.w ^ 2) := by
  have h1 : sc.p0 + sc.t * 0 = sc.p0 := by ring
  have h2 : sc.p0 - sc.t * 0 = sc.p0 := by ring
  have h3 : sc.p1 + sc.u * 0 = sc.p1 := by ring
  have h4 : sc.p1 - sc.u * 0 = sc.p1 := by ring
  have h5 : sc.w ^ 2 * (1 - 0 ^ 2) = sc.w ^ 2 := by ring
  simp only [rotDirect, h1, h2, h3, h4, h5]
  exact max_self _

private theorem rotCoupling_zero (sc : RotScalars) :
    rotCoupling sc 0 = Real.sqrt (sc.t ^ 2 + sc.q ^ 2) + Real.sqrt (sc.t ^ 2 + sc.w ^ 2) := by
  have h5 : sc.t ^ 2 * (1 - 0 ^ 2) = sc.t ^ 2 := by ring
  simp only [rotCoupling, h5]

theorem rotRightAngle_pair (s r : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hr0 : 0 ≤ r)
    (hrs : r ^ 2 + s ^ 2 = 1) :
    rotDirect (rotReducedScalars s r 0 1 0) 0 = 2 * Real.sqrt (1 + 1 / rotRho s ^ 2) ∧
      rotCoupling (rotReducedScalars s r 0 1 0) 0 = 2 / rotRho s := by
  have h1m : 0 < 1 - s := by linarith
  have h1mn : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hs1))
  have hden : -(1 - s) ≠ 0 := neg_ne_zero.mpr h1mn
  have hF : rotF s 0 0 1 = -(1 - s) := by
    simp only [rotF]
    ring
  have hred : rotReducedScalars s r 0 1 0 = rotScalars s r 0 1 0 1 := by
    simp only [rotReducedScalars, pow_two, mul_zero, sub_zero, Real.sqrt_one]
  have hp0 : (rotReducedScalars s r 0 1 0).p0 = 0 := by
    rw [hred]
    simp only [rotScalars, rotP0]
    rw [hF]
    simp
  have hp1 : (rotReducedScalars s r 0 1 0).p1 = -2 := by
    rw [hred]
    simp only [rotScalars, rotP1]
    rw [hF]
    field_simp [hden]
  have ht : (rotReducedScalars s r 0 1 0).t = 0 := by
    rw [hred]
    simp only [rotScalars, rotT]
    rw [hF]
    simp
  have hq : (rotReducedScalars s r 0 1 0).q = 0 := by
    rw [hred]
    simp only [rotScalars, rotQ]
    rw [hF]
    simp
  have hw : (rotReducedScalars s r 0 1 0).w = -(2 * r / (1 - s)) := by
    rw [hred]
    simp only [rotScalars, rotW]
    rw [hF]
    field_simp [hden, h1mn]
  have hρeq : 2 * r / (1 - s) = 2 / rotRho s := by
    rw [mul_div_assoc, rotR_div_one_minus s r hr0 hrs hs0 hs1, ← mul_div_assoc, mul_one]
  have hwn : 0 ≤ 2 * r / (1 - s) :=
    div_nonneg (mul_nonneg (by norm_num) hr0) (le_of_lt h1m)
  have hp12 : (rotReducedScalars s r 0 1 0).p1 ^ 2 = 4 := by
    rw [hp1]
    norm_num
  have hw2 : (rotReducedScalars s r 0 1 0).w ^ 2 = (2 * r / (1 - s)) ^ 2 := by
    rw [hw]
    ring
  have hD : rotDirect (rotReducedScalars s r 0 1 0) 0
      = Real.sqrt (4 + (2 * r / (1 - s)) ^ 2) := by
    rw [rotDirect_zero, hp0, hp12, hw2]
    simp only [abs_zero, zero_add]
  have hD' : Real.sqrt (4 + (2 * r / (1 - s)) ^ 2) = 2 * Real.sqrt (1 + 1 / rotRho s ^ 2) := by
    rw [hρeq]
    have hsq : (4 : ℝ) + (2 / rotRho s) ^ 2 = 4 * (1 + 1 / rotRho s ^ 2) := by
      ring
    rw [hsq, Real.sqrt_mul (x := 4) (by norm_num) (1 + 1 / rotRho s ^ 2)]
    have h4 : Real.sqrt 4 = 2 := by
      rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
      norm_num
    rw [h4]
  have ht2 : (rotReducedScalars s r 0 1 0).t ^ 2 = 0 := by
    rw [ht]
    norm_num
  have hq2 : (rotReducedScalars s r 0 1 0).q ^ 2 = 0 := by
    rw [hq]
    norm_num
  have hC : rotCoupling (rotReducedScalars s r 0 1 0) 0 = 2 * r / (1 - s) := by
    rw [rotCoupling_zero, ht2, hq2, hw]
    simp only [Real.sqrt_zero, zero_add]
    rw [Real.sqrt_sq_eq_abs, abs_neg, abs_of_nonneg hwn]
  refine ⟨?_, ?_⟩
  · rw [hD, hD']
  · rw [hC, hρeq]

theorem rotRightAngle_negF_dominated (s r x v : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1) (hd : rotDomain s 0 x v)
    (hF : rotNegDenominator s 0 x) :
    rotDirect (rotReducedScalars s r 0 1 x) v ≥ 2 * Real.sqrt (1 + 1 / rotRho s ^ 2) ∧
      rotCoupling (rotReducedScalars s r 0 1 x) v ≥ 2 / rotRho s := by
  have hρ0 : 0 < rotRho s := rotRho_pos s hs0 hs1
  have hy : 0 < Real.sqrt (1 - x ^ 2) := rotNegBranch_y_pos s 0 x hs0 hs1 hF
  have hy1 : Real.sqrt (1 - x ^ 2) ≤ 1 := by
    have hlt : Real.sqrt (1 - x ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith [sq_nonneg x])
    rwa [Real.sqrt_one] at hlt
  have hv := rotDomain_v s 0 x v hd
  have hv2 : 0 ≤ 1 - v ^ 2 := arcPhase_nonneg v hv.1 hv.2
  have hCw : rotCoupling (rotReducedScalars s r 0 1 x) v ≥ |(rotReducedScalars s r 0 1 x).w| :=
    rotCoupling_ge_w _ _ hv2
  have hwd : |(rotReducedScalars s r 0 1 x).w|
      ≥ 2 * 1 / (rotRho s * Real.sqrt (1 - x ^ 2)) :=
    dominance_neg_w s r 0 1 x v hd hF hr0 hrs hs0 hs1
  have hconv : 2 * 1 / (rotRho s * Real.sqrt (1 - x ^ 2))
      = 2 / (rotRho s * Real.sqrt (1 - x ^ 2)) := by ring
  have hwd' : |(rotReducedScalars s r 0 1 x).w| ≥ 2 / (rotRho s * Real.sqrt (1 - x ^ 2)) := by
    rw [hconv] at hwd
    exact hwd
  have hCstep : 2 / rotRho s ≤ 2 / (rotRho s * Real.sqrt (1 - x ^ 2)) := by
    apply (le_div_iff₀ (mul_pos hρ0 hy)).2
    have hq : (2 / rotRho s) * (rotRho s * Real.sqrt (1 - x ^ 2))
        = 2 * Real.sqrt (1 - x ^ 2) := by
      field_simp [hρ0.ne']
    rw [hq]
    linarith [hy1]
  have hC : rotCoupling (rotReducedScalars s r 0 1 x) v ≥ 2 / rotRho s :=
    le_trans hCstep (le_trans hwd' hCw)
  have hcert : rotDirect (rotReducedScalars s r 0 1 x) v ^ 2
      ≥ (rotReducedScalars s r 0 1 x).p1 ^ 2 + (rotReducedScalars s r 0 1 x).w ^ 2 :=
    rotDirect_sq_ge_p1_w s r 0 1 x v hs0 hs1 hr0 hrs (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hd
  have hp1 : |(rotReducedScalars s r 0 1 x).p1| ≥ 2 / Real.sqrt (1 - x ^ 2) :=
    dominance_neg_p1 s r 0 1 x v hd hF hr0 hrs hs0 hs1
  have hp1' : 2 ≤ |(rotReducedScalars s r 0 1 x).p1| := by
    have h2 : 2 ≤ 2 / Real.sqrt (1 - x ^ 2) := by
      apply (le_div_iff₀ hy).2
      linarith [hy1]
    exact le_trans h2 hp1
  have hwd'' : 2 / rotRho s ≤ |(rotReducedScalars s r 0 1 x).w| :=
    le_trans hCstep hwd'
  have hp1sq : (rotReducedScalars s r 0 1 x).p1 ^ 2 ≥ 4 := by
    calc (rotReducedScalars s r 0 1 x).p1 ^ 2 = |(rotReducedScalars s r 0 1 x).p1| ^ 2 :=
        (sq_abs _).symm
      _ ≥ (2 : ℝ) ^ 2 := by
        have ha : 0 ≤ (2 : ℝ) := by norm_num
        have hb : 0 ≤ |(rotReducedScalars s r 0 1 x).p1| := abs_nonneg _
        exact (sq_le_sq₀ ha hb).mpr hp1'
      _ = 4 := by ring
  have hwabs : (rotReducedScalars s r 0 1 x).w ^ 2 ≥ (2 / rotRho s) ^ 2 := by
    calc (rotReducedScalars s r 0 1 x).w ^ 2 = |(rotReducedScalars s r 0 1 x).w| ^ 2 :=
        (sq_abs _).symm
      _ ≥ (2 / rotRho s) ^ 2 := by
        have ha : 0 ≤ 2 / rotRho s := div_nonneg (by norm_num) (le_of_lt hρ0)
        have hb : 0 ≤ |(rotReducedScalars s r 0 1 x).w| := abs_nonneg _
        exact (sq_le_sq₀ ha hb).mpr hwd''
  have hDsum : (rotReducedScalars s r 0 1 x).p1 ^ 2 + (rotReducedScalars s r 0 1 x).w ^ 2
      ≥ 4 + 4 / rotRho s ^ 2 := by
    calc (rotReducedScalars s r 0 1 x).p1 ^ 2 + (rotReducedScalars s r 0 1 x).w ^ 2
        ≥ 4 + (2 / rotRho s) ^ 2 := add_le_add hp1sq hwabs
      _ = 4 + 4 / rotRho s ^ 2 := by ring
  have hX : 0 ≤ 1 + 1 / rotRho s ^ 2 := by
    have hq : 0 ≤ 1 / rotRho s ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
    linarith
  have htarget : (2 * Real.sqrt (1 + 1 / rotRho s ^ 2)) ^ 2 = 4 + 4 / rotRho s ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hX]
    ring
  have hDnonneg : 0 ≤ rotDirect (rotReducedScalars s r 0 1 x) v :=
    le_trans (Real.sqrt_nonneg _) (rotDirect_ge_radical _ _)
  have hB : 0 ≤ 2 * Real.sqrt (1 + 1 / rotRho s ^ 2) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hD : rotDirect (rotReducedScalars s r 0 1 x) v ≥ 2 * Real.sqrt (1 + 1 / rotRho s ^ 2) := by
    have hsq : (2 * Real.sqrt (1 + 1 / rotRho s ^ 2)) ^ 2
        ≤ rotDirect (rotReducedScalars s r 0 1 x) v ^ 2 := by
      rw [htarget]
      exact le_trans hDsum hcert
    exact (sq_le_sq₀ hB hDnonneg).mp hsq
  exact ⟨hD, hC⟩

theorem rotRightAngle_min (s r x v : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hr0 : 0 ≤ r)
    (hrs : r ^ 2 + s ^ 2 = 1) (hd : rotDomain s 0 x v) :
    max (rotDirect (rotReducedScalars s r 0 1 x) v) (rotCoupling (rotReducedScalars s r 0 1 x) v)
      ≥ min (rotSharpMin (rotM s 0) (rotH 0 1)) (2 * Real.sqrt (1 + 1 / rotRho s ^ 2)) := by
  have hne : rotF s 0 x (Real.sqrt (1 - x ^ 2)) ≠ 0 := hd.2.2.2.2
  rcases rotDenominator_cases s 0 x hne with hpos | hneg
  · have hv := rotDomain_v s 0 x v hd
    have hD : rotDirect (rotReducedScalars s r 0 1 x) v
        ≥ 2 * |(rotReducedScalars s r 0 1 x).t| * v :=
      dominance_pos_direct s r 0 1 x v hd hpos hr0 (by norm_num) (by norm_num)
    have hT : 2 * |(rotReducedScalars s r 0 1 x).t| ≥ rotM s 0 :=
      dominance_pos_t s r 0 1 x v hd hpos hr0 hrs hs0 hs1 (by norm_num)
    have hC : rotCoupling (rotReducedScalars s r 0 1 x) v ≥ rotArcCoupling s 0 1 v :=
      dominance_pos_coupling s r 0 1 x v hd hpos hr0 hrs hs0 hs1 (by norm_num)
    have hA : rotArcDirect s 0 v ≤ rotDirect (rotReducedScalars s r 0 1 x) v := by
      calc rotArcDirect s 0 v = rotM s 0 * v := rfl
        _ ≤ 2 * |(rotReducedScalars s r 0 1 x).t| * v := mul_le_mul_of_nonneg_right hT hv.1
        _ ≤ rotDirect (rotReducedScalars s r 0 1 x) v := hD
    have hmax : max (rotArcDirect s 0 v) (rotArcCoupling s 0 1 v)
        ≤ max (rotDirect (rotReducedScalars s r 0 1 x) v)
          (rotCoupling (rotReducedScalars s r 0 1 x) v) :=
      max_le_max hA hC
    have harc : max (rotArcDirect s 0 v) (rotArcCoupling s 0 1 v)
        ≥ rotSharpMin (rotM s 0) (rotH 0 1) :=
      rotSharpMin_le_arc s 0 1 v hs0 hs1 (by norm_num) (by norm_num) (by norm_num) hv.1 hv.2
    have h1 : max (rotDirect (rotReducedScalars s r 0 1 x) v)
          (rotCoupling (rotReducedScalars s r 0 1 x) v) ≥ rotSharpMin (rotM s 0) (rotH 0 1) :=
      le_trans harc hmax
    exact le_trans (min_le_left _ _) h1
  · have hdom := rotRightAngle_negF_dominated s r x v hs0 hs1 hr0 hrs hd hneg
    have h1 : 2 * Real.sqrt (1 + 1 / rotRho s ^ 2)
        ≤ max (rotDirect (rotReducedScalars s r 0 1 x) v)
          (rotCoupling (rotReducedScalars s r 0 1 x) v) :=
      le_trans hdom.1 (le_max_left _ _)
    exact le_trans (min_le_right _ _) h1

theorem rotRightAngle_min_attained (s r : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hr0 : 0 ≤ r)
    (hrs : r ^ 2 + s ^ 2 = 1) :
    max (rotArcDirect s 0 (rotSharpMinArg (rotM s 0) (rotH 0 1)))
        (rotArcCoupling s 0 1 (rotSharpMinArg (rotM s 0) (rotH 0 1)))
      = rotSharpMin (rotM s 0) (rotH 0 1) ∧
      rotDirect (rotReducedScalars s r 0 1 0) 0 = 2 * Real.sqrt (1 + 1 / rotRho s ^ 2) ∧
      rotCoupling (rotReducedScalars s r 0 1 0) 0 = 2 / rotRho s := by
  refine ⟨rotSharpMin_attained s 0 1 hs0 hs1 (by norm_num) (by norm_num) (by norm_num), ?_⟩
  exact rotRightAngle_pair s r hs0 hs1 hr0 hrs

theorem rotRightAngle_image_lower (cfg : Config) (s r : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1) (heta : cfg.upper.eta = cfg.vac.eta0) :
    ∀ b ∈ physicalResourceImage cfg s r 0 1,
      max b.1 b.2 ≥ min (rotSharpMin (rotM s 0) (rotH 0 1))
        (2 * Real.sqrt (1 + 1 / rotRho s ^ 2)) := by
  intro b hb
  obtain ⟨x, v, hd, rfl⟩ :=
    (exact_physical_resource_image cfg s r 0 1 hrs (by norm_num) heta b).mp hb
  exact rotRightAngle_min s r x v hs0 hs1 hr0 hrs hd

theorem rotRightAngle_image_attained (cfg : Config) (s r : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1) (heta : cfg.upper.eta = cfg.vac.eta0) :
    ∃ b ∈ physicalResourceImage cfg s r 0 1,
      max b.1 b.2 = 2 * Real.sqrt (1 + 1 / rotRho s ^ 2) := by
  have hF : rotF s 0 0 (Real.sqrt (1 - 0 ^ 2)) = -(1 - s) := by
    rw [rotF]
    have hsq0 : Real.sqrt (1 - 0 ^ 2) = 1 := by
      have h : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h, sub_zero, Real.sqrt_one]
    rw [hsq0]
    ring
  have hFne : rotF s 0 0 (Real.sqrt (1 - 0 ^ 2)) ≠ 0 := by
    rw [hF]
    intro hz
    have hzs : (1 : ℝ) - s = 0 := by linarith
    linarith
  have hd : rotDomain s 0 0 0 :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, hFne⟩
  refine ⟨(rotDirect (rotReducedScalars s r 0 1 0) 0,
      rotCoupling (rotReducedScalars s r 0 1 0) 0), ?_, ?_⟩
  · exact (exact_physical_resource_image cfg s r 0 1 hrs (by norm_num) heta _).mpr
      ⟨0, 0, hd, rfl⟩
  · have hp := rotRightAngle_pair s r hs0 hs1 hr0 hrs
    have hρpos : 0 < rotRho s := rotRho_pos s hs0 hs1
    have hsq : (1 / rotRho s) ^ 2 ≤ 1 + 1 / rotRho s ^ 2 := by
      rw [div_pow]
      linarith
    have h1 : Real.sqrt ((1 / rotRho s) ^ 2) ≤ Real.sqrt (1 + 1 / rotRho s ^ 2) :=
      Real.sqrt_le_sqrt hsq
    have h2 : Real.sqrt ((1 / rotRho s) ^ 2) = 1 / rotRho s := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (div_pos (by norm_num) hρpos)]
    have h3 : 1 / rotRho s ≤ Real.sqrt (1 + 1 / rotRho s ^ 2) := h2 ▸ h1
    have hle : 2 / rotRho s ≤ 2 * Real.sqrt (1 + 1 / rotRho s ^ 2) := by
      have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 2)
      rw [show 2 * (1 / rotRho s) = 2 / rotRho s by ring] at h4
      exact h4
    rw [hp.1, hp.2]
    exact max_eq_left hle

end GSTC.Scattering.RotatedRankOneRecovery
