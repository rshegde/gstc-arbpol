/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.RotatedRankOneFrontier

public section
set_option autoImplicit false
namespace GSTC.Scattering.RotatedRankOneRecovery
open scoped Matrix
open RotatedRankOneResources

private noncomputable def radR (m h : ℝ) : ℝ := m ^ 4 + 4 * m ^ 2 * h ^ 2 - 4 * h ^ 4

private noncomputable def radS (m h : ℝ) : ℝ := m ^ 2 + 2 * h ^ 2 + Real.sqrt (radR m h)

@[expose] noncomputable def rotSharpMin (m h : ℝ) : ℝ :=
  if m ≤ h then h
  else (1 / 2) * Real.sqrt (m ^ 2 + 2 * h ^ 2 +
    Real.sqrt (m ^ 4 + 4 * m ^ 2 * h ^ 2 - 4 * h ^ 4))

@[expose] noncomputable def rotSharpMinArg (m h : ℝ) : ℝ :=
  if m ≤ h then 1 else rotSharpMin m h / m

theorem rotSharpMin_radical_nonneg (m h : ℝ) (hm : m > h) (hh : 0 ≤ h) :
    0 < m ^ 4 + 4 * m ^ 2 * h ^ 2 - 4 * h ^ 4 := by
  have hdiff : 0 < m ^ 2 - h ^ 2 := by
    have hprod : 0 < (m - h) * (m + h) := mul_pos (sub_pos.mpr hm) (by linarith)
    nlinarith
  have h4 : 0 < m ^ 4 - h ^ 4 := by
    have hsum : 0 < m ^ 2 + h ^ 2 := by nlinarith [sq_nonneg h]
    have hprod : 0 < (m ^ 2 - h ^ 2) * (m ^ 2 + h ^ 2) := mul_pos hdiff hsum
    nlinarith
  have hc4 : 0 ≤ 4 * h ^ 2 := by nlinarith [sq_nonneg h]
  have hpos : 0 ≤ 4 * h ^ 2 * (m ^ 2 - h ^ 2) := mul_nonneg hc4 (le_of_lt hdiff)
  nlinarith [sq_nonneg (h ^ 2)]

theorem rotSharpMin_eq_h (m h : ℝ) (hm : m ≤ h) : rotSharpMin m h = h := by
  simp [rotSharpMin, hm]

theorem rotSharpMin_quadratic (m h : ℝ) (hm : m > h) (hh : 0 ≤ h) :
    2 * rotSharpMin m h ^ 4 - (m ^ 2 + 2 * h ^ 2) * rotSharpMin m h ^ 2 + h ^ 4 = 0 := by
  have hR : 0 ≤ radR m h := by
    unfold radR
    exact (rotSharpMin_radical_nonneg m h hm hh).le
  have hS : 0 ≤ radS m h := by
    unfold radS
    positivity
  have hW : (Real.sqrt (radR m h)) ^ 2 = radR m h := Real.sq_sqrt hR
  have hB : rotSharpMin m h = (1 / 2) * Real.sqrt (radS m h) := by
    simp [rotSharpMin, hm, radS, radR]
  have hB2 : ((1 / 2 : ℝ) * Real.sqrt (radS m h)) ^ 2 = (1 / 4) * radS m h := by
    rw [mul_pow, Real.sq_sqrt hS]
    ring
  have hB4 : ((1 / 2 : ℝ) * Real.sqrt (radS m h)) ^ 4 = (1 / 16) * radS m h ^ 2 := by
    calc ((1 / 2) * Real.sqrt (radS m h)) ^ 4
        = (((1 / 2) * Real.sqrt (radS m h)) ^ 2) ^ 2 := by ring
      _ = ((1 / 4) * radS m h) ^ 2 := by rw [hB2]
      _ = (1 / 16) * radS m h ^ 2 := by ring
  rw [hB, hB4, hB2]
  field_simp
  unfold radS radR at *
  ring_nf at *
  nlinarith [hW]

theorem rotSharpMin_bounds (m h : ℝ) (hm : m > h) (hh : 0 ≤ h) :
    h < rotSharpMin m h ∧ rotSharpMin m h ≤ m := by
  have hdiff : 0 < m ^ 2 - h ^ 2 := by
    have hprod : 0 < (m - h) * (m + h) := mul_pos (sub_pos.mpr hm) (by linarith)
    nlinarith

  have hR4 : h ^ 4 < radR m h := by
    have h1 : 0 < m ^ 4 - h ^ 4 := by
      have hsum : 0 < m ^ 2 + h ^ 2 := by nlinarith [sq_nonneg h]
      have hprod : 0 < (m ^ 2 - h ^ 2) * (m ^ 2 + h ^ 2) := mul_pos hdiff hsum
      nlinarith
    have h2 : 0 ≤ m ^ 2 * h ^ 2 - h ^ 4 := by
      nlinarith [mul_nonneg (sq_nonneg h) (le_of_lt hdiff)]
    unfold radR
    nlinarith

  have hW : h ^ 2 < Real.sqrt (radR m h) := by
    have h1 := Real.sqrt_lt_sqrt (by positivity) hR4
    rw [show h ^ 4 = (h ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (sq_nonneg h)] at h1
    exact h1

  have hS4 : 4 * h ^ 2 < radS m h := by
    unfold radS
    nlinarith
  have hq : 0 ≤ 3 * m ^ 2 - 2 * h ^ 2 := by nlinarith [sq_nonneg h]
  have hsq : (3 * m ^ 2 - 2 * h ^ 2) ^ 2 - radR m h = 8 * (m ^ 2 - h ^ 2) ^ 2 := by
    unfold radR
    ring
  have hRle : radR m h ≤ (3 * m ^ 2 - 2 * h ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (m ^ 2 - h ^ 2)]
  have hWle : Real.sqrt (radR m h) ≤ 3 * m ^ 2 - 2 * h ^ 2 := by
    have h1 := Real.sqrt_le_sqrt hRle
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hq] at h1
    exact h1
  have hS4m : radS m h ≤ 4 * m ^ 2 := by
    unfold radS
    nlinarith

  have hS0 : 0 ≤ radS m h := by
    unfold radS
    positivity
  have hB : rotSharpMin m h = (1 / 2) * Real.sqrt (radS m h) := by
    simp [rotSharpMin, hm, radS, radR]
  have hB0 : 0 ≤ rotSharpMin m h := by
    rw [hB]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hB2 : 4 * rotSharpMin m h ^ 2 = radS m h := by
    rw [hB, mul_pow, Real.sq_sqrt hS0]
    ring
  constructor
  · have hb2 : h ^ 2 < rotSharpMin m h ^ 2 := by nlinarith
    have h1 := Real.sqrt_lt_sqrt (sq_nonneg h) hb2
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hh,
      abs_of_nonneg hB0] at h1
    exact h1
  · have hm0 : 0 < m := lt_of_le_of_lt hh hm
    have hb2 : rotSharpMin m h ^ 2 ≤ m ^ 2 := by nlinarith
    have h1 := Real.sqrt_le_sqrt hb2
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hB0,
      abs_of_nonneg (le_of_lt hm0)] at h1
    exact h1

private theorem sharp_identity (m h : ℝ) (hm : m > h) (hh : 0 ≤ h) :
    (rotSharpMin m h ^ 2 - h ^ 2) ^ 2
      = rotSharpMin m h ^ 2 * (m ^ 2 - rotSharpMin m h ^ 2) := by
  have hq := rotSharpMin_quadratic m h hm hh
  nlinarith [hq]

private theorem sharp_sqrt_x (m h : ℝ) (hm : m > h) (hh : 0 ≤ h) :
    Real.sqrt (m ^ 2 - rotSharpMin m h ^ 2)
      = (rotSharpMin m h ^ 2 - h ^ 2) / rotSharpMin m h := by
  have hb := rotSharpMin_bounds m h hm hh
  have hB0 : 0 < rotSharpMin m h := by linarith [hb.1, hh]
  have hX0 : 0 ≤ m ^ 2 - rotSharpMin m h ^ 2 := by
    have hprod : 0 ≤ (m - rotSharpMin m h) * (m + rotSharpMin m h) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hnum : 0 ≤ rotSharpMin m h ^ 2 - h ^ 2 := by nlinarith [hb.1, hh]
  have hid := sharp_identity m h hm hh
  have hX : m ^ 2 - rotSharpMin m h ^ 2
      = (rotSharpMin m h ^ 2 - h ^ 2) ^ 2 / rotSharpMin m h ^ 2 := by
    rw [eq_div_iff (ne_of_gt (sq_pos_of_pos hB0))]
    nlinarith [hid]
  have hsq : ((rotSharpMin m h ^ 2 - h ^ 2) / rotSharpMin m h) ^ 2
      = (rotSharpMin m h ^ 2 - h ^ 2) ^ 2 / rotSharpMin m h ^ 2 := by
    field_simp [ne_of_gt (sq_pos_of_pos hB0)]
  rw [Real.sqrt_eq_iff_eq_sq hX0 (by positivity)]
  rw [hX, hsq]

private theorem sharp_sqrt_x4h2 (m h : ℝ) (hm : m > h) (hh : 0 ≤ h) :
    Real.sqrt (m ^ 2 - rotSharpMin m h ^ 2 + 4 * h ^ 2)
      = (rotSharpMin m h ^ 2 + h ^ 2) / rotSharpMin m h := by
  have hb := rotSharpMin_bounds m h hm hh
  have hB0 : 0 < rotSharpMin m h := by linarith [hb.1, hh]
  have hX0 : 0 ≤ m ^ 2 - rotSharpMin m h ^ 2 := by
    have hprod : 0 ≤ (m - rotSharpMin m h) * (m + rotSharpMin m h) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hY0 : 0 ≤ m ^ 2 - rotSharpMin m h ^ 2 + 4 * h ^ 2 := by
    have : 0 ≤ 4 * h ^ 2 := by positivity
    linarith
  have hid := sharp_identity m h hm hh
  have hX : m ^ 2 - rotSharpMin m h ^ 2
      = (rotSharpMin m h ^ 2 - h ^ 2) ^ 2 / rotSharpMin m h ^ 2 := by
    rw [eq_div_iff (ne_of_gt (sq_pos_of_pos hB0))]
    nlinarith [hid]
  have hY : m ^ 2 - rotSharpMin m h ^ 2 + 4 * h ^ 2
      = (rotSharpMin m h ^ 2 + h ^ 2) ^ 2 / rotSharpMin m h ^ 2 := by
    rw [hX]
    field_simp [ne_of_gt (sq_pos_of_pos hB0)]; ring
  have hsq : ((rotSharpMin m h ^ 2 + h ^ 2) / rotSharpMin m h) ^ 2
      = (rotSharpMin m h ^ 2 + h ^ 2) ^ 2 / rotSharpMin m h ^ 2 := by
    field_simp [ne_of_gt (sq_pos_of_pos hB0)]
  rw [Real.sqrt_eq_iff_eq_sq hY0 (by positivity)]
  rw [hY, hsq]

private theorem arcCoupling_at_one (s c j : ℝ) (hc0 : 0 ≤ c) (hj0 : 0 ≤ j) :
    rotArcCoupling s c j 1 = rotH c j := by
  have hh : 0 ≤ rotH c j := by
    simp only [rotH]
    refine div_nonneg (mul_nonneg (by norm_num) hj0) ?_
    linarith
  simp only [rotArcCoupling]
  have h1 : (1 : ℝ) - (1 : ℝ) ^ 2 = 0 := by ring
  simp only [h1, Real.sqrt_zero, mul_zero, zero_add, add_zero]
  rw [show (4 : ℝ) * rotH c j ^ 2 = (2 * rotH c j) ^ 2 by ring, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num) hh)]
  ring

theorem rotSharpMin_crossing (s c j : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c)
    (_hc1 : c ≤ 1) (hj0 : 0 ≤ j) (hmh : rotM s c > rotH c j) :
    rotArcCoupling s c j (rotSharpMin (rotM s c) (rotH c j) / rotM s c)
        = rotSharpMin (rotM s c) (rotH c j)
      ∧ rotArcDirect s c (rotSharpMin (rotM s c) (rotH c j) / rotM s c)
        = rotSharpMin (rotM s c) (rotH c j) := by
  have hm_pos : 0 < rotM s c := rotM_pos s c hs0 hs1 hc0
  have hh0 : 0 ≤ rotH c j := by
    simp only [rotH]
    refine div_nonneg (mul_nonneg (by norm_num) hj0) ?_
    linarith
  have hb := rotSharpMin_bounds (rotM s c) (rotH c j) hmh hh0
  have hB0 : 0 < rotSharpMin (rotM s c) (rotH c j) := by linarith [hb.1, hh0]
  have hX0 : 0 ≤ rotM s c ^ 2 - rotSharpMin (rotM s c) (rotH c j) ^ 2 := by
    have hprod : 0 ≤ (rotM s c - rotSharpMin (rotM s c) (rotH c j))
        * (rotM s c + rotSharpMin (rotM s c) (rotH c j)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hv_le : rotSharpMin (rotM s c) (rotH c j) / rotM s c ≤ 1 := by
    rw [div_le_one hm_pos]
    exact hb.2
  have h1v : 0 ≤ 1 - (rotSharpMin (rotM s c) (rotH c j) / rotM s c) ^ 2 := by
    have hv0 : 0 ≤ rotSharpMin (rotM s c) (rotH c j) / rotM s c := by
      exact div_nonneg hB0.le hm_pos.le
    have hsq := mul_self_le_mul_self hv0 hv_le
    nlinarith
  have hone : 1 - (rotSharpMin (rotM s c) (rotH c j) / rotM s c) ^ 2
      = (rotM s c ^ 2 - rotSharpMin (rotM s c) (rotH c j) ^ 2) / rotM s c ^ 2 := by
    rw [div_pow]
    field_simp [ne_of_gt (sq_pos_of_pos hm_pos)]
  have harg1 : rotM s c ^ 2 * (1 - (rotSharpMin (rotM s c) (rotH c j) / rotM s c) ^ 2)
      + 4 * rotH c j ^ 2
      = (rotM s c ^ 2 - rotSharpMin (rotM s c) (rotH c j) ^ 2) + 4 * rotH c j ^ 2 := by
    rw [hone]
    have hcancel : rotM s c ^ 2 * ((rotM s c ^ 2 - rotSharpMin (rotM s c) (rotH c j) ^ 2)
        / rotM s c ^ 2) = rotM s c ^ 2 - rotSharpMin (rotM s c) (rotH c j) ^ 2 := by
      field_simp [ne_of_gt (sq_pos_of_pos hm_pos)]
    rw [hcancel]
  have hsq1 : Real.sqrt (1 - (rotSharpMin (rotM s c) (rotH c j) / rotM s c) ^ 2)
      = Real.sqrt (rotM s c ^ 2 - rotSharpMin (rotM s c) (rotH c j) ^ 2) / rotM s c := by
    rw [Real.sqrt_eq_iff_eq_sq h1v (by positivity)]
    rw [hone, div_pow, Real.sq_sqrt hX0]
  have hcancel : rotM s c
      * (Real.sqrt (rotM s c ^ 2 - rotSharpMin (rotM s c) (rotH c j) ^ 2) / rotM s c)
      = Real.sqrt (rotM s c ^ 2 - rotSharpMin (rotM s c) (rotH c j) ^ 2) := by
    field_simp [ne_of_gt hm_pos]
  have hcouple : rotArcCoupling s c j (rotSharpMin (rotM s c) (rotH c j) / rotM s c)
      = rotSharpMin (rotM s c) (rotH c j) := by
    simp only [rotArcCoupling]
    rw [harg1, hsq1, hcancel]
    rw [sharp_sqrt_x4h2 (rotM s c) (rotH c j) hmh hh0]
    rw [sharp_sqrt_x (rotM s c) (rotH c j) hmh hh0]
    field_simp [ne_of_gt hB0]
    ring
  have hdirect : rotArcDirect s c (rotSharpMin (rotM s c) (rotH c j) / rotM s c)
      = rotSharpMin (rotM s c) (rotH c j) := by
    simp only [rotArcDirect]
    field_simp [ne_of_gt hm_pos]
  exact ⟨hcouple, hdirect⟩

theorem rotSharpMin_arg_mem (m h : ℝ) (hm0 : 0 ≤ m) (hh0 : 0 ≤ h) :
    0 ≤ rotSharpMinArg m h ∧ rotSharpMinArg m h ≤ 1 := by
  by_cases hmh : m ≤ h
  · simp [rotSharpMinArg, hmh]
  · have hmh' : m > h := lt_of_not_ge hmh
    have hm_pos : 0 < m := lt_of_le_of_lt hh0 hmh'
    have hb := rotSharpMin_bounds m h hmh' hh0
    have hB0 : 0 < rotSharpMin m h := by linarith [hb.1, hh0]
    simp [rotSharpMinArg, hmh]
    constructor
    · exact div_nonneg (le_of_lt hB0) hm0
    · rw [div_le_one hm_pos]
      exact hb.2

theorem rotSharpMin_le_arc (s c j v : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hj0 : 0 ≤ j) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    max (rotArcDirect s c v) (rotArcCoupling s c j v) ≥ rotSharpMin (rotM s c) (rotH c j) := by
  have hm_pos : 0 < rotM s c := rotM_pos s c hs0 hs1 hc0
  have hh0 : 0 ≤ rotH c j := by
    simp only [rotH]
    refine div_nonneg (mul_nonneg (by norm_num) hj0) ?_
    linarith
  by_cases hmh : rotM s c > rotH c j
  · have hcross := rotSharpMin_crossing s c j hs0 hs1 hc0 hc1 hj0 hmh
    have harg : rotSharpMinArg (rotM s c) (rotH c j)
        = rotSharpMin (rotM s c) (rotH c j) / rotM s c := by
      simp [rotSharpMinArg, not_le.mpr hmh]
    have hargmem := rotSharpMin_arg_mem (rotM s c) (rotH c j) (le_of_lt hm_pos) hh0
    by_cases hveq : v = rotSharpMinArg (rotM s c) (rotH c j)
    · rw [hveq, harg, hcross.1, hcross.2]
      exact le_max_left _ _
    · by_cases hlt : v < rotSharpMinArg (rotM s c) (rotH c j)
      · have hdec := rotArcCoupling_strict_decreasing s c j
          (rotSharpMinArg (rotM s c) (rotH c j)) v hs0 hs1 hc0 hc1 hj0
          hargmem.1 hargmem.2 hv0 hlt
        have hcs : rotArcCoupling s c j (rotSharpMinArg (rotM s c) (rotH c j))
            = rotSharpMin (rotM s c) (rotH c j) := by
          rw [harg]
          exact hcross.1
        have hmax : rotArcCoupling s c j v
            ≤ max (rotArcDirect s c v) (rotArcCoupling s c j v) := le_max_right _ _
        linarith
      · have hgt : rotSharpMinArg (rotM s c) (rotH c j) < v :=
          lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hveq)
        have hdv : rotArcDirect s c v = rotM s c * v := by simp [rotArcDirect]
        have hmulstar : rotM s c * rotSharpMinArg (rotM s c) (rotH c j)
            = rotSharpMin (rotM s c) (rotH c j) := by
          rw [harg]
          field_simp [ne_of_gt hm_pos]
        have hmax : rotArcDirect s c v
            ≤ max (rotArcDirect s c v) (rotArcCoupling s c j v) := le_max_left _ _
        have hmul : rotM s c * v > rotM s c * rotSharpMinArg (rotM s c) (rotH c j) :=
          mul_lt_mul_of_pos_left hgt hm_pos
        rw [hdv] at hmax ⊢
        linarith
  · have hBh : rotSharpMin (rotM s c) (rotH c j) = rotH c j :=
      rotSharpMin_eq_h _ _ (le_of_not_gt hmh)
    have hone := arcCoupling_at_one s c j hc0 hj0
    by_cases hveq : v = 1
    · rw [hveq, hone, hBh]
      exact le_max_right _ _
    · have hlt : v < 1 := lt_of_le_of_ne hv1 hveq
      have hdec := rotArcCoupling_strict_decreasing s c j 1 v hs0 hs1 hc0 hc1 hj0
        (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) hv0 hlt
      have hmax : rotArcCoupling s c j v
          ≤ max (rotArcDirect s c v) (rotArcCoupling s c j v) := le_max_right _ _
      linarith

theorem rotSharpMin_attained (s c j : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hj0 : 0 ≤ j) :
    max (rotArcDirect s c (rotSharpMinArg (rotM s c) (rotH c j)))
      (rotArcCoupling s c j (rotSharpMinArg (rotM s c) (rotH c j)))
      = rotSharpMin (rotM s c) (rotH c j) := by
  have hm_pos : 0 < rotM s c := rotM_pos s c hs0 hs1 hc0
  have hh0 : 0 ≤ rotH c j := by
    simp only [rotH]
    refine div_nonneg (mul_nonneg (by norm_num) hj0) ?_
    linarith
  by_cases hmh : rotM s c > rotH c j
  · have hcross := rotSharpMin_crossing s c j hs0 hs1 hc0 hc1 hj0 hmh
    have harg : rotSharpMinArg (rotM s c) (rotH c j)
        = rotSharpMin (rotM s c) (rotH c j) / rotM s c := by
      simp [rotSharpMinArg, not_le.mpr hmh]
    rw [harg, hcross.1, hcross.2]
    simp
  · have hBh : rotSharpMin (rotM s c) (rotH c j) = rotH c j :=
      rotSharpMin_eq_h _ _ (le_of_not_gt hmh)
    have hone := arcCoupling_at_one s c j hc0 hj0
    have harg : rotSharpMinArg (rotM s c) (rotH c j) = 1 := by
      simp [rotSharpMinArg, le_of_not_gt hmh]
    rw [harg, hone, hBh]
    have h1 : rotArcDirect s c 1 = rotM s c := by simp [rotArcDirect]
    rw [h1]
    exact max_eq_right (le_of_not_gt hmh)

theorem rotSharpMin_unique (s c j v : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hj0 : 0 ≤ j) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hne : v ≠ rotSharpMinArg (rotM s c) (rotH c j)) :
    max (rotArcDirect s c v) (rotArcCoupling s c j v) > rotSharpMin (rotM s c) (rotH c j) := by
  have hm_pos : 0 < rotM s c := rotM_pos s c hs0 hs1 hc0
  have hh0 : 0 ≤ rotH c j := by
    simp only [rotH]
    refine div_nonneg (mul_nonneg (by norm_num) hj0) ?_
    linarith
  by_cases hmh : rotM s c > rotH c j
  · have hcross := rotSharpMin_crossing s c j hs0 hs1 hc0 hc1 hj0 hmh
    have harg : rotSharpMinArg (rotM s c) (rotH c j)
        = rotSharpMin (rotM s c) (rotH c j) / rotM s c := by
      simp [rotSharpMinArg, not_le.mpr hmh]
    have hargmem := rotSharpMin_arg_mem (rotM s c) (rotH c j) (le_of_lt hm_pos) hh0
    by_cases hlt : v < rotSharpMinArg (rotM s c) (rotH c j)
    · have hdec := rotArcCoupling_strict_decreasing s c j
        (rotSharpMinArg (rotM s c) (rotH c j)) v hs0 hs1 hc0 hc1 hj0
        hargmem.1 hargmem.2 hv0 hlt
      have hcs : rotArcCoupling s c j (rotSharpMinArg (rotM s c) (rotH c j))
          = rotSharpMin (rotM s c) (rotH c j) := by
        rw [harg]
        exact hcross.1
      have hmax : rotArcCoupling s c j v
          ≤ max (rotArcDirect s c v) (rotArcCoupling s c j v) := le_max_right _ _
      linarith
    · have hgt : rotSharpMinArg (rotM s c) (rotH c j) < v :=
        lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
      have hdv : rotArcDirect s c v = rotM s c * v := by simp [rotArcDirect]
      have hmulstar : rotM s c * rotSharpMinArg (rotM s c) (rotH c j)
          = rotSharpMin (rotM s c) (rotH c j) := by
        rw [harg]
        field_simp [ne_of_gt hm_pos]
      have hmax : rotArcDirect s c v
          ≤ max (rotArcDirect s c v) (rotArcCoupling s c j v) := le_max_left _ _
      have hmul : rotM s c * v > rotM s c * rotSharpMinArg (rotM s c) (rotH c j) :=
        mul_lt_mul_of_pos_left hgt hm_pos
      rw [hdv] at hmax ⊢
      linarith
  · have hBh : rotSharpMin (rotM s c) (rotH c j) = rotH c j :=
      rotSharpMin_eq_h _ _ (le_of_not_gt hmh)
    have hone := arcCoupling_at_one s c j hc0 hj0
    have harg : rotSharpMinArg (rotM s c) (rotH c j) = 1 := by
      simp [rotSharpMinArg, le_of_not_gt hmh]
    rw [harg] at hne
    have hlt : v < 1 := lt_of_le_of_ne hv1 hne
    have hdec := rotArcCoupling_strict_decreasing s c j 1 v hs0 hs1 hc0 hc1 hj0
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) hv0 hlt
    have hmax : rotArcCoupling s c j v
        ≤ max (rotArcDirect s c v) (rotArcCoupling s c j v) := le_max_right _ _
    linarith

theorem rotSharpMin_le_two_of_m_le_two (s c j : ℝ) (_hs0 : 0 < s) (_hs1 : s < 1)
    (hc0 : 0 ≤ c) (_hc1 : c ≤ 1) (hj0 : 0 ≤ j) (hjc : j ^ 2 + c ^ 2 = 1)
    (hm : rotM s c ≤ 2) :
    rotSharpMin (rotM s c) (rotH c j) ≤ 2 := by
  have h1c : 0 < 1 + c := by linarith
  have hj1 : j ≤ 1 := by nlinarith [hjc, sq_nonneg c, sq_nonneg (j - 1)]
  rcases le_or_gt (rotM s c) (rotH c j) with hle | hgt
  · rw [rotSharpMin_eq_h _ _ hle]
    have hhj : 2 * j ≤ 2 * (1 + c) := by linarith
    rw [rotH]
    exact (div_le_iff₀ h1c).mpr hhj
  · have hh0 : 0 ≤ rotH c j := by
      rw [rotH]
      exact div_nonneg (mul_nonneg (by norm_num) hj0) h1c.le
    have hb := rotSharpMin_bounds (rotM s c) (rotH c j) hgt hh0
    linarith

theorem rotSharpMin_global_lower (s r c j x v : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hj0 : 0 ≤ j) (hjc : j ^ 2 + c ^ 2 = 1) (hd : rotDomain s c x v)
    (hB : rotSharpMin (rotM s c) (rotH c j) ≤ 2) :
    max (rotDirect (rotReducedScalars s r c j x) v)
      (rotCoupling (rotReducedScalars s r c j x) v)
      ≥ rotSharpMin (rotM s c) (rotH c j) := by
  have hFne : rotF s c x (Real.sqrt (1 - x ^ 2)) ≠ 0 := hd.2.2.2.2
  rcases rotDenominator_cases s c x hFne with hFpos | hFneg
  ·
    have hdir := dominance_pos_direct s r c j x v hd hFpos hr0 hc0 hc1
    have ht := dominance_pos_t s r c j x v hd hFpos hr0 hrs hs0 hs1 hc0
    have hcq := dominance_pos_coupling s r c j x v hd hFpos hr0 hrs hs0 hs1 hc0
    have hv0 : 0 ≤ v := hd.2.2.1
    have hv1 : v ≤ 1 := hd.2.2.2.1
    have hdir' : rotDirect (rotReducedScalars s r c j x) v ≥ rotArcDirect s c v := by
      have h2 : 2 * |(rotReducedScalars s r c j x).t| * v ≥ rotM s c * v :=
        mul_le_mul_of_nonneg_right ht hv0
      rw [rotArcDirect]
      linarith
    have h1 : rotArcDirect s c v
        ≤ max (rotDirect (rotReducedScalars s r c j x) v)
          (rotCoupling (rotReducedScalars s r c j x) v) :=
      le_trans hdir' (le_max_left _ _)
    have h2 : rotArcCoupling s c j v
        ≤ max (rotDirect (rotReducedScalars s r c j x) v)
          (rotCoupling (rotReducedScalars s r c j x) v) :=
      le_trans hcq (le_max_right _ _)
    have hmax : max (rotArcDirect s c v) (rotArcCoupling s c j v)
        ≤ max (rotDirect (rotReducedScalars s r c j x) v)
          (rotCoupling (rotReducedScalars s r c j x) v) := max_le_iff.mpr ⟨h1, h2⟩
    have harc := rotSharpMin_le_arc s c j v hs0 hs1 hc0 hc1 hj0 hv0 hv1
    linarith
  ·
    have hgt := rotDirect_gt_two_negF s r c j x v hd hFneg hr0 hrs hs0 hs1 hj0 hjc
    have hle : rotDirect (rotReducedScalars s r c j x) v
        ≤ max (rotDirect (rotReducedScalars s r c j x) v)
          (rotCoupling (rotReducedScalars s r c j x) v) :=
      le_max_left _ _
    linarith

theorem rotSharpMin_image_lower (cfg : Config) (s r c j : ℝ) (hs0 : 0 < s)
    (hs1 : s < 1) (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hj0 : 0 ≤ j) (hjc : j ^ 2 + c ^ 2 = 1)
    (heta : cfg.upper.eta = cfg.vac.eta0)
    (hB : rotSharpMin (rotM s c) (rotH c j) ≤ 2) (b : ℝ × ℝ)
    (hb : b ∈ physicalResourceImage cfg s r c j) :
    max b.1 b.2 ≥ rotSharpMin (rotM s c) (rotH c j) := by
  obtain ⟨x, v, hd, rfl⟩ := (exact_physical_resource_image cfg s r c j hrs hjc heta b).mp hb
  exact rotSharpMin_global_lower s r c j x v hs0 hs1 hr0 hrs hc0 hc1 hj0 hjc hd hB

theorem rotSharpMin_image_attained (cfg : Config) (s r c j : ℝ) (hs0 : 0 < s)
    (hs1 : s < 1) (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hj0 : 0 ≤ j) (hjc : j ^ 2 + c ^ 2 = 1)
    (heta : cfg.upper.eta = cfg.vac.eta0) :
    ∃ b ∈ physicalResourceImage cfg s r c j,
      max b.1 b.2 = rotSharpMin (rotM s c) (rotH c j) := by
  set v0 : ℝ := rotSharpMinArg (rotM s c) (rotH c j) with hv0def
  have hmpos : 0 < rotM s c := rotM_pos s c hs0 hs1 hc0
  have hden : 0 < 1 + c := by linarith
  have hhpos : 0 ≤ rotH c j := by
    rw [rotH]
    exact div_nonneg (mul_nonneg (by norm_num) hj0) (le_of_lt hden)
  have harg : 0 ≤ rotSharpMinArg (rotM s c) (rotH c j)
      ∧ rotSharpMinArg (rotM s c) (rotH c j) ≤ 1 :=
    rotSharpMin_arg_mem (rotM s c) (rotH c j) (le_of_lt hmpos) hhpos
  have hF : rotF s c 1 (Real.sqrt (1 - 1 ^ 2)) = (1 + s) * (1 + c) ^ 2 := by
    rw [rotF]
    have hsq0 : Real.sqrt (1 - 1 ^ 2) = 0 := by
      have h : (1 : ℝ) ^ 2 = 1 := by norm_num
      rw [h, sub_self, Real.sqrt_zero]
    rw [hsq0]
    ring
  have hFne : rotF s c 1 (Real.sqrt (1 - 1 ^ 2)) ≠ 0 := by
    rw [hF]
    exact mul_ne_zero (ne_of_gt (by linarith : (0 : ℝ) < 1 + s))
      (ne_of_gt (sq_pos_of_pos hden))
  have hd : rotDomain s c 1 v0 :=
    ⟨by norm_num, by norm_num, harg.1, harg.2, hFne⟩
  refine ⟨(rotDirect (rotReducedScalars s r c j 1) v0,
      rotCoupling (rotReducedScalars s r c j 1) v0), ?_, ?_⟩
  · exact (exact_physical_resource_image cfg s r c j hrs hjc heta _).mpr ⟨1, v0, hd, rfl⟩
  · have hd1 : rotDirect (rotReducedScalars s r c j 1) v0 = rotArcDirect s c v0 :=
      centeredArc_direct s r c j v0 hr0 hrs hs0 hs1 hc0 harg.1 harg.2
    have hd2 : rotCoupling (rotReducedScalars s r c j 1) v0 = rotArcCoupling s c j v0 :=
      centeredArc_coupling s r c j v0 hr0 hrs hs0 hs1 hc0 harg.1 harg.2
    rw [hd1, hd2, hv0def]
    exact rotSharpMin_attained s c j hs0 hs1 hc0 hc1 hj0

theorem rotSharpMin_aligned (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    rotSharpMin (rotM s 1) (rotH 1 0) = Real.sqrt 2 * rotRho s := by
  have hρpos : 0 < rotRho s := rotRho_pos s hs0 hs1
  have hm : rotM s 1 = 2 * rotRho s := by
    rw [rotM]
    ring
  have hh : rotH 1 0 = 0 := by
    rw [rotH]
    ring
  have hmpos : 0 < rotM s 1 := by rw [hm]; linarith
  have h4 : Real.sqrt (rotM s 1 ^ 4) = rotM s 1 ^ 2 := by
    rw [show rotM s 1 ^ 4 = (rotM s 1 ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
  have hhz2 : rotH 1 0 ^ 2 = 0 := by
    rw [hh]
    norm_num
  have hhz4 : rotH 1 0 ^ 4 = 0 := by
    rw [hh]
    norm_num
  have hrad : rotM s 1 ^ 4 + 4 * rotM s 1 ^ 2 * rotH 1 0 ^ 2 - 4 * rotH 1 0 ^ 4
      = rotM s 1 ^ 4 := by
    rw [hhz2, hhz4]
    ring
  have hsq : Real.sqrt (rotM s 1 ^ 2 + rotM s 1 ^ 2) = Real.sqrt 2 * rotM s 1 := by
    have h1 : rotM s 1 ^ 2 + rotM s 1 ^ 2 = 2 * rotM s 1 ^ 2 := by ring
    rw [h1, Real.sqrt_mul (by norm_num) (rotM s 1 ^ 2), Real.sqrt_sq_eq_abs,
      abs_of_pos hmpos]
  rw [rotSharpMin]
  have hnotle : ¬ (rotM s 1 ≤ rotH 1 0) := by
    rw [hm, hh]
    linarith
  by_cases hle : rotM s 1 ≤ rotH 1 0
  · rw [ite_eq_left hle]
    exact (hnotle hle).elim
  · rw [ite_eq_right hle]
    have hout : rotM s 1 ^ 2 + 2 * rotH 1 0 ^ 2
        + Real.sqrt (rotM s 1 ^ 4 + 4 * rotM s 1 ^ 2 * rotH 1 0 ^ 2 - 4 * rotH 1 0 ^ 4)
        = rotM s 1 ^ 2 + rotM s 1 ^ 2 := by
      rw [hrad, hhz2, h4]
      ring
    rw [hout, hsq, hm]
    ring

end GSTC.Scattering.RotatedRankOneRecovery
