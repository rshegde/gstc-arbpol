/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module
public import GSTC.Scattering.RotatedRankOneImage

public section
set_option autoImplicit false
namespace GSTC.Scattering.RotatedRankOneRecovery
open scoped Matrix
open RotatedRankOneResources

@[expose] noncomputable def rotRho (s : ℝ) : ℝ := Real.sqrt ((1 - s) / (1 + s))

@[expose] noncomputable def rotM (s c : ℝ) : ℝ := 4 * rotRho s / (1 + c)

@[expose] noncomputable def rotH (c j : ℝ) : ℝ := 2 * j / (1 + c)

def RotPhysical (s r c j : ℝ) : Prop :=
  0 < s ∧ s < 1 ∧ 0 ≤ r ∧ r ^ 2 + s ^ 2 = 1 ∧
    0 ≤ c ∧ c ≤ 1 ∧ 0 ≤ j ∧ j ^ 2 + c ^ 2 = 1

def rotPosDenominator (s c x : ℝ) : Prop := 0 < rotF s c x (Real.sqrt (1 - x ^ 2))

def rotNegDenominator (s c x : ℝ) : Prop := rotF s c x (Real.sqrt (1 - x ^ 2)) < 0

theorem rotDenominator_cases (s c x : ℝ)
    (hne : rotF s c x (Real.sqrt (1 - x ^ 2)) ≠ 0) :
    rotPosDenominator s c x ∨ rotNegDenominator s c x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · right
    show rotF s c x (Real.sqrt (1 - x ^ 2)) < 0
    exact hlt
  · left
    show 0 < rotF s c x (Real.sqrt (1 - x ^ 2))
    exact hgt

structure ResourcePair where
  direct : ℝ
  coupling : ℝ

def ResourcePair.Dominates (a b : ResourcePair) : Prop :=
  a.direct ≤ b.direct ∧ a.coupling ≤ b.coupling ∧
    (a.direct < b.direct ∨ a.coupling < b.coupling)

@[expose] noncomputable def rotArcDirect (s c v : ℝ) : ℝ := rotM s c * v

@[expose] noncomputable def rotArcCoupling (s c j v : ℝ) : ℝ :=
  (Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
    + rotM s c * Real.sqrt (1 - v ^ 2)) / 2

theorem rotR_eq (s r : ℝ) (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1) : r = rotR s := by
  have hsq : r ^ 2 = 1 - s ^ 2 := by linarith
  calc r = |r| := (abs_of_nonneg hr0).symm
    _ = Real.sqrt (r ^ 2) := (Real.sqrt_sq_eq_abs r).symm
    _ = Real.sqrt (1 - s ^ 2) := by rw [hsq]
    _ = rotR s := rfl

theorem rotRho_pos (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : 0 < rotRho s := by
  have h : 0 < (1 - s) / (1 + s) := div_pos (by linarith) (by linarith)
  simpa only [rotRho] using (Real.sqrt_pos.2 h)

theorem rotRho_le_half (s : ℝ) (hs : 3 / 5 ≤ s) (hs1 : s < 1) : rotRho s ≤ 1 / 2 := by
  have h1 : 0 < 1 + s := by linarith
  have h2 : (1 - s) / (1 + s) ≤ (1 : ℝ) / 4 := by
    rw [div_le_iff₀ h1]
    nlinarith
  have hsq : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by norm_num)]
  have h3 : Real.sqrt ((1 - s) / (1 + s)) ≤ Real.sqrt ((1 : ℝ) / 4) :=
    Real.sqrt_le_sqrt h2
  simpa only [rotRho] using h3.trans_eq hsq

theorem rotM_pos (s c : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c) : 0 < rotM s c := by
  have h := rotRho_pos s hs0 hs1
  have hd : 0 < 1 + c := by linarith
  simp only [rotM]
  exact div_pos (mul_pos (by norm_num) h) hd

theorem rotRho_sq (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    rotRho s ^ 2 = (1 - s) / (1 + s) := by
  have h : 0 ≤ (1 - s) / (1 + s) := div_nonneg (by linarith) (by linarith)
  simp only [rotRho, Real.sq_sqrt h]

theorem rotR_div (s r : ℝ) (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1)
    (hs0 : 0 < s) (hs1 : s < 1) : r / (1 + s) = rotRho s := by
  have h1 : (1 + s) ≠ 0 := by linarith
  have hsq : r ^ 2 = 1 - s ^ 2 := by linarith
  have hsq2 : (r / (1 + s)) ^ 2 = (1 - s) / (1 + s) := by
    rw [div_pow, hsq]
    field_simp [h1]
    ring
  have hRsq : rotRho s ^ 2 = (1 - s) / (1 + s) := rotRho_sq s hs0 hs1
  have heq : (r / (1 + s)) ^ 2 = (rotRho s) ^ 2 := by rw [hsq2, hRsq]
  have hL : 0 ≤ r / (1 + s) := div_nonneg hr0 (by linarith)
  have hR : 0 ≤ rotRho s := Real.sqrt_nonneg _
  exact le_antisymm
    ((sq_le_sq₀ hL hR).mp (le_of_eq heq))
    ((sq_le_sq₀ hR hL).mp (le_of_eq heq.symm))

theorem rotR_div_one_minus (s r : ℝ) (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1)
    (hs0 : 0 < s) (hs1 : s < 1) : r / (1 - s) = 1 / rotRho s := by
  have h1 : (1 - s) ≠ 0 := by linarith
  have hsq : r ^ 2 = 1 - s ^ 2 := by linarith
  have hrho : 0 < rotRho s := rotRho_pos s hs0 hs1
  have hρ : rotRho s ^ 2 = (1 - s) / (1 + s) := rotRho_sq s hs0 hs1
  have hprod : r * rotRho s = 1 - s := by
    have hsq2 : (r * rotRho s) ^ 2 = (1 - s) ^ 2 := by
      rw [mul_pow, hsq, hρ]
      field_simp [ne_of_gt (by linarith : 0 < 1 + s)]
      ring
    have hL : 0 ≤ r * rotRho s := mul_nonneg hr0 (Real.sqrt_nonneg _)
    have hR : 0 ≤ 1 - s := by linarith
    exact le_antisymm
      ((sq_le_sq₀ hL hR).mp (le_of_eq hsq2))
      ((sq_le_sq₀ hR hL).mp (le_of_eq hsq2.symm))
  have hfrac : r * rotRho s / (1 - s) = 1 := by
    rw [hprod]
    field_simp [h1]
  calc r / (1 - s) = (r * rotRho s / (1 - s)) / rotRho s := by
        field_simp [h1, ne_of_gt hrho]
    _ = 1 / rotRho s := by rw [hfrac]

theorem rotReducedScalars_centered (s r c j : ℝ) (hr0 : 0 ≤ r)
    (hrs : r ^ 2 + s ^ 2 = 1) (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c) :
    rotReducedScalars s r c j 1 =
      { p0 := 0, p1 := 0, t := rotM s c / 2, u := rotM s c / 2, w := 0, q := rotH c j } := by
  have h1 : (1 + s) ≠ 0 := by linarith
  have hc1 : (1 + c) ≠ 0 := by linarith
  have hrdiv : r / (1 + s) = rotRho s := rotR_div s r hr0 hrs hs0 hs1
  have hF : rotF s c 1 0 = (1 + s) * (1 + c) ^ 2 := by
    simp [rotF]
  have ht : rotT s r c 1 0 = rotM s c / 2 := by
    have hstep : 2 * r * (1 + c) / ((1 + s) * (1 + c) ^ 2) = 2 * (r / (1 + s)) / (1 + c) := by
      field_simp [hc1, h1]
    rw [rotT, hF, hstep, hrdiv, rotM]
    field_simp [hc1]
    ring
  have hu : rotU s r c 1 0 = rotM s c / 2 := by
    have hstep : 2 * r * (1 + c * 1) / ((1 + s) * (1 + c) ^ 2)
        = 2 * (r / (1 + s)) / (1 + c) := by
      field_simp [hc1, h1]
    rw [rotU, hF, hstep, hrdiv, rotM]
    field_simp [hc1]
    ring
  have hp0 : rotP0 s c 1 0 = 0 := by
    rw [rotP0, hF]
    ring
  have hp1 : rotP1 s c 1 0 = 0 := by
    rw [rotP1, hF]
    ring
  have hw : rotW s r c j 1 0 = 0 := by
    rw [rotW, hF]
    ring
  have hq : rotQ s c j 1 0 = rotH c j := by
    have hstep : 2 * j * (1 + s) * (1 + c) / ((1 + s) * (1 + c) ^ 2)
        = 2 * j / (1 + c) := by
      field_simp [hc1, h1]
    rw [rotQ, hF, hstep]
    rfl
  simp only [rotReducedScalars, rotScalars]
  rw [show Real.sqrt (1 - 1 ^ 2) = 0 by simp, hp0, hp1, ht, hu, hw, hq]

theorem arcPhase_nonneg (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 ≤ 1 - v ^ 2 := by
  have h1 : v * v ≤ v := by
    simpa using (mul_le_mul_of_nonneg_right hv1 hv0)
  nlinarith

theorem centeredArc_direct (s r c j v : ℝ) (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    rotDirect (rotReducedScalars s r c j 1) v = rotArcDirect s c v := by
  have hc : rotReducedScalars s r c j 1 =
      { p0 := 0, p1 := 0, t := rotM s c / 2, u := rotM s c / 2, w := 0, q := rotH c j } :=
    rotReducedScalars_centered s r c j hr0 hrs hs0 hs1 hc0
  have hmm : 0 ≤ rotM s c := le_of_lt (rotM_pos s c hs0 hs1 hc0)
  have hm2 : 0 ≤ rotM s c / 2 := by linarith
  have hX : 0 ≤ (rotM s c / 2) * v := mul_nonneg hm2 hv0
  have hv2 : 0 ≤ 1 - v ^ 2 := arcPhase_nonneg v hv0 hv1
  rw [hc]
  simp only [rotDirect, rotArcDirect]
  have hrad1 : ((rotM s c / 2) * v) ^ 2 + 0 ^ 2 * (1 - v ^ 2)
      = ((rotM s c / 2) * v) ^ 2 := by
    rw [← Real.sq_sqrt hv2]
    ring
  have hbr1 : |0 + (rotM s c / 2) * v|
      + Real.sqrt ((0 + (rotM s c / 2) * v) ^ 2 + 0 ^ 2 * (1 - v ^ 2)) = rotM s c * v := by
    rw [zero_add, hrad1, Real.sqrt_sq hX, abs_of_nonneg hX]
    ring
  have hrad2 : ((0 - (rotM s c / 2) * v)) ^ 2 + 0 ^ 2 * (1 - v ^ 2)
      = ((rotM s c / 2) * v) ^ 2 := by
    rw [← Real.sq_sqrt hv2]
    ring
  have hbr2 : |0 - (rotM s c / 2) * v|
      + Real.sqrt ((0 - (rotM s c / 2) * v) ^ 2 + 0 ^ 2 * (1 - v ^ 2)) = rotM s c * v := by
    rw [hrad2, zero_sub, Real.sqrt_sq_eq_abs, abs_neg, abs_of_nonneg hX]
    ring
  rw [hbr1, hbr2]
  exact max_eq_left (le_refl _)

theorem centeredArc_coupling (s r c j v : ℝ) (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    rotCoupling (rotReducedScalars s r c j 1) v = rotArcCoupling s c j v := by
  have hc : rotReducedScalars s r c j 1 =
      { p0 := 0, p1 := 0, t := rotM s c / 2, u := rotM s c / 2, w := 0, q := rotH c j } :=
    rotReducedScalars_centered s r c j hr0 hrs hs0 hs1 hc0
  have hmm : 0 ≤ rotM s c := le_of_lt (rotM_pos s c hs0 hs1 hc0)
  have hm2 : 0 ≤ rotM s c / 2 := by linarith
  have hv2 : 0 ≤ 1 - v ^ 2 := arcPhase_nonneg v hv0 hv1
  have hfirst : Real.sqrt ((rotM s c / 2) ^ 2 * (1 - v ^ 2) + rotH c j ^ 2)
      = Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2) / 2 := by
    have heq : (rotM s c / 2) ^ 2 * (1 - v ^ 2) + rotH c j ^ 2
        = (1 / 4) * (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2) := by ring
    rw [heq, Real.sqrt_mul (show (0 : ℝ) ≤ 1 / 4 by norm_num) _]
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by ring,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    ring
  have hsecond : Real.sqrt ((rotM s c / 2) ^ 2 * (1 - v ^ 2) + 0 ^ 2)
      = (rotM s c / 2) * Real.sqrt (1 - v ^ 2) := by
    rw [show (0 : ℝ) ^ 2 = 0 by ring, add_zero]
    rw [show (rotM s c / 2) ^ 2 * (1 - v ^ 2) = (1 - v ^ 2) * (rotM s c / 2) ^ 2 by ring]
    rw [Real.sqrt_mul hv2 _]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hm2]
    ring
  rw [hc]
  simp only [rotCoupling, rotArcCoupling]
  rw [hfirst, hsecond]
  ring

theorem abs_add_sub_ge_two_max (a b : ℝ) : |a + b| + |a - b| ≥ 2 * max |a| |b| := by
  have h1 : 2 * |a| ≤ |a + b| + |a - b| := by
    have h := abs_add_le (a + b) (a - b)
    rw [show a + b + (a - b) = 2 * a by ring, abs_mul, abs_two] at h
    exact h
  have h2 : 2 * |b| ≤ |a + b| + |a - b| := by
    have h := abs_add_le (a + b) (-(a - b))
    rw [show a + b + -(a - b) = 2 * b by ring, abs_mul, abs_two, abs_neg] at h
    exact h
  by_cases h : |a| ≤ |b|
  · rw [max_eq_right h]
    exact h2
  · rw [max_eq_left (le_of_not_ge h)]
    exact h1

theorem sqrt_sq_add_le (a b : ℝ) : Real.sqrt (a ^ 2 + b ^ 2) ≥ |a| := by
  have h : a ^ 2 ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg b]
  have h2 := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs] at h2
  exact h2

theorem rotF_le_scaled (s c x : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    (1 + s) * |x + c| * (1 + c) ≥ rotF s c x (Real.sqrt (1 - x ^ 2)) := by
  have h1x2 : 0 ≤ 1 - x ^ 2 := by
    have h1 : 0 ≤ 1 + x := by linarith
    have h2 : 0 ≤ 1 - x := by linarith
    have heq : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
    rw [heq]
    exact mul_nonneg h1 h2
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt h1x2
  have hF : rotF s c x (Real.sqrt (1 - x ^ 2))
      = (1 + s) * (x + c) ^ 2 - (1 - s) * (1 - x ^ 2) := by
    simp only [rotF]
    rw [hsq]
  have habs : |x + c| ≤ 1 + c := by
    have h := abs_add_le x c
    have hx : |x| ≤ 1 := abs_le.mpr ⟨hx0, hx1⟩
    have hc' : |c| = c := abs_of_nonneg hc0
    linarith
  have hsq2 : (x + c) ^ 2 ≤ |x + c| * (1 + c) := by
    have h1 : |x + c| * |x + c| ≤ |x + c| * (1 + c) :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg (x + c))
    calc (x + c) ^ 2 = |x + c| * |x + c| := by rw [← pow_two, sq_abs]
      _ ≤ |x + c| * (1 + c) := h1
  have h3 : (1 + s) * |x + c| * (1 + c) ≥ (1 + s) * (x + c) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hsq2 (by linarith : 0 ≤ 1 + s)
    have hh : (1 + s) * (|x + c| * (1 + c)) = (1 + s) * |x + c| * (1 + c) := by ring
    rw [hh] at h1
    exact h1
  rw [hF]
  have h4 : 0 ≤ (1 - s) * (1 - x ^ 2) := mul_nonneg (by linarith) h1x2
  linarith

theorem rotReducedScalars_t (s r c j x : ℝ) :
    (rotReducedScalars s r c j x).t
      = 2 * r * (x + c) / rotF s c x (Real.sqrt (1 - x ^ 2)) := by
  simp only [rotReducedScalars, rotScalars, rotT]

theorem rotReducedScalars_u (s r c j x : ℝ) :
    (rotReducedScalars s r c j x).u
      = 2 * r * (1 + c * x) / rotF s c x (Real.sqrt (1 - x ^ 2)) := by
  simp only [rotReducedScalars, rotScalars, rotU]

theorem rotReducedScalars_q (s r c j x : ℝ) :
    (rotReducedScalars s r c j x).q
      = 2 * j * (1 + s) * (x + c) / rotF s c x (Real.sqrt (1 - x ^ 2)) := by
  simp only [rotReducedScalars, rotScalars, rotQ]

theorem dominance_pos_u_ge_t (s r c j x v : ℝ) (hd : rotDomain s c x v)
    (hF : rotPosDenominator s c x) (hr0 : 0 ≤ r) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    |(rotReducedScalars s r c j x).u| ≥ |(rotReducedScalars s r c j x).t| := by
  have hx0 : -1 ≤ x := hd.1
  have hx1 : x ≤ 1 := hd.2.1
  have hFpos : 0 < rotF s c x (Real.sqrt (1 - x ^ 2)) := hF
  have h1x2 : 0 ≤ 1 - x ^ 2 := by
    have h1 : 0 ≤ 1 + x := by linarith
    have h2 : 0 ≤ 1 - x := by linarith
    have heq : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
    rw [heq]
    exact mul_nonneg h1 h2
  have h1c : 0 ≤ 1 - c ^ 2 := by
    have h1 : 0 ≤ 1 - c := by linarith
    have h2 : 0 ≤ 1 + c := by linarith
    have heq : 1 - c ^ 2 = (1 - c) * (1 + c) := by ring
    rw [heq]
    exact mul_nonneg h1 h2
  have hprod : 0 ≤ (1 - c ^ 2) * (1 - x ^ 2) := mul_nonneg h1c h1x2
  have hsq : (x + c) ^ 2 ≤ (1 + c * x) ^ 2 := by
    have heq : (1 + c * x) ^ 2 - (x + c) ^ 2 = (1 - c ^ 2) * (1 - x ^ 2) := by ring
    nlinarith [heq, hprod]
  have hsq' : |x + c| ^ 2 ≤ |1 + c * x| ^ 2 := by
    rw [sq_abs, sq_abs]
    exact hsq
  have habs : |x + c| ≤ |1 + c * x| :=
    (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp hsq'
  rw [rotReducedScalars_u, rotReducedScalars_t]
  simp only [abs_div, abs_mul, abs_two, abs_of_nonneg hr0, abs_of_pos hFpos]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left habs (by linarith : 0 ≤ 2 * r))
    (by linarith : 0 ≤ rotF s c x (Real.sqrt (1 - x ^ 2)))

theorem dominance_pos_t (s r c j x v : ℝ) (hd : rotDomain s c x v)
    (hF : rotPosDenominator s c x) (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c) :
    2 * |(rotReducedScalars s r c j x).t| ≥ rotM s c := by
  have hx0 : -1 ≤ x := hd.1
  have hx1 : x ≤ 1 := hd.2.1
  have hFpos : 0 < rotF s c x (Real.sqrt (1 - x ^ 2)) := hF
  have hscale : (1 + s) * |x + c| * (1 + c) ≥ rotF s c x (Real.sqrt (1 - x ^ 2)) :=
    rotF_le_scaled s c x hs0 hs1 hc0 hx0 hx1
  have hD : 0 < (1 + s) * (1 + c) := by nlinarith
  have hle : (2 * r) / ((1 + s) * (1 + c))
      ≤ (2 * r * |x + c|) / rotF s c x (Real.sqrt (1 - x ^ 2)) := by
    rw [div_le_div_iff₀ hD hFpos]
    have hmul := mul_le_mul_of_nonneg_left hscale (by linarith : 0 ≤ 2 * r)
    have hh : (2 * r * |x + c|) * ((1 + s) * (1 + c))
        = (2 * r) * ((1 + s) * |x + c| * (1 + c)) := by ring
    rw [hh]
    exact hmul
  have habsT : |(rotReducedScalars s r c j x).t|
      = (2 * r * |x + c|) / rotF s c x (Real.sqrt (1 - x ^ 2)) := by
    rw [rotReducedScalars_t]
    simp only [abs_div, abs_mul, abs_two, abs_of_nonneg hr0, abs_of_pos hFpos]
  have hρ : rotRho s = r / (1 + s) := (rotR_div s r hr0 hrs hs0 hs1).symm
  have heq : (2 * r) / ((1 + s) * (1 + c)) = rotM s c / 2 := by
    simp only [rotM, hρ]
    have hd1 : (2 * r) / ((1 + s) * (1 + c)) = (2 * r) / (1 + s) / (1 + c) :=
      (div_div _ _ _).symm
    have hd2 : (4 * (r / (1 + s)) / (1 + c)) / 2 = 2 * (r / (1 + s)) / (1 + c) := by ring
    rw [hd1, hd2]
    ring
  have hle' : 2 * |(rotReducedScalars s r c j x).t| ≥ rotM s c := by
    rw [habsT]
    have h2 := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2)
    have h3 : 2 * ((2 * r) / ((1 + s) * (1 + c))) = rotM s c := by rw [heq]; ring
    linarith
  exact hle'

theorem dominance_pos_q_abs (s r c j x v : ℝ) (hd : rotDomain s c x v)
    (hF : rotPosDenominator s c x) (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c) :
    |(rotReducedScalars s r c j x).q| ≥ |rotH c j| := by
  have hx0 : -1 ≤ x := hd.1
  have hx1 : x ≤ 1 := hd.2.1
  have hFpos : 0 < rotF s c x (Real.sqrt (1 - x ^ 2)) := hF
  have hscale : (1 + s) * |x + c| * (1 + c) ≥ rotF s c x (Real.sqrt (1 - x ^ 2)) :=
    rotF_le_scaled s c x hs0 hs1 hc0 hx0 hx1
  have h1c : 0 < 1 + c := by linarith
  have h1s : 0 < 1 + s := by linarith
  have habsQ : |(rotReducedScalars s r c j x).q|
      = (2 * |j| * (1 + s) * |x + c|) / rotF s c x (Real.sqrt (1 - x ^ 2)) := by
    rw [rotReducedScalars_q]
    simp only [abs_div, abs_mul, abs_two, abs_of_pos hFpos, abs_of_pos h1s]
  have habsH : |rotH c j| = (2 * |j|) / (1 + c) := by
    simp only [rotH, abs_div, abs_mul, abs_two, abs_of_pos h1c]
  rw [habsQ, habsH]
  have hdiv : (2 * |j|) / (1 + c)
      ≤ (2 * |j| * (1 + s) * |x + c|) / rotF s c x (Real.sqrt (1 - x ^ 2)) := by
    rw [div_le_div_iff₀ h1c hFpos]
    have hmul := mul_le_mul_of_nonneg_left hscale
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg j))
    have hh : (2 * |j| * (1 + s) * |x + c|) * (1 + c)
        = 2 * |j| * ((1 + s) * |x + c| * (1 + c)) := by ring
    rw [hh]
    exact hmul
  exact hdiv

theorem dominance_pos_q (s r c j x v : ℝ) (hd : rotDomain s c x v)
    (hF : rotPosDenominator s c x) (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c) :
    |(rotReducedScalars s r c j x).q| ≥ rotH c j := by
  have h := dominance_pos_q_abs s r c j x v hd hF hs0 hs1 hc0
  exact le_trans (le_abs_self (rotH c j)) h

theorem rotDirect_ge (sc : RotScalars) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hut : |sc.u| ≥ |sc.t|) :
    rotDirect sc v ≥ 2 * |sc.t| * v := by
  have hv2 : 0 ≤ 1 - v ^ 2 := by
    have h1 : 0 ≤ 1 + v := by linarith
    have h2 : 0 ≤ 1 - v := by linarith
    have heq : 1 - v ^ 2 = (1 + v) * (1 - v) := by ring
    rw [heq]
    exact mul_nonneg h1 h2
  have hsq : (Real.sqrt (1 - v ^ 2)) ^ 2 = 1 - v ^ 2 := Real.sq_sqrt hv2
  have hw : (sc.w * Real.sqrt (1 - v ^ 2)) ^ 2 = sc.w ^ 2 * (1 - v ^ 2) := by
    have h2 : (sc.w * Real.sqrt (1 - v ^ 2)) ^ 2
        = (sc.w ^ 2) * ((Real.sqrt (1 - v ^ 2)) ^ 2) := by ring
    rw [h2, hsq]
  have hB1 : Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
      ≥ |sc.p1 + sc.u * v| := by
    have h := sqrt_sq_add_le (sc.p1 + sc.u * v) (sc.w * Real.sqrt (1 - v ^ 2))
    rw [hw] at h
    exact h
  have hB2 : Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
      ≥ |sc.p1 - sc.u * v| := by
    have h := sqrt_sq_add_le (sc.p1 - sc.u * v) (sc.w * Real.sqrt (1 - v ^ 2))
    rw [hw] at h
    exact h
  have hA : |sc.p0 + sc.t * v| + |sc.p0 - sc.t * v| ≥ 2 * (max |sc.p0| (|sc.t| * v)) := by
    have h := abs_add_sub_ge_two_max sc.p0 (sc.t * v)
    rwa [abs_mul, abs_of_nonneg hv0] at h
  have hC : |sc.p1 + sc.u * v| + |sc.p1 - sc.u * v| ≥ 2 * (max |sc.p1| (|sc.u| * v)) := by
    have h := abs_add_sub_ge_two_max sc.p1 (sc.u * v)
    rwa [abs_mul, abs_of_nonneg hv0] at h
  simp only [rotDirect]
  have hhalf : (|sc.p0 + sc.t * v|
        + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
        + (|sc.p0 - sc.t * v|
        + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)))) / 2
      ≤ max (|sc.p0 + sc.t * v|
        + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)))
        (|sc.p0 - sc.t * v|
        + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))) := by
    have h1 : |sc.p0 + sc.t * v|
          + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
        ≤ max (|sc.p0 + sc.t * v|
          + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)))
          (|sc.p0 - sc.t * v|
          + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))) :=
      le_max_left _ _
    have h2 : |sc.p0 - sc.t * v|
          + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
        ≤ max (|sc.p0 + sc.t * v|
          + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)))
          (|sc.p0 - sc.t * v|
          + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))) :=
      le_max_right _ _
    linarith
  have hsum : (|sc.p0 + sc.t * v|
        + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
        + (|sc.p0 - sc.t * v|
        + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)))) / 2
      ≥ 2 * |sc.t| * v := by
    have h3 : (|sc.p0 + sc.t * v| + |sc.p0 - sc.t * v|) / 2
        ≥ (max |sc.p0| (|sc.t| * v)) := by linarith [hA]
    have h4 : (Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
        + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))) / 2
        ≥ (max |sc.p1| (|sc.u| * v)) := by linarith [hB1, hB2, hC]
    have h5 : (max |sc.p0| (|sc.t| * v)) + (max |sc.p1| (|sc.u| * v))
        ≥ |sc.t| * v + |sc.u| * v := by
      have hm1 := le_max_right |sc.p0| (|sc.t| * v)
      have hm2 := le_max_right |sc.p1| (|sc.u| * v)
      linarith
    have h6 : |sc.u| * v + |sc.t| * v ≥ 2 * |sc.t| * v := by
      have hu := mul_le_mul_of_nonneg_right hut hv0
      linarith
    linarith
  linarith

theorem dominance_pos_direct (s r c j x v : ℝ) (hd : rotDomain s c x v)
    (hF : rotPosDenominator s c x) (hr0 : 0 ≤ r) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    rotDirect (rotReducedScalars s r c j x) v ≥ 2 * |(rotReducedScalars s r c j x).t| * v := by
  have hv := rotDomain_v s c x v hd
  have huv : |(rotReducedScalars s r c j x).u| ≥ |(rotReducedScalars s r c j x).t| :=
    dominance_pos_u_ge_t s r c j x v hd hF hr0 hc0 hc1
  exact rotDirect_ge (rotReducedScalars s r c j x) v hv.1 hv.2 huv

theorem rotCoupling_ge (sc : RotScalars) (s c j v : ℝ) (hv2 : 0 ≤ 1 - v ^ 2)
    (ht : |sc.t| ≥ rotM s c / 2) (hq : |sc.q| ≥ |rotH c j|) (hm : 0 ≤ rotM s c) :
    rotCoupling sc v ≥ rotArcCoupling s c j v := by
  have hM2 : 0 ≤ rotM s c / 2 := by linarith
  have ht2 : sc.t ^ 2 ≥ (rotM s c / 2) ^ 2 := by
    have h1 : (rotM s c / 2) ^ 2 ≤ |sc.t| ^ 2 :=
      (sq_le_sq₀ hM2 (abs_nonneg _)).mpr ht
    have h3 : |sc.t| ^ 2 = sc.t ^ 2 := sq_abs _
    rw [h3] at h1
    exact h1
  have hq2 : sc.q ^ 2 ≥ (rotH c j) ^ 2 := by
    have h1 : |rotH c j| ^ 2 ≤ |sc.q| ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hq
    have h3 : |sc.q| ^ 2 = sc.q ^ 2 := sq_abs _
    rw [h3, sq_abs (rotH c j)] at h1
    exact h1
  have hr1 : sc.t ^ 2 * (1 - v ^ 2) + sc.q ^ 2
      ≥ (rotM s c / 2) ^ 2 * (1 - v ^ 2) + (rotH c j) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right ht2 hv2
    linarith
  have hrad : Real.sqrt ((rotM s c / 2) ^ 2 * (1 - v ^ 2) + (rotH c j) ^ 2)
      = Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * (rotH c j) ^ 2) / 2 := by
    have heq : (rotM s c / 2) ^ 2 * (1 - v ^ 2) + (rotH c j) ^ 2
        = (1 / 4) * (rotM s c ^ 2 * (1 - v ^ 2) + 4 * (rotH c j) ^ 2) := by ring
    rw [heq, Real.sqrt_mul (show (0 : ℝ) ≤ 1 / 4 by norm_num) _]
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by ring,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    ring
  have hr2 : sc.t ^ 2 * (1 - v ^ 2) + sc.w ^ 2
      ≥ (rotM s c / 2) ^ 2 * (1 - v ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_right ht2 hv2
    linarith [sq_nonneg sc.w]
  have hrad2 : Real.sqrt ((rotM s c / 2) ^ 2 * (1 - v ^ 2))
      = (rotM s c / 2) * Real.sqrt (1 - v ^ 2) := by
    rw [show (rotM s c / 2) ^ 2 * (1 - v ^ 2) = (1 - v ^ 2) * (rotM s c / 2) ^ 2 by ring]
    rw [Real.sqrt_mul hv2 _]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hM2]
    ring
  simp only [rotCoupling]
  have h1 : Real.sqrt (sc.t ^ 2 * (1 - v ^ 2) + sc.q ^ 2)
      ≥ Real.sqrt ((rotM s c / 2) ^ 2 * (1 - v ^ 2) + (rotH c j) ^ 2) :=
    Real.sqrt_le_sqrt hr1
  have h2 : Real.sqrt (sc.t ^ 2 * (1 - v ^ 2) + sc.w ^ 2)
      ≥ Real.sqrt ((rotM s c / 2) ^ 2 * (1 - v ^ 2)) := Real.sqrt_le_sqrt hr2
  calc rotArcCoupling s c j v
      = (Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * (rotH c j) ^ 2)
        + rotM s c * Real.sqrt (1 - v ^ 2)) / 2 := rfl
    _ ≤ Real.sqrt ((rotM s c / 2) ^ 2 * (1 - v ^ 2) + (rotH c j) ^ 2)
        + Real.sqrt ((rotM s c / 2) ^ 2 * (1 - v ^ 2)) := by
      rw [hrad, hrad2]
      exact le_of_eq (by ring)
    _ ≤ Real.sqrt (sc.t ^ 2 * (1 - v ^ 2) + sc.q ^ 2)
        + Real.sqrt (sc.t ^ 2 * (1 - v ^ 2) + sc.w ^ 2) :=
      add_le_add h1 h2

theorem dominance_pos_coupling (s r c j x v : ℝ) (hd : rotDomain s c x v)
    (hF : rotPosDenominator s c x) (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c) :
    rotCoupling (rotReducedScalars s r c j x) v ≥ rotArcCoupling s c j v := by
  have hv := rotDomain_v s c x v hd
  have hm : 0 ≤ rotM s c := le_of_lt (rotM_pos s c hs0 hs1 hc0)
  have ht : |(rotReducedScalars s r c j x).t| ≥ rotM s c / 2 := by
    have h := dominance_pos_t s r c j x v hd hF hr0 hrs hs0 hs1 hc0
    linarith
  have hq : |(rotReducedScalars s r c j x).q| ≥ |rotH c j| :=
    dominance_pos_q_abs s r c j x v hd hF hs0 hs1 hc0
  exact rotCoupling_ge (rotReducedScalars s r c j x) s c j v
    (arcPhase_nonneg v hv.1 hv.2) ht hq hm

theorem rotNegBranch_y_pos (s c x : ℝ) (hs0 : 0 < s) (_hs1 : s < 1)
    (hF : rotNegDenominator s c x) : 0 < Real.sqrt (1 - x ^ 2) := by
  have h1s : 0 < 1 + s := by linarith
  have h1m : 0 < 1 - s := by linarith
  have hsq : 0 ≤ (1 + s) * (x + c) ^ 2 := mul_nonneg (le_of_lt h1s) (sq_nonneg (x + c))
  have hF' : (1 + s) * (x + c) ^ 2 - (1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2 < 0 := by
    simpa only [rotNegDenominator, rotF] using hF
  have hlt : (1 + s) * (x + c) ^ 2 < (1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2 := sub_neg.mp hF'
  have hprod : 0 < (1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2 := lt_of_le_of_lt hsq hlt
  rcases mul_pos_iff.mp hprod with hpos | hneg
  · nlinarith [hpos.2, Real.sqrt_nonneg (1 - x ^ 2)]
  · exact absurd hneg.1 (not_lt_of_ge (le_of_lt h1m))

theorem rotF_neg_abs_le (s c x : ℝ) (hs0 : 0 < s) (_hs1 : s < 1)
    (hF : rotNegDenominator s c x) :
    |rotF s c x (Real.sqrt (1 - x ^ 2))| ≤ (1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2 := by
  have h1s : 0 < 1 + s := by linarith
  have hF' : rotF s c x (Real.sqrt (1 - x ^ 2)) < 0 := hF
  have habs : |rotF s c x (Real.sqrt (1 - x ^ 2))| = -rotF s c x (Real.sqrt (1 - x ^ 2)) :=
    abs_of_neg hF'
  simp only [rotF] at habs ⊢
  have hsq : 0 ≤ (1 + s) * (x + c) ^ 2 := mul_nonneg (le_of_lt h1s) (sq_nonneg (x + c))
  rw [habs]
  linarith

theorem dominance_neg_p1 (s r c j x v : ℝ) (hd : rotDomain s c x v)
    (hF : rotNegDenominator s c x) (_hr0 : 0 ≤ r) (_hrs : r ^ 2 + s ^ 2 = 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    |(rotReducedScalars s r c j x).p1| ≥ 2 / Real.sqrt (1 - x ^ 2) := by
  have hy : 0 < Real.sqrt (1 - x ^ 2) := rotNegBranch_y_pos s c x hs0 hs1 hF
  have h1m : 0 < 1 - s := by linarith
  have hneF : rotF s c x (Real.sqrt (1 - x ^ 2)) ≠ 0 := hd.2.2.2.2
  have hDpos : 0 < |rotF s c x (Real.sqrt (1 - x ^ 2))| := abs_pos.mpr hneF
  have hbound : |rotF s c x (Real.sqrt (1 - x ^ 2))| ≤ (1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2 :=
    rotF_neg_abs_le s c x hs0 hs1 hF
  have hp1 : (rotReducedScalars s r c j x).p1
      = 2 * (1 - s) * Real.sqrt (1 - x ^ 2) / rotF s c x (Real.sqrt (1 - x ^ 2)) := by
    simp only [rotReducedScalars, rotScalars, rotP1]
  have habsp1 : |(rotReducedScalars s r c j x).p1|
      = (2 * (1 - s) * Real.sqrt (1 - x ^ 2)) / |rotF s c x (Real.sqrt (1 - x ^ 2))| := by
    rw [hp1]
    simp only [abs_div, abs_mul, abs_two, abs_of_nonneg (le_of_lt h1m),
      abs_of_nonneg (Real.sqrt_nonneg _)]
  have hkey : (2 / Real.sqrt (1 - x ^ 2))
      ≤ (2 * (1 - s) * Real.sqrt (1 - x ^ 2)) / |rotF s c x (Real.sqrt (1 - x ^ 2))| := by
    rw [div_le_div_iff₀ hy hDpos]
    calc 2 * |rotF s c x (Real.sqrt (1 - x ^ 2))|
        ≤ 2 * ((1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = (2 * (1 - s) * Real.sqrt (1 - x ^ 2)) * Real.sqrt (1 - x ^ 2) := by ring
  calc 2 / Real.sqrt (1 - x ^ 2)
      ≤ (2 * (1 - s) * Real.sqrt (1 - x ^ 2)) / |rotF s c x (Real.sqrt (1 - x ^ 2))| := hkey
    _ = |(rotReducedScalars s r c j x).p1| := habsp1.symm

theorem dominance_neg_w (s r c j x v : ℝ) (hd : rotDomain s c x v)
    (hF : rotNegDenominator s c x) (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    |(rotReducedScalars s r c j x).w| ≥ 2 * j / (rotRho s * Real.sqrt (1 - x ^ 2)) := by
  have hy : 0 < Real.sqrt (1 - x ^ 2) := rotNegBranch_y_pos s c x hs0 hs1 hF
  have hρpos : 0 < rotRho s := rotRho_pos s hs0 hs1
  have h1m : 0 < 1 - s := by linarith
  have hneF : rotF s c x (Real.sqrt (1 - x ^ 2)) ≠ 0 := hd.2.2.2.2
  have hDpos : 0 < |rotF s c x (Real.sqrt (1 - x ^ 2))| := abs_pos.mpr hneF
  have hbound : |rotF s c x (Real.sqrt (1 - x ^ 2))| ≤ (1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2 :=
    rotF_neg_abs_le s c x hs0 hs1 hF
  have hw : (rotReducedScalars s r c j x).w
      = 2 * r * j * Real.sqrt (1 - x ^ 2) / rotF s c x (Real.sqrt (1 - x ^ 2)) := by
    simp only [rotReducedScalars, rotScalars, rotW]
  have habsw : |(rotReducedScalars s r c j x).w|
      = (2 * r * |j| * Real.sqrt (1 - x ^ 2)) / |rotF s c x (Real.sqrt (1 - x ^ 2))| := by
    rw [hw]
    simp only [abs_div, abs_mul, abs_two, abs_of_nonneg hr0, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hρ : r / (1 - s) = 1 / rotRho s := rotR_div_one_minus s r hr0 hrs hs0 hs1
  have hrρ : r * rotRho s = 1 - s := by
    have hne1 : 1 - s ≠ 0 := ne_of_gt h1m
    have hne2 : rotRho s ≠ 0 := ne_of_gt hρpos
    rw [div_eq_mul_inv, div_eq_mul_inv] at hρ
    field_simp [hne1, hne2] at hρ
    linarith [hρ]
  have hrj : r * |j| * rotRho s = |j| * (1 - s) := by
    calc r * |j| * rotRho s = |j| * (r * rotRho s) := by ring
      _ = |j| * (1 - s) := by rw [hrρ]
  have hstep1 : (2 * r * |j| * Real.sqrt (1 - x ^ 2)) / ((1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2)
      ≤ (2 * r * |j| * Real.sqrt (1 - x ^ 2)) / |rotF s c x (Real.sqrt (1 - x ^ 2))| :=
    div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr0) (abs_nonneg j))
        (Real.sqrt_nonneg _)) hDpos hbound
  have hstep2 : (2 * r * |j| * Real.sqrt (1 - x ^ 2)) / ((1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2)
      = (2 * |j|) / (rotRho s * Real.sqrt (1 - x ^ 2)) := by
    have hne1 : 1 - s ≠ 0 := ne_of_gt h1m
    have hne2 : rotRho s ≠ 0 := ne_of_gt hρpos
    have hne4 : (1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2 ≠ 0 :=
      mul_ne_zero hne1 (ne_of_gt (sq_pos_of_pos hy))
    have hne5 : rotRho s * Real.sqrt (1 - x ^ 2) ≠ 0 := mul_ne_zero hne2 (ne_of_gt hy)
    rw [div_eq_div_iff hne4 hne5]
    calc 2 * r * |j| * Real.sqrt (1 - x ^ 2) * (rotRho s * Real.sqrt (1 - x ^ 2))
        = 2 * (Real.sqrt (1 - x ^ 2)) ^ 2 * (r * |j| * rotRho s) := by ring
      _ = 2 * (Real.sqrt (1 - x ^ 2)) ^ 2 * (|j| * (1 - s)) := by rw [hrj]
      _ = (2 * |j|) * ((1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2) := by ring
  have hfinal : (2 * j) / (rotRho s * Real.sqrt (1 - x ^ 2))
      ≤ (2 * |j|) / (rotRho s * Real.sqrt (1 - x ^ 2)) := by
    have hnum : 2 * j ≤ 2 * |j| := by linarith [le_abs_self j]
    exact div_le_div_of_nonneg_right hnum
      (mul_nonneg (le_of_lt hρpos) (Real.sqrt_nonneg _))
  calc (2 * j) / (rotRho s * Real.sqrt (1 - x ^ 2))
      ≤ (2 * |j|) / (rotRho s * Real.sqrt (1 - x ^ 2)) := hfinal
    _ = (2 * r * |j| * Real.sqrt (1 - x ^ 2)) / ((1 - s) * (Real.sqrt (1 - x ^ 2)) ^ 2) :=
      hstep2.symm
    _ ≤ (2 * r * |j| * Real.sqrt (1 - x ^ 2)) / |rotF s c x (Real.sqrt (1 - x ^ 2))| := hstep1
    _ = |(rotReducedScalars s r c j x).w| := habsw.symm

theorem rotDirect_ge_p1 (sc : RotScalars) (v : ℝ) (hv2 : 0 ≤ 1 - v ^ 2) :
    rotDirect sc v ≥ |sc.p1| := by
  have hsq : (Real.sqrt (1 - v ^ 2)) ^ 2 = 1 - v ^ 2 := Real.sq_sqrt hv2
  have hw : (sc.w * Real.sqrt (1 - v ^ 2)) ^ 2 = sc.w ^ 2 * (1 - v ^ 2) := by
    have h2 : (sc.w * Real.sqrt (1 - v ^ 2)) ^ 2
        = (sc.w ^ 2) * ((Real.sqrt (1 - v ^ 2)) ^ 2) := by ring
    rw [h2, hsq]
  have hB1 : Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
      ≥ |sc.p1 + sc.u * v| := by
    have h := sqrt_sq_add_le (sc.p1 + sc.u * v) (sc.w * Real.sqrt (1 - v ^ 2))
    rw [hw] at h
    exact h
  have hB2 : Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
      ≥ |sc.p1 - sc.u * v| := by
    have h := sqrt_sq_add_le (sc.p1 - sc.u * v) (sc.w * Real.sqrt (1 - v ^ 2))
    rw [hw] at h
    exact h
  have hmaxabs : max |sc.p1 + sc.u * v| |sc.p1 - sc.u * v| ≥ |sc.p1| := by
    have h := abs_add_sub_ge_two_max sc.p1 (sc.u * v)
    have h1 : max |sc.p1 + sc.u * v| |sc.p1 - sc.u * v|
        ≥ (|sc.p1 + sc.u * v| + |sc.p1 - sc.u * v|) / 2 := by
      have hle : |sc.p1 + sc.u * v| ≤ max |sc.p1 + sc.u * v| |sc.p1 - sc.u * v| := le_max_left _ _
      have hle2 : |sc.p1 - sc.u * v| ≤ max |sc.p1 + sc.u * v| |sc.p1 - sc.u * v| := le_max_right _ _
      linarith
    have h2 : (|sc.p1 + sc.u * v| + |sc.p1 - sc.u * v|) / 2 ≥ max |sc.p1| |sc.u * v| := by
      linarith [h]
    have h3 : max |sc.p1| |sc.u * v| ≥ |sc.p1| := le_max_left _ _
    linarith
  simp only [rotDirect]
  have hA1 : |sc.p0 + sc.t * v|
      + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
      ≥ |sc.p1 + sc.u * v| := by
    exact le_trans hB1 (by linarith [abs_nonneg (sc.p0 + sc.t * v)])
  have hA2 : |sc.p0 - sc.t * v|
      + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
      ≥ |sc.p1 - sc.u * v| := by
    exact le_trans hB2 (by linarith [abs_nonneg (sc.p0 - sc.t * v)])
  have hmax2 : max |sc.p1 + sc.u * v| |sc.p1 - sc.u * v|
      ≤ max (|sc.p0 + sc.t * v|
          + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)))
        (|sc.p0 - sc.t * v|
          + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))) := by
    exact max_le_max hA1 hA2
  linarith

theorem rotDirect_ge_radical (sc : RotScalars) (v : ℝ) :
    rotDirect sc v ≥ Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)) := by
  simp only [rotDirect]
  have hge : Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))
      ≤ |sc.p0 + sc.t * v|
        + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)) := by
    linarith [abs_nonneg (sc.p0 + sc.t * v)]
  exact le_trans hge
    (le_max_left
      (|sc.p0 + sc.t * v| + Real.sqrt ((sc.p1 + sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2)))
      (|sc.p0 - sc.t * v| + Real.sqrt ((sc.p1 - sc.u * v) ^ 2 + sc.w ^ 2 * (1 - v ^ 2))))

theorem rotCoupling_ge_w (sc : RotScalars) (v : ℝ) (hv2 : 0 ≤ 1 - v ^ 2) :
    rotCoupling sc v ≥ |sc.w| := by
  simp only [rotCoupling]
  have h2 : 0 ≤ sc.t ^ 2 * (1 - v ^ 2) := mul_nonneg (sq_nonneg _) hv2
  have hrad : |sc.w| ≤ Real.sqrt (sc.t ^ 2 * (1 - v ^ 2) + sc.w ^ 2) := by
    have h := Real.sqrt_le_sqrt
      (show sc.w ^ 2 ≤ sc.t ^ 2 * (1 - v ^ 2) + sc.w ^ 2 by linarith [h2])
    rw [Real.sqrt_sq_eq_abs] at h
    exact h
  linarith [Real.sqrt_nonneg (sc.t ^ 2 * (1 - v ^ 2) + sc.q ^ 2)]

theorem dominance_neg_direct (s r c j x v : ℝ) (hd : rotDomain s c x v)
    (_hF : rotNegDenominator s c x) :
    rotDirect (rotReducedScalars s r c j x) v ≥ |(rotReducedScalars s r c j x).p1| := by
  have hv := rotDomain_v s c x v hd
  exact rotDirect_ge_p1 (rotReducedScalars s r c j x) v (arcPhase_nonneg v hv.1 hv.2)

theorem dominance_neg_coupling (s r c j x v : ℝ) (hd : rotDomain s c x v)
    (_hF : rotNegDenominator s c x) :
    rotCoupling (rotReducedScalars s r c j x) v ≥ |(rotReducedScalars s r c j x).w| := by
  have hv := rotDomain_v s c x v hd
  exact rotCoupling_ge_w (rotReducedScalars s r c j x) v (arcPhase_nonneg v hv.1 hv.2)

theorem rotDirect_gt_two_negF (s r c j x v : ℝ) (hd : rotDomain s c x v)
    (hF : rotNegDenominator s c x) (hr0 : 0 ≤ r) (hrs : r ^ 2 + s ^ 2 = 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hj0 : 0 ≤ j) (hjc : j ^ 2 + c ^ 2 = 1) :
    rotDirect (rotReducedScalars s r c j x) v > 2 := by
  have hv := rotDomain_v s c x v hd
  have hv0 : 0 ≤ v := hv.1
  have hx0 : -1 ≤ x := hd.1
  have hx1 : x ≤ 1 := hd.2.1
  have hρpos : 0 < rotRho s := rotRho_pos s hs0 hs1
  have h1m : 0 < 1 - s := by linarith
  have hy : 0 < Real.sqrt (1 - x ^ 2) := rotNegBranch_y_pos s c x hs0 hs1 hF
  rcases eq_or_ne x 0 with hx | hx
  · rw [hx] at hd hF hy ⊢
    have hy1 : Real.sqrt (1 - 0 ^ 2) = 1 := by simp
    have hF0 : rotF s c 0 1 < 0 := by
      have h' : rotF s c 0 (Real.sqrt (1 - 0 ^ 2)) < 0 := hF
      rw [hy1] at h'
      exact h'
    rcases eq_or_ne c 0 with hc | hc
    · rw [hc] at hd hF0 hjc ⊢
      have hj1 : j = 1 := by
        have hj2 : j ^ 2 = (1 : ℝ) ^ 2 := by linarith [hjc]
        have habs : |j| = 1 := by
          have h1 : Real.sqrt (j ^ 2) = Real.sqrt ((1 : ℝ) ^ 2) := congrArg Real.sqrt hj2
          rw [Real.sqrt_sq_eq_abs] at h1
          norm_num at h1
          exact h1
        have hjn : j = |j| := (abs_of_nonneg hj0).symm
        rw [hjn, habs]
      have hFval : rotF s 0 0 1 = -(1 - s) := by simp only [rotF]; ring
      have hrρ : r * rotRho s = 1 - s := by
        have hρ : r / (1 - s) = 1 / rotRho s := rotR_div_one_minus s r hr0 hrs hs0 hs1
        have hne1 : 1 - s ≠ 0 := ne_of_gt h1m
        have hne2 : rotRho s ≠ 0 := ne_of_gt hρpos
        rw [div_eq_mul_inv, div_eq_mul_inv] at hρ
        field_simp [hne1, hne2] at hρ
        linarith [hρ]
      have hp1 : (rotReducedScalars s r 0 j 0).p1 = -2 := by
        simp only [rotReducedScalars, rotScalars, rotP1]
        rw [hy1, hFval]
        field_simp [ne_of_gt h1m]
      have hu : (rotReducedScalars s r 0 j 0).u = -2 / rotRho s := by
        simp only [rotReducedScalars, rotScalars, rotU, zero_mul, add_zero]
        rw [hy1, hFval]
        field_simp [ne_of_gt h1m, ne_of_gt hρpos]; nlinarith [hrρ]
      have hw : (rotReducedScalars s r 0 j 0).w = -2 * j / rotRho s := by
        simp only [rotReducedScalars, rotScalars, rotW]
        rw [hy1, hFval]
        have hrρj : r * j * rotRho s = j * (1 - s) := by
          calc r * j * rotRho s = j * (r * rotRho s) := by ring
            _ = j * (1 - s) := by rw [hrρ]
        field_simp [ne_of_gt h1m, ne_of_gt hρpos]; nlinarith [hrρj]
      have hw1 : (rotReducedScalars s r 0 j 0).w = -2 / rotRho s := by
        rw [hw, hj1]
        ring
      have hrad : rotDirect (rotReducedScalars s r 0 j 0) v
          ≥ Real.sqrt ((-2 + (-2 / rotRho s) * v) ^ 2 + (-2 / rotRho s) ^ 2 * (1 - v ^ 2)) := by
        have h := rotDirect_ge_radical (rotReducedScalars s r 0 j 0) v
        rw [hp1, hu, hw1] at h
        exact h
      have hRform : ((-2 + (-2 / rotRho s) * v) ^ 2 + (-2 / rotRho s) ^ 2 * (1 - v ^ 2))
          * rotRho s ^ 2 = 4 * rotRho s ^ 2 + 8 * rotRho s * v + 4 := by
        field_simp [ne_of_gt hρpos]
        ring
      have hρsq : 0 < rotRho s ^ 2 := sq_pos_of_pos hρpos
      have hpos8 : 0 < 8 * rotRho s * v + 4 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 8 by norm_num)
          (mul_nonneg (le_of_lt hρpos) hv0)]
      have hR : 4 < (-2 + (-2 / rotRho s) * v) ^ 2 + (-2 / rotRho s) ^ 2 * (1 - v ^ 2) := by
        have hmul : 4 * rotRho s ^ 2
            < ((-2 + (-2 / rotRho s) * v) ^ 2 + (-2 / rotRho s) ^ 2 * (1 - v ^ 2))
              * rotRho s ^ 2 := by
          rw [hRform]
          nlinarith [hpos8]
        have hdiv : 4 * rotRho s ^ 2 / rotRho s ^ 2
            < ((-2 + (-2 / rotRho s) * v) ^ 2 + (-2 / rotRho s) ^ 2 * (1 - v ^ 2)) :=
          (div_lt_iff₀ hρsq).mpr hmul
        simpa [ne_of_gt hρsq] using hdiv
      have hsqrt : 2 < Real.sqrt ((-2 + (-2 / rotRho s) * v) ^ 2
          + (-2 / rotRho s) ^ 2 * (1 - v ^ 2)) := by
        have hlt : Real.sqrt 4 < Real.sqrt ((-2 + (-2 / rotRho s) * v) ^ 2
            + (-2 / rotRho s) ^ 2 * (1 - v ^ 2)) :=
          Real.sqrt_lt_sqrt (by norm_num) hR
        have h4 : Real.sqrt 4 = 2 := by
          have hh := Real.sqrt_sq_eq_abs (2 : ℝ)
          norm_num at hh
          exact hh
        rw [h4] at hlt
        exact hlt
      linarith
    · have hFval : rotF s c 0 1 = (1 + s) * c ^ 2 - (1 - s) := by
        simp only [rotF]
        ring
      have hFneg : rotF s c 0 1 < 0 := by rw [hFval]; linarith [hF0]
      have habsF : |rotF s c 0 1| = (1 - s) - (1 + s) * c ^ 2 := by
        rw [abs_of_neg hFneg, hFval]
        ring
      have hcc : 0 < c ^ 2 := by
        have h := mul_self_pos.mpr hc
        nlinarith [h]
      have hlt : |rotF s c 0 1| < 1 - s := by
        rw [habsF]
        nlinarith
      have hp1form : (rotReducedScalars s r c j 0).p1
          = 2 * (1 - s) * 1 / rotF s c 0 1 := by
        simp only [rotReducedScalars, rotScalars, rotP1]
        rw [hy1]
      have habsp1 : |(rotReducedScalars s r c j 0).p1|
          = (2 * (1 - s)) / |rotF s c 0 1| := by
        rw [hp1form]
        rw [abs_div, abs_mul]
        rw [abs_of_nonneg (mul_nonneg (by norm_num) (le_of_lt h1m))]
        simp only [abs_one, mul_one]
      have hp1gt : 2 < |(rotReducedScalars s r c j 0).p1| := by
        rw [habsp1]
        have hdpos : 0 < |rotF s c 0 1| := abs_pos.mpr (ne_of_lt hFneg)
        rw [lt_div_iff₀ hdpos]
        linarith
      have hdirect := dominance_neg_direct s r c j 0 v hd hF
      linarith
  · have hxsqpos : 0 < x ^ 2 := by
      have h := mul_self_pos.mpr hx
      nlinarith [h]
    have h1mx2 : 0 ≤ 1 - x ^ 2 := by
      have h1px : 0 ≤ 1 - x := by linarith [hx1]
      have h1px1 : 0 ≤ 1 + x := by linarith [hx0]
      nlinarith [mul_nonneg h1px h1px1]
    have hy_lt : Real.sqrt (1 - x ^ 2) < 1 := by
      have h := Real.sqrt_lt_sqrt h1mx2 (show 1 - x ^ 2 < 1 by linarith [hxsqpos])
      simpa using h
    have h2y : 2 < 2 / Real.sqrt (1 - x ^ 2) := by
      rw [lt_div_iff₀ hy]
      nlinarith [hy_lt]
    have hp1 := dominance_neg_p1 s r c j x v hd hF hr0 hrs hs0 hs1
    have hdirect := dominance_neg_direct s r c j x v hd hF
    linarith

theorem rotM_le_two_iff (s c : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c)
    (_hc1 : c ≤ 1) :
    rotM s c ≤ 2 ↔ rotRho s ≤ (1 + c) / 2 := by
  have h1c : 0 < 1 + c := by linarith
  simp only [rotM]
  constructor
  · intro h
    have h4 : 4 * rotRho s ≤ 2 * (1 + c) := (div_le_iff₀ h1c).mp h
    linarith
  · intro h
    have h4 : 4 * rotRho s ≤ 2 * (1 + c) := by linarith
    exact (div_le_iff₀ h1c).mpr h4

theorem rotM_le_two_of_s (s c : ℝ) (hs : 3 / 5 ≤ s) (hs1 : s < 1) (hc0 : 0 ≤ c) :
    rotM s c ≤ 2 := by
  have hρ : rotRho s ≤ 1 / 2 := rotRho_le_half s hs hs1
  have h1c : 0 < 1 + c := by linarith
  have h4 : 4 * rotRho s ≤ 2 * (1 + c) := by nlinarith [hρ]
  simp only [rotM]
  exact (div_le_iff₀ h1c).mpr h4

theorem rotArcCoupling_strict_decreasing (s c j v v' : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 ≤ c) (_hc1 : c ≤ 1) (hj0 : 0 ≤ j)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hv'0 : 0 ≤ v') (hv'lt : v' < v) :
    rotArcCoupling s c j v' > rotArcCoupling s c j v := by
  have hm : 0 < rotM s c := rotM_pos s c hs0 hs1 hc0
  have h1c : 0 < 1 + c := by linarith
  have hh : 0 ≤ rotH c j := by
    simp only [rotH]
    exact div_nonneg (mul_nonneg (by norm_num) hj0) (le_of_lt h1c)
  have hvpos : 0 < v := lt_of_le_of_lt hv'0 hv'lt
  have hv'1 : v' ≤ 1 := le_trans (le_of_lt hv'lt) hv1
  have hsq : v' ^ 2 < v ^ 2 := by
    have h1 : v' * v' ≤ v' * v := mul_le_mul_of_nonneg_left (le_of_lt hv'lt) hv'0
    have h2 : v' * v < v * v := mul_lt_mul_of_pos_right hv'lt hvpos
    nlinarith [h1, h2]
  have hsq1 : v' ^ 2 ≤ 1 := by
    have h := mul_le_mul hv'1 hv'1 hv'0 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [h]
  have h1v' : 0 ≤ 1 - v' ^ 2 := by nlinarith [hsq1]
  have h1v : 0 ≤ 1 - v ^ 2 := arcPhase_nonneg v hv0 hv1
  have hs1' : 1 - v ^ 2 < 1 - v' ^ 2 := by nlinarith [hsq]
  have hm2 : 0 < rotM s c ^ 2 := sq_pos_of_pos hm
  have hmul : rotM s c ^ 2 * (1 - v ^ 2) < rotM s c ^ 2 * (1 - v' ^ 2) :=
    mul_lt_mul_of_pos_left hs1' hm2
  have hradlt : rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2
      < rotM s c ^ 2 * (1 - v' ^ 2) + 4 * rotH c j ^ 2 := by linarith [hmul]
  have hradA : 0 ≤ rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2 := by
    have h1 : 0 ≤ rotM s c ^ 2 * (1 - v ^ 2) := mul_nonneg (le_of_lt hm2) h1v
    have h2 : 0 ≤ 4 * rotH c j ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    linarith
  have hradA' : 0 ≤ rotM s c ^ 2 * (1 - v' ^ 2) + 4 * rotH c j ^ 2 := by
    have h1 : 0 ≤ rotM s c ^ 2 * (1 - v' ^ 2) := mul_nonneg (le_of_lt hm2) h1v'
    have h2 : 0 ≤ 4 * rotH c j ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    linarith
  have hsqrts : Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
      < Real.sqrt (rotM s c ^ 2 * (1 - v' ^ 2) + 4 * rotH c j ^ 2) :=
    Real.sqrt_lt_sqrt hradA hradlt
  have hsqrts2 : Real.sqrt (1 - v ^ 2) < Real.sqrt (1 - v' ^ 2) :=
    Real.sqrt_lt_sqrt h1v hs1'
  have hmul2 : rotM s c * Real.sqrt (1 - v ^ 2) < rotM s c * Real.sqrt (1 - v' ^ 2) :=
    mul_lt_mul_of_pos_left hsqrts2 hm
  have hsum : Real.sqrt (rotM s c ^ 2 * (1 - v ^ 2) + 4 * rotH c j ^ 2)
      + rotM s c * Real.sqrt (1 - v ^ 2)
      < Real.sqrt (rotM s c ^ 2 * (1 - v' ^ 2) + 4 * rotH c j ^ 2)
        + rotM s c * Real.sqrt (1 - v' ^ 2) := by linarith [hsqrts, hmul2]
  simp only [rotArcCoupling]
  exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr hsum

theorem centeredArc_pareto_optimal (cfg : Config) (s r c j : ℝ)
    (hp : RotPhysical s r c j)
    (hm : rotM s c ≤ 2)
    (heta : cfg.upper.eta = cfg.vac.eta0)
    (b : ℝ × ℝ) (hb : b ∈ physicalResourceImage cfg s r c j)
    (v : ℝ) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    ¬ ResourcePair.Dominates ⟨b.1, b.2⟩
      ⟨rotDirect (rotReducedScalars s r c j 1) v,
        rotCoupling (rotReducedScalars s r c j 1) v⟩ := by
  rcases hp with ⟨hs0, hs1, hr0, hrs, hc0, hc1, hj0, hjc⟩
  have hsq0 : Real.sqrt (1 - 1 ^ 2) = 0 := by
    have h : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [h, sub_self, Real.sqrt_zero]
  have harcdom : rotDomain s c 1 v := by
    refine ⟨by norm_num, by norm_num, hv, hv1, ?_⟩
    have hF : rotF s c 1 (Real.sqrt (1 - 1 ^ 2)) = (1 + s) * (1 + c) ^ 2 := by
      rw [rotF, hsq0]
      ring
    rw [hF]
    exact mul_ne_zero (ne_of_gt (by linarith : (0 : ℝ) < 1 + s))
      (ne_of_gt (sq_pos_of_pos (by linarith : (0 : ℝ) < 1 + c)))
  have himg := (exact_physical_resource_image cfg s r c j hrs hjc heta b).mp hb
  rcases himg with ⟨x', v', hd', hb_eq⟩
  subst b
  have hv'0 : 0 ≤ v' := hd'.2.2.1
  have hv'1 : v' ≤ 1 := hd'.2.2.2.1
  have hFne : rotF s c x' (Real.sqrt (1 - x' ^ 2)) ≠ 0 := hd'.2.2.2.2
  have harcd : rotDirect (rotReducedScalars s r c j 1) v = rotM s c * v :=
    centeredArc_direct s r c j v hr0 hrs hs0 hs1 hc0 hv hv1
  have harcc : rotCoupling (rotReducedScalars s r c j 1) v = rotArcCoupling s c j v :=
    centeredArc_coupling s r c j v hr0 hrs hs0 hs1 hc0 hv hv1
  intro hdom
  rcases hdom with ⟨hDle, hCle, hstrict⟩
  rcases lt_or_gt_of_ne hFne with hFlt | hFgt
  · have hFneg : rotNegDenominator s c x' := by
      show rotF s c x' (Real.sqrt (1 - x' ^ 2)) < 0
      exact hFlt
    have hDgt : rotDirect (rotReducedScalars s r c j x') v' > 2 :=
      rotDirect_gt_two_negF s r c j x' v' hd' hFneg hr0 hrs hs0 hs1 hj0 hjc
    have hmv : rotM s c * v ≤ rotM s c := by
      have h := mul_le_mul_of_nonneg_left hv1 (le_of_lt (rotM_pos s c hs0 hs1 hc0))
      simpa using h
    have hmv2 : rotM s c * v ≤ 2 := le_trans hmv hm
    rw [harcd] at hDle
    linarith
  · have hFpos : rotPosDenominator s c x' := by
      show 0 < rotF s c x' (Real.sqrt (1 - x' ^ 2))
      exact hFgt
    have hDpos : rotDirect (rotReducedScalars s r c j x') v'
        ≥ 2 * |(rotReducedScalars s r c j x').t| * v' :=
      dominance_pos_direct s r c j x' v' hd' hFpos hr0 hc0 hc1
    have hT : 2 * |(rotReducedScalars s r c j x').t| ≥ rotM s c :=
      dominance_pos_t s r c j x' v' hd' hFpos hr0 hrs hs0 hs1 hc0
    have hDm : rotM s c * v' ≤ 2 * |(rotReducedScalars s r c j x').t| * v' :=
      mul_le_mul_of_nonneg_right hT hv'0
    have hDge : rotDirect (rotReducedScalars s r c j x') v' ≥ rotM s c * v' :=
      le_trans hDm hDpos
    have hCge : rotCoupling (rotReducedScalars s r c j x') v'
        ≥ rotArcCoupling s c j v' :=
      dominance_pos_coupling s r c j x' v' hd' hFpos hr0 hrs hs0 hs1 hc0
    rw [harcd] at hDle
    rw [harcc] at hCle
    rcases lt_trichotomy v' v with hlt | heq | hgt
    · have hdec : rotArcCoupling s c j v' > rotArcCoupling s c j v :=
        rotArcCoupling_strict_decreasing s c j v v' hs0 hs1 hc0 hc1 hj0 hv hv1
          hv'0 hlt
      linarith
    · subst heq
      rcases hstrict with hlt1 | hlt2
      · linarith
      · linarith
    · have hmpos : 0 < rotM s c := rotM_pos s c hs0 hs1 hc0
      have hmv : rotM s c * v < rotM s c * v' := mul_lt_mul_of_pos_left hgt hmpos
      linarith

end GSTC.Scattering.RotatedRankOneRecovery
