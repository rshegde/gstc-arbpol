import GSTC.Scattering.RotatedRankOneRightAngle

open GSTC.Scattering
open RotatedRankOneResources RotatedRankOneRecovery
open scoped Matrix

namespace GSTC.Scattering.RotatedRankOneScalarMinRegression

example : rotSharpMin (rotM (1 / 10) 0) (rotH 0 1) =
    Real.sqrt ((58 + 2 * Real.sqrt 599) / 11) := by
  have hfrac : ((1 : ℝ) - 1 / 10) / ((1 : ℝ) + 1 / 10) = 9 / 11 := by
    field_simp
    norm_num
  have hρ : rotRho (1 / 10) = Real.sqrt (9 / 11) := by
    rw [rotRho, hfrac]
  have hρsq : rotRho (1 / 10) ^ 2 = 9 / 11 := by
    rw [hρ, Real.sq_sqrt (by norm_num)]
  have hh : rotH 0 1 = 2 := by
    rw [rotH]
    norm_num
  have hm : rotM (1 / 10) 0 = 4 * rotRho (1 / 10) := by
    rw [rotM]
    norm_num
  have hhalf : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  have hmh : rotM (1 / 10) 0 > rotH 0 1 := by
    rw [hm, hh]
    have hlt : Real.sqrt (1 / 4) < rotRho (1 / 10) := by
      rw [hρ]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [hhalf] at hlt
    linarith
  have hm2 : rotM (1 / 10) 0 ^ 2 = (144 / 11 : ℝ) := by
    rw [hm, mul_pow]
    nlinarith [hρsq]
  have hρ4 : rotRho (1 / 10) ^ 4 = (81 / 121 : ℝ) := by
    nlinarith [hρsq]
  have hm4 : rotM (1 / 10) 0 ^ 4 = (20736 / 121 : ℝ) := by
    rw [hm, mul_pow]
    nlinarith [hρ4]
  have hR : rotM (1 / 10) 0 ^ 4 + 4 * rotM (1 / 10) 0 ^ 2 * rotH 0 1 ^ 2
      - 4 * rotH 0 1 ^ 4 = (38336 / 121 : ℝ) := by
    rw [hh, hm2, hm4]
    norm_num
  have hroot : Real.sqrt (rotM (1 / 10) 0 ^ 4 + 4 * rotM (1 / 10) 0 ^ 2 * rotH 0 1 ^ 2
      - 4 * rotH 0 1 ^ 4) = 8 * Real.sqrt 599 / 11 := by
    rw [hR, Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hX : rotM (1 / 10) 0 ^ 2 + 2 * rotH 0 1 ^ 2
      + Real.sqrt (rotM (1 / 10) 0 ^ 4 + 4 * rotM (1 / 10) 0 ^ 2 * rotH 0 1 ^ 2
        - 4 * rotH 0 1 ^ 4) = 4 * ((58 + 2 * Real.sqrt 599) / 11) := by
    rw [hroot, hm2, hh]
    ring
  have hnotle : ¬ (rotM (1 / 10) 0 ≤ rotH 0 1) := not_le.mpr hmh
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  rw [rotSharpMin]
  split
  · rename_i hc
    exact absurd hc hnotle
  · rw [hX, Real.sqrt_mul (x := 4) (by norm_num) ((58 + 2 * Real.sqrt 599) / 11),
      hsqrt4]
    ring

example : ∀ (m h : ℝ), m > h → 0 ≤ h →
    0 < m ^ 4 + 4 * m ^ 2 * h ^ 2 - 4 * h ^ 4 :=
  rotSharpMin_radical_nonneg

example : ∀ (m h : ℝ), m ≤ h → rotSharpMin m h = h :=
  rotSharpMin_eq_h

example : ∀ (m h : ℝ), m > h → 0 ≤ h →
    2 * rotSharpMin m h ^ 4 - (m ^ 2 + 2 * h ^ 2) * rotSharpMin m h ^ 2 + h ^ 4 = 0 :=
  rotSharpMin_quadratic

example : ∀ (m h : ℝ), m > h → 0 ≤ h →
    h < rotSharpMin m h ∧ rotSharpMin m h ≤ m :=
  rotSharpMin_bounds

example : rotSharpMin 2 2 = 2 := by
  simp [rotSharpMin]

example : rotSharpMinArg 2 2 = 1 := by
  simp [rotSharpMinArg]

example : ∀ (s c j : ℝ), 0 < s → s < 1 → 0 ≤ c → c ≤ 1 → 0 ≤ j →
    rotM s c > rotH c j →
    rotArcCoupling s c j (rotSharpMin (rotM s c) (rotH c j) / rotM s c)
        = rotSharpMin (rotM s c) (rotH c j)
      ∧ rotArcDirect s c (rotSharpMin (rotM s c) (rotH c j) / rotM s c)
        = rotSharpMin (rotM s c) (rotH c j) :=
  rotSharpMin_crossing

example : ∀ (m h : ℝ), 0 ≤ m → 0 ≤ h →
    0 ≤ rotSharpMinArg m h ∧ rotSharpMinArg m h ≤ 1 :=
  rotSharpMin_arg_mem

example : ∀ (s c j v : ℝ), 0 < s → s < 1 → 0 ≤ c → c ≤ 1 → 0 ≤ j → 0 ≤ v → v ≤ 1 →
    max (rotArcDirect s c v) (rotArcCoupling s c j v) ≥ rotSharpMin (rotM s c) (rotH c j) :=
  rotSharpMin_le_arc

example : ∀ (s c j : ℝ), 0 < s → s < 1 → 0 ≤ c → c ≤ 1 → 0 ≤ j →
    max (rotArcDirect s c (rotSharpMinArg (rotM s c) (rotH c j)))
      (rotArcCoupling s c j (rotSharpMinArg (rotM s c) (rotH c j)))
      = rotSharpMin (rotM s c) (rotH c j) :=
  rotSharpMin_attained

example : ∀ (s c j v : ℝ), 0 < s → s < 1 → 0 ≤ c → c ≤ 1 → 0 ≤ j → 0 ≤ v → v ≤ 1 →
    v ≠ rotSharpMinArg (rotM s c) (rotH c j) →
    max (rotArcDirect s c v) (rotArcCoupling s c j v) > rotSharpMin (rotM s c) (rotH c j) :=
  rotSharpMin_unique

private theorem h_m_le_h : rotM (3 / 4) 0 ≤ rotH 0 1 := by
  have hρ : rotRho (3 / 4) = Real.sqrt (1 / 7) := by
    rw [rotRho]
    have hfrac : ((1 : ℝ) - 3 / 4) / ((1 : ℝ) + 3 / 4) = 1 / 7 := by
      field_simp
      norm_num
    rw [hfrac]
  have hh : rotH 0 1 = 2 := by
    rw [rotH]
    norm_num
  have h1 : Real.sqrt (1 / 7 : ℝ) ≤ 1 / 2 := by
    have hsq : Real.sqrt (1 / 7 : ℝ) ≤ Real.sqrt (1 / 4 : ℝ) :=
      Real.sqrt_le_sqrt (by norm_num)
    have hhalf : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
      norm_num
    rw [hhalf] at hsq
    exact hsq
  rw [rotM, hh, hρ]
  simp only [add_zero, div_one]
  nlinarith [h1]

example : rotSharpMin (rotM (3 / 4) 0) (rotH 0 1) = rotH 0 1 := by
  exact rotSharpMin_eq_h (rotM (3 / 4) 0) (rotH 0 1) h_m_le_h

example : rotSharpMinArg (rotM (3 / 4) 0) (rotH 0 1) = 1 := by
  simp [rotSharpMinArg, h_m_le_h]

example : ∀ (v : ℝ), 0 ≤ v → v ≤ 1 →
    max (rotArcDirect (3 / 4) 0 v) (rotArcCoupling (3 / 4) 0 1 v) ≥ rotSharpMin (rotM (3 / 4) 0) (rotH 0 1) :=
  fun v hv0 hv1 => rotSharpMin_le_arc (3 / 4) 0 1 v (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hv0 hv1

example : rotSharpMin (rotM (1 / 10) 1) (rotH 1 0) = Real.sqrt 2 * rotRho (1 / 10) := by
  exact rotSharpMin_aligned (1 / 10) (by norm_num) (by norm_num)

example : ∀ (s c j : ℝ), 0 < s → s < 1 → 0 ≤ c → c ≤ 1 → 0 ≤ j → j ^ 2 + c ^ 2 = 1 →
    rotM s c ≤ 2 → rotSharpMin (rotM s c) (rotH c j) ≤ 2 :=
  rotSharpMin_le_two_of_m_le_two

example : ∀ (s r c j x v : ℝ), 0 < s → s < 1 → 0 ≤ r → r ^ 2 + s ^ 2 = 1 →
    0 ≤ c → c ≤ 1 → 0 ≤ j → j ^ 2 + c ^ 2 = 1 → rotDomain s c x v →
    rotSharpMin (rotM s c) (rotH c j) ≤ 2 →
    max (rotDirect (rotReducedScalars s r c j x) v)
      (rotCoupling (rotReducedScalars s r c j x) v) ≥ rotSharpMin (rotM s c) (rotH c j) :=
  rotSharpMin_global_lower

example : ∀ (cfg : Config) (s r c j : ℝ), 0 < s → s < 1 → 0 ≤ r →
    r ^ 2 + s ^ 2 = 1 → 0 ≤ c → c ≤ 1 → 0 ≤ j → j ^ 2 + c ^ 2 = 1 →
    cfg.upper.eta = cfg.vac.eta0 → rotSharpMin (rotM s c) (rotH c j) ≤ 2 →
    ∀ b ∈ physicalResourceImage cfg s r c j,
      max b.1 b.2 ≥ rotSharpMin (rotM s c) (rotH c j) :=
  rotSharpMin_image_lower

example : ∀ (cfg : Config) (s r c j : ℝ), 0 < s → s < 1 → 0 ≤ r →
    r ^ 2 + s ^ 2 = 1 → 0 ≤ c → c ≤ 1 → 0 ≤ j → j ^ 2 + c ^ 2 = 1 →
    cfg.upper.eta = cfg.vac.eta0 →
    ∃ b ∈ physicalResourceImage cfg s r c j,
      max b.1 b.2 = rotSharpMin (rotM s c) (rotH c j) :=
  rotSharpMin_image_attained

example : ∀ (s r c j x v : ℝ) (_hs0 : 0 < s) (_hs1 : s < 1) (_hr0 : 0 ≤ r)
    (_hrs : r ^ 2 + s ^ 2 = 1) (_hc0 : 0 ≤ c) (_hc1 : c ≤ 1) (_hj0 : 0 ≤ j)
    (_hjc : j ^ 2 + c ^ 2 = 1) (_hd : rotDomain s c x v),
    rotDirect (rotReducedScalars s r c j x) v ^ 2
      ≥ (rotReducedScalars s r c j x).p1 ^ 2 + (rotReducedScalars s r c j x).w ^ 2 :=
  rotDirect_sq_ge_p1_w

example : ∀ (s r c j x v : ℝ) (_hs0 : 0 < s) (_hs1 : s < 1) (_hr0 : 0 ≤ r)
    (_hrs : r ^ 2 + s ^ 2 = 1) (_hc0 : 0 ≤ c) (_hc1 : c ≤ 1) (_hj0 : 0 ≤ j)
    (_hjc : j ^ 2 + c ^ 2 = 1) (_hd : rotDomain s c x v),
    rotDirect (rotReducedScalars s r c j x) v ^ 2
      + rotCoupling (rotReducedScalars s r c j x) v ^ 2 ≥ (2 * rotRho s) ^ 2 :=
  rotDirect_sq_add_coupling_sq

example : ∀ (s r c j x : ℝ) (_hc0 : 0 ≤ c) (_hc1 : c ≤ 1) (_hj0 : 0 ≤ j)
    (_hjc : j ^ 2 + c ^ 2 = 1) (_hx0 : -1 ≤ x) (_hx1 : x ≤ 1),
    |(rotReducedScalars s r c j x).u| ≥ |(rotReducedScalars s r c j x).w| :=
  rotU_abs_ge_w

private theorem hr0_witness : 0 ≤ Real.sqrt 99 / 10 := by
  positivity

private theorem hrs_witness : (Real.sqrt 99 / 10) ^ 2 + (1 / 10) ^ 2 = 1 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

example : rotDirect (rotReducedScalars (1 / 10) (Real.sqrt 99 / 10) 0 1 0) 0 =
    2 * Real.sqrt (1 + 1 / rotRho (1 / 10) ^ 2) := by
  exact (rotRightAngle_pair (1 / 10) (Real.sqrt 99 / 10) (by norm_num) (by norm_num)
    hr0_witness hrs_witness).1

example : rotDirect (rotReducedScalars (1 / 10) (Real.sqrt 99 / 10) 0 1 0) 0 =
    2 * Real.sqrt (1 + 1 / rotRho (1 / 10) ^ 2) ∧
    rotCoupling (rotReducedScalars (1 / 10) (Real.sqrt 99 / 10) 0 1 0) 0 =
      2 / rotRho (1 / 10) := by
  exact rotRightAngle_pair (1 / 10) (Real.sqrt 99 / 10) (by norm_num) (by norm_num)
    hr0_witness hrs_witness

example : ∀ (cfg : Config) (s r : ℝ), 0 < s → s < 1 → 0 ≤ r →
    r ^ 2 + s ^ 2 = 1 → cfg.upper.eta = cfg.vac.eta0 →
    ∀ b ∈ physicalResourceImage cfg s r 0 1,
      max b.1 b.2 ≥ min (rotSharpMin (rotM s 0) (rotH 0 1))
        (2 * Real.sqrt (1 + 1 / rotRho s ^ 2)) :=
  rotRightAngle_image_lower

example : ∀ (cfg : Config) (s r : ℝ), 0 < s → s < 1 → 0 ≤ r →
    r ^ 2 + s ^ 2 = 1 → cfg.upper.eta = cfg.vac.eta0 →
    ∃ b ∈ physicalResourceImage cfg s r 0 1,
      max b.1 b.2 = 2 * Real.sqrt (1 + 1 / rotRho s ^ 2) :=
  rotRightAngle_image_attained

example : Real.sqrt ((58 + 2 * Real.sqrt 599) / 11) > 4 * Real.sqrt 5 / 3 := by
  have hC : 0 ≤ 4 * Real.sqrt 5 / 3 := by positivity
  have h599 : 179 / 9 < Real.sqrt 599 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hlt : 4 * Real.sqrt 5 / 3 < Real.sqrt ((58 + 2 * Real.sqrt 599) / 11) := by
    rw [Real.lt_sqrt hC]
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    linarith [h599]
  exact hlt

#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMinArg
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_radical_nonneg
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_eq_h
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_quadratic
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_bounds
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_crossing
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_arg_mem
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_le_arc
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_attained
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_unique
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_le_two_of_m_le_two
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_global_lower
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_image_lower
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_aligned
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotU_abs_ge_w
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotDirect_sq_ge_p1_w
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotDirect_sq_add_coupling_sq
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotRightAngle_pair
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotRightAngle_negF_dominated
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotRightAngle_min
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotRightAngle_min_attained
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotSharpMin_image_attained
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotRightAngle_image_lower
#print axioms GSTC.Scattering.RotatedRankOneRecovery.rotRightAngle_image_attained

end GSTC.Scattering.RotatedRankOneScalarMinRegression
