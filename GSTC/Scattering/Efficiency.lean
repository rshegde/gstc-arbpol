/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Jones
public import GSTC.Scattering.Power

public section

namespace GSTC.Scattering

open scoped Matrix

theorem jonesNormSqR_eq (u : Vec2) :
    jonesNormSqR u = Complex.normSq (u 0) + Complex.normSq (u 1) := by
  unfold jonesNormSqR jonesNormSq jonesInner
  rw [Complex.add_re, star_mul_re, star_mul_re]

theorem jonesNormSqR_nonneg (u : Vec2) : 0 ≤ jonesNormSqR u := by
  rw [jonesNormSqR_eq]
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem jonesNormSqR_eq_zero_iff (u : Vec2) : jonesNormSqR u = 0 ↔ u = 0 := by
  constructor
  · intro h
    rw [jonesNormSqR_eq] at h
    have h0 : Complex.normSq (u 0) = 0 := by
      linarith [Complex.normSq_nonneg (u 0), Complex.normSq_nonneg (u 1)]
    have h1 : Complex.normSq (u 1) = 0 := by
      linarith [Complex.normSq_nonneg (u 0), Complex.normSq_nonneg (u 1)]
    have h0' : u 0 = 0 := Complex.normSq_eq_zero.mp h0
    have h1' : u 1 = 0 := Complex.normSq_eq_zero.mp h1
    funext i
    fin_cases i
    · exact h0'
    · exact h1'
  · intro h
    rw [h]
    simp [jonesNormSqR_eq]

theorem jonesNormSqR_smul (α : ℂ) (v : Vec2) :
    jonesNormSqR (α • v) = Complex.normSq α * jonesNormSqR v := by
  rw [jonesNormSqR_eq (α • v), jonesNormSqR_eq v]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  ring

theorem wavePower_normal_jones (m : Medium) (e : Vec2) :
    wavePower m 0 e = jonesNormSqR e / (2 * m.eta) := by
  rw [wavePower_normal, jonesNormSqR_eq]

@[expose] def identicalMedia (cfg : Config) (s : Side) : Prop :=
  (Wave.medium cfg s .incident).eta = (Wave.medium cfg s .transmitted).eta

theorem power_balance_jones (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) (hloss : sus.Lossless)
    (hgstc : gstcSatisfied cfg s sus eI eR eT) :
    jonesNormSqR eI / (2 * (Wave.medium cfg s .incident).eta)
      = jonesNormSqR eR / (2 * (Wave.medium cfg s .reflected).eta)
        + jonesNormSqR eT / (2 * (Wave.medium cfg s .transmitted).eta) := by
  calc
    jonesNormSqR eI / (2 * (Wave.medium cfg s .incident).eta)
        = wavePower (Wave.medium cfg s .incident) 0 eI :=
      (wavePower_normal_jones _ _).symm
    _ = wavePower (Wave.medium cfg s .reflected) 0 eR
        + wavePower (Wave.medium cfg s .transmitted) 0 eT :=
      power_balance_normal cfg s sus eI eR eT hk hloss hgstc
    _ = jonesNormSqR eR / (2 * (Wave.medium cfg s .reflected).eta)
        + jonesNormSqR eT / (2 * (Wave.medium cfg s .transmitted).eta) := by
      rw [wavePower_normal_jones (Wave.medium cfg s .reflected) eR,
        wavePower_normal_jones (Wave.medium cfg s .transmitted) eT]

theorem power_balance_jones_cleared (cfg : Config) (s : Side)
    (sus : Susceptibilities) (eI eR eT : Vec2) (hk : cfg.kPar = 0)
    (hloss : sus.Lossless) (hgstc : gstcSatisfied cfg s sus eI eR eT) :
    jonesNormSqR eI * (Wave.medium cfg s .transmitted).eta
      = jonesNormSqR eR * (Wave.medium cfg s .transmitted).eta
        + jonesNormSqR eT * (Wave.medium cfg s .incident).eta := by
  have hbal := power_balance_jones cfg s sus eI eR eT hk hloss hgstc
  rw [medium_reflected_eq] at hbal
  have hηI : (2 * (Wave.medium cfg s .incident).eta : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt (Wave.medium cfg s .incident).eta_pos)
  have hηT : (2 * (Wave.medium cfg s .transmitted).eta : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt (Wave.medium cfg s .transmitted).eta_pos)
  have h1 := congrArg (fun x : ℝ => x * (2 * (Wave.medium cfg s .incident).eta)) hbal
  rw [div_mul_cancel₀ _ hηI] at h1
  rw [add_mul] at h1
  rw [div_mul_cancel₀ _ hηI] at h1
  have h3 : (jonesNormSqR eT / (2 * (Wave.medium cfg s .transmitted).eta))
      * (2 * (Wave.medium cfg s .incident).eta)
      * (Wave.medium cfg s .transmitted).eta
      = jonesNormSqR eT * (Wave.medium cfg s .incident).eta := by
    have key : jonesNormSqR eT
          * ((2 * (Wave.medium cfg s .incident).eta)
            * (Wave.medium cfg s .transmitted).eta)
        = (jonesNormSqR eT * (Wave.medium cfg s .incident).eta)
          * (2 * (Wave.medium cfg s .transmitted).eta) := by ring
    rw [mul_assoc, div_mul_eq_mul_div]
    exact (div_eq_iff hηT).mpr key
  have h2 := congrArg (fun x : ℝ => x * (Wave.medium cfg s .transmitted).eta) h1
  rw [add_mul] at h2
  rw [h3] at h2
  exact h2

theorem power_balance_jones_identical (cfg : Config) (s : Side)
    (sus : Susceptibilities) (eI eR eT : Vec2) (hk : cfg.kPar = 0)
    (hloss : sus.Lossless) (hgstc : gstcSatisfied cfg s sus eI eR eT)
    (hmed : identicalMedia cfg s) :
    jonesNormSqR eI = jonesNormSqR eR + jonesNormSqR eT := by
  have hcleared := power_balance_jones_cleared cfg s sus eI eR eT hk hloss hgstc
  have hmed' : (Wave.medium cfg s .incident).eta = (Wave.medium cfg s .transmitted).eta := hmed
  rw [← hmed'] at hcleared
  have hηI : (Wave.medium cfg s .incident).eta ≠ 0 :=
    ne_of_gt (Wave.medium cfg s .incident).eta_pos
  calc jonesNormSqR eI
      = (jonesNormSqR eR * (Wave.medium cfg s .incident).eta
          + jonesNormSqR eT * (Wave.medium cfg s .incident).eta)
        / (Wave.medium cfg s .incident).eta :=
        (eq_div_iff hηI).mpr hcleared
    _ = jonesNormSqR eR + jonesNormSqR eT := by
      field_simp [hηI]

theorem isNormalized_jonesNormSqR (u : Vec2) (h : isNormalized u) :
    jonesNormSqR u = 1 := by
  have h1 : jonesNormSq u = 1 := h
  unfold jonesNormSqR
  rw [h1, Complex.one_re]

end GSTC.Scattering
