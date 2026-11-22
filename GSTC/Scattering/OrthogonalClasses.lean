/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIPhysicalFeasibility
public import GSTC.Scattering.ElectricOnly

public section

namespace GSTC.Scattering
namespace OrthogonalClasses

open scoped Matrix
open BIFeasibility
open BIPhysicalFeasibility
open GSTC.Scattering.Operator

theorem readR_pack (u : Vec2) : readR (pack u 0) = u := by
  ext i
  fin_cases i <;> simp [readR, pack]

@[expose] noncomputable def biForwardR (cfg : Config) (p : BIParams) : Ten2 :=
  !![(biPowerResponse4 cfg p) 0 0, (biPowerResponse4 cfg p) 0 1;
     (biPowerResponse4 cfg p) 1 0, (biPowerResponse4 cfg p) 1 1]

theorem readR_biPowerResponse4_pack (cfg : Config) (p : BIParams) (u : Vec2) :
    readR (biPowerResponse4 cfg p *ᵥ pack u 0) = biForwardR cfg p *ᵥ u := by
  ext i
  fin_cases i <;>
    simp [readR, biForwardR, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four,
      Fin.sum_univ_two, pack]

theorem readT_biPowerResponse4_pack (cfg : Config) (p : BIParams) (u : Vec2) :
    readT (biPowerResponse4 cfg p *ᵥ pack u 0) = biForwardT cfg p *ᵥ u := by
  ext i
  fin_cases i <;>
    simp [readT, biForwardT, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four,
      Fin.sum_univ_two, pack]

theorem portScale4_mulVec' (cfg : Config) (heq : cfg.lower.eta = cfg.upper.eta)
    (x : Fin 4 → ℂ) :
    portScale4 cfg *ᵥ x = (Real.sqrt cfg.upper.eta : ℂ) • x := by
  have hs := portScale4_eq_scalar cfg heq
  rw [hs]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec_apply_eq_sum, Matrix.smul_apply, Matrix.one_apply]

theorem readR_portScale4 (cfg : Config) (heq : cfg.lower.eta = cfg.upper.eta)
    (x : Fin 4 → ℂ) :
    readR (portScale4 cfg *ᵥ x) = (Real.sqrt cfg.upper.eta : ℂ) • readR x := by
  rw [portScale4_mulVec' cfg heq x]
  ext i
  fin_cases i <;> simp [readR, Pi.smul_apply, smul_eq_mul]

theorem readT_portScale4 (cfg : Config) (heq : cfg.lower.eta = cfg.upper.eta)
    (x : Fin 4 → ℂ) :
    readT (portScale4 cfg *ᵥ x) = (Real.sqrt cfg.upper.eta : ℂ) • readT x := by
  rw [portScale4_mulVec' cfg heq x]
  ext i
  fin_cases i <;> simp [readT, Pi.smul_apply, smul_eq_mul]

theorem readT_portScale4_pack_zero (cfg : Config) (heq : cfg.lower.eta = cfg.upper.eta)
    (u : Vec2) : readT (portScale4 cfg *ᵥ pack u 0) = 0 := by
  rw [portScale4_mulVec' cfg heq]
  ext i
  fin_cases i <;> simp [readT, pack, Pi.smul_apply, smul_eq_mul]

theorem gstc_above_of_forward (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) (u : Vec2) :
    gstcSatisfied cfg .above (encode p)
      ((Real.sqrt cfg.upper.eta : ℂ) • u)
      ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardR cfg p *ᵥ u))
      ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardT cfg p *ᵥ u)) := by
  have hgstc : gstcSatisfied4 cfg (encode p)
      (readR (portScale4 cfg *ᵥ pack u 0))
      (readR (portScale4 cfg *ᵥ (biPowerResponse4 cfg p *ᵥ pack u 0)))
      (readT (portScale4 cfg *ᵥ pack u 0))
      (readT (portScale4 cfg *ᵥ (biPowerResponse4 cfg p *ᵥ pack u 0))) :=
    (bi_gstc_iff_power_response cfg p hk heq (pack u 0)
      (biPowerResponse4 cfg p *ᵥ pack u 0)).mpr rfl
  rw [readT_portScale4_pack_zero cfg heq u] at hgstc
  have h3 := gstcSatisfied4_above cfg (encode p)
    (readR (portScale4 cfg *ᵥ pack u 0))
    (readR (portScale4 cfg *ᵥ (biPowerResponse4 cfg p *ᵥ pack u 0)))
    (readT (portScale4 cfg *ᵥ (biPowerResponse4 cfg p *ᵥ pack u 0))) hk hgstc
  simp only [readR_portScale4 cfg heq, readT_portScale4 cfg heq] at h3
  simp only [readR_pack, readR_biPowerResponse4_pack cfg p u,
    readT_biPowerResponse4_pack cfg p u] at h3
  exact h3

theorem power_balance_identical (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR eT : Vec2) (hk : cfg.kPar = 0) (hmed : identicalMedia cfg s)
    (hloss : sus.Lossless) (hgstc : gstcSatisfied cfg s sus eI eR eT) :
    jonesNormSqR eI = jonesNormSqR eR + jonesNormSqR eT := by
  have hbal := power_balance_jones_cleared cfg s sus eI eR eT hk hloss hgstc
  have hηI : (Wave.medium cfg s .incident).eta = (Wave.medium cfg s .transmitted).eta :=
    hmed
  rw [hηI] at hbal
  have hη : (Wave.medium cfg s .transmitted).eta ≠ 0 :=
    (Wave.medium cfg s .transmitted).eta_pos.ne'
  have h1 : jonesNormSqR eI * (Wave.medium cfg s .transmitted).eta
      = (jonesNormSqR eR + jonesNormSqR eT) * (Wave.medium cfg s .transmitted).eta := by
    linarith [hbal]
  exact mul_right_cancel₀ hη h1

theorem jonesNormSqR_smul_real (c : ℝ) (v : Vec2) :
    jonesNormSqR ((c : ℂ) • v) = c * c * jonesNormSqR v := by
  rw [jonesNormSqR_smul, Complex.normSq_ofReal]

theorem biForwardT_contractive (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) (u : Vec2) :
    jonesNormSqR (biForwardT cfg p *ᵥ u) ≤ jonesNormSqR u := by
  have hgstc := gstc_above_of_forward cfg p hk heq u
  have hloss : (encode p).Lossless := encode_lossless p
  have hmed : identicalMedia cfg .above := by
    simp [identicalMedia, Wave.medium, heq]
  have hbal := power_balance_identical cfg .above (encode p)
    ((Real.sqrt cfg.upper.eta : ℂ) • u)
    ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardR cfg p *ᵥ u))
    ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardT cfg p *ᵥ u)) hk hmed hloss hgstc
  have hI : jonesNormSqR ((Real.sqrt cfg.upper.eta : ℂ) • u)
      = (Real.sqrt cfg.upper.eta) ^ 2 * jonesNormSqR u := by
    rw [jonesNormSqR_smul_real]
    ring
  have hR : jonesNormSqR ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardR cfg p *ᵥ u))
      = (Real.sqrt cfg.upper.eta) ^ 2 * jonesNormSqR (biForwardR cfg p *ᵥ u) := by
    rw [jonesNormSqR_smul_real]
    ring
  have hT : jonesNormSqR ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardT cfg p *ᵥ u))
      = (Real.sqrt cfg.upper.eta) ^ 2 * jonesNormSqR (biForwardT cfg p *ᵥ u) := by
    rw [jonesNormSqR_smul_real]
    ring
  have hpos : 0 < (Real.sqrt cfg.upper.eta) ^ 2 := by
    have : 0 < Real.sqrt cfg.upper.eta := Real.sqrt_pos.2 cfg.upper.eta_pos
    nlinarith

  have hdiv : jonesNormSqR u = jonesNormSqR (biForwardR cfg p *ᵥ u)
      + jonesNormSqR (biForwardT cfg p *ᵥ u) := by
    have hscale : (Real.sqrt cfg.upper.eta) ^ 2 * jonesNormSqR u
        = (Real.sqrt cfg.upper.eta) ^ 2
          * (jonesNormSqR (biForwardR cfg p *ᵥ u) + jonesNormSqR (biForwardT cfg p *ᵥ u)) := by
      linarith [hbal, hI, hR, hT]
    exact mul_left_cancel₀ (ne_of_gt hpos) hscale
  have hnonneg : 0 ≤ jonesNormSqR (biForwardR cfg p *ᵥ u) := jonesNormSqR_nonneg _
  linarith [hdiv, hnonneg]

theorem perfect_efficiency_reflection_vanishes (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (u v : Vec2) (α : ℂ)
    (hu : isNormalized u) (hv : isNormalized v)
    (hconv : biForwardT cfg p *ᵥ u = α • v) (heff : efficiency α = 1) :
    biForwardR cfg p *ᵥ u = 0 := by
  have hgstc := gstc_above_of_forward cfg p hk heq u
  have hloss : (encode p).Lossless := encode_lossless p
  have hmed : identicalMedia cfg .above := by
    simp [identicalMedia, Wave.medium, heq]
  have hbal := power_balance_identical cfg .above (encode p)
    ((Real.sqrt cfg.upper.eta : ℂ) • u)
    ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardR cfg p *ᵥ u))
    ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardT cfg p *ᵥ u)) hk hmed hloss hgstc
  rw [hconv] at hbal
  have hu' : jonesNormSqR u = 1 := isNormalized_jonesNormSqR u hu
  have hv' : jonesNormSqR v = 1 := isNormalized_jonesNormSqR v hv
  have hα : Complex.normSq α = 1 := by simpa [efficiency] using heff
  have hI : jonesNormSqR ((Real.sqrt cfg.upper.eta : ℂ) • u)
      = (Real.sqrt cfg.upper.eta) ^ 2 := by
    rw [jonesNormSqR_smul_real, hu']
    ring
  have hT : jonesNormSqR ((Real.sqrt cfg.upper.eta : ℂ) • (α • v))
      = (Real.sqrt cfg.upper.eta) ^ 2 := by
    rw [jonesNormSqR_smul_real, jonesNormSqR_smul, hv', hα]
    ring
  have hR : jonesNormSqR ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardR cfg p *ᵥ u)) = 0 := by
    linarith [hbal, hI, hT]
  have hR0 : (Real.sqrt cfg.upper.eta : ℂ) • (biForwardR cfg p *ᵥ u) = 0 :=
    (jonesNormSqR_eq_zero_iff _).mp hR
  have hz0 : (Real.sqrt cfg.upper.eta : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 cfg.upper.eta_pos))
  ext i
  have hi := congrArg (fun v : Vec2 => v i) hR0
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact (mul_eq_zero.mp hi).resolve_left hz0

theorem encode_chiTT_ee (p : BIParams) : chiTT (encode p).ee = p.eeBlock := by
  rw [encode, chiTT_ten3OfTT]

theorem encode_chiTT_mm (p : BIParams) : chiTT (encode p).mm = p.mmBlock := by
  rw [encode, chiTT_ten3OfTT]

theorem reflectionless_transmission_is_isometry (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta) (w : Vec2)
    (hR : biForwardR cfg p = 0) :
    jonesNormSqR (biForwardT cfg p *ᵥ w) = jonesNormSqR w := by
  have hgstc := gstc_above_of_forward cfg p hk heq w
  have hloss : (encode p).Lossless := encode_lossless p
  have hmed : identicalMedia cfg .above := by
    simp [identicalMedia, Wave.medium, heq]
  have hbal := power_balance_identical cfg .above (encode p)
    ((Real.sqrt cfg.upper.eta : ℂ) • w)
    ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardR cfg p *ᵥ w))
    ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardT cfg p *ᵥ w)) hk hmed hloss hgstc
  have hR0 : (Real.sqrt cfg.upper.eta : ℂ) • (biForwardR cfg p *ᵥ w) = 0 := by
    rw [hR, Matrix.zero_mulVec, smul_zero]
  have hRnorm : jonesNormSqR ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardR cfg p *ᵥ w)) = 0 :=
    (jonesNormSqR_eq_zero_iff _).mpr hR0
  have hI : jonesNormSqR ((Real.sqrt cfg.upper.eta : ℂ) • w)
      = (Real.sqrt cfg.upper.eta) * (Real.sqrt cfg.upper.eta) * jonesNormSqR w := by
    rw [jonesNormSqR_smul_real]
  have hT : jonesNormSqR ((Real.sqrt cfg.upper.eta : ℂ) • (biForwardT cfg p *ᵥ w))
      = (Real.sqrt cfg.upper.eta) * (Real.sqrt cfg.upper.eta)
        * jonesNormSqR (biForwardT cfg p *ᵥ w) := by
    rw [jonesNormSqR_smul_real]
  have hkey : (Real.sqrt cfg.upper.eta) * (Real.sqrt cfg.upper.eta) * jonesNormSqR w
      = (Real.sqrt cfg.upper.eta) * (Real.sqrt cfg.upper.eta)
        * jonesNormSqR (biForwardT cfg p *ᵥ w) := by
    linarith [hbal, hI, hT, hRnorm]
  have hz0 : (Real.sqrt cfg.upper.eta) * (Real.sqrt cfg.upper.eta) ≠ 0 := by
    have h : Real.sqrt cfg.upper.eta ≠ 0 := ne_of_gt (Real.sqrt_pos.2 cfg.upper.eta_pos)
    exact mul_ne_zero h h
  exact mul_left_cancel₀ hz0 hkey.symm

end OrthogonalClasses
end GSTC.Scattering
