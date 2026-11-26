/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module
public import GSTC.Scattering.RotatedRankOneBudgets

public section
set_option autoImplicit false
namespace GSTC.Scattering.RotatedRankOneRecovery
open scoped Matrix
open BIInverse RotatedRankOneResources
open SusceptibilityBudget MaterialSpace BIPolynomials ClassFeasibility

@[expose] def flipY (sc : RotScalars) : RotScalars :=
  {p0 := -sc.p0, p1 := -sc.p1, t := sc.t, u := sc.u, w := -sc.w, q := sc.q}

theorem rotScalars_neg_y (s r c j x y : ℝ) :
    rotScalars s r c j x (-y)=flipY (rotScalars s r c j x y) := by
  simp [rotScalars, flipY, rotP0, rotP1, rotT, rotU, rotW, rotQ, rotF]
  ring_nf
  simp

theorem rotDirect_flipY (sc : RotScalars) (v : ℝ) :
    rotDirect (flipY sc) v=rotDirect sc v := by
  have h1 : -sc.p0+sc.t*v=-(sc.p0-sc.t*v) := by ring
  have h2 : -sc.p0-sc.t*v=-(sc.p0+sc.t*v) := by ring
  have h3 : -sc.p1+sc.u*v=-(sc.p1-sc.u*v) := by ring
  have h4 : -sc.p1-sc.u*v=-(sc.p1+sc.u*v) := by ring
  simp only [rotDirect, flipY, h1, h2, h3, h4, abs_neg, neg_sq]
  exact max_comm _ _

theorem rotCoupling_flipY (sc : RotScalars) (v : ℝ) :
    rotCoupling (flipY sc) v=rotCoupling sc v := by
  simp [rotCoupling, flipY]

theorem resources_abs_y (s r c j x y v : ℝ) :
    rotDirect (rotScalars s r c j x y) v=rotDirect (rotScalars s r c j x |y|) v ∧
    rotCoupling (rotScalars s r c j x y) v=rotCoupling (rotScalars s r c j x |y|) v := by
  by_cases hy : 0 ≤ y
  · simp [abs_of_nonneg hy]
  · rw [abs_of_neg (lt_of_not_ge hy), rotScalars_neg_y,
      rotDirect_flipY, rotCoupling_flipY]
    exact ⟨rfl,rfl⟩

theorem reduced_domain_of_circles (s c x y h k : ℝ)
    (hx : y^2+x^2=1) (hb : k^2+h^2=1) (hf : rotF s c x y ≠ 0) :
    rotDomain s c x |k*x-h*y| := by
  have hrel := relativePhase_circle x y h k hx hb
  have hys : Real.sqrt (1-x^2)=|y| := by
    rw [show 1-x^2=y^2 by linarith, Real.sqrt_sq_eq_abs]
  refine ⟨?_,?_,abs_nonneg _,?_,?_⟩
  · nlinarith [sq_nonneg y]
  · nlinarith [sq_nonneg y]
  · have hsq : |k*x-h*y|^2 ≤ 1 := by
      rw [sq_abs]
      nlinarith [sq_nonneg (h*x+k*y)]
    nlinarith [abs_nonneg (k*x-h*y)]
  · simpa only [hys, rotF, sq_abs] using hf

theorem resources_reduced (s r c j x y v : ℝ) (hx : y^2+x^2=1) :
    rotDirect (rotScalars s r c j x y) v=rotDirect (rotReducedScalars s r c j x) v ∧
    rotCoupling (rotScalars s r c j x y) v=rotCoupling (rotReducedScalars s r c j x) v := by
  have hys : Real.sqrt (1-x^2)=|y| := by
    rw [show 1-x^2=y^2 by linarith, Real.sqrt_sq_eq_abs]
  simpa only [rotReducedScalars, hys] using resources_abs_y s r c j x y v

theorem relativePhase_trig (φ β : ℝ) :
    Real.sin β*Real.cos φ-Real.cos β*Real.sin φ=Real.cos (Real.pi/2+φ-β) := by
  simp [Real.cos_sub, Real.cos_add, Real.sin_add]
  ring

theorem every_completion_reduced_budgets (cfg : Config) (p : BIParams) (s r c j x y h k : ℝ)
    (hr : r^2+s^2=1) (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hb : k^2+h^2=1)
    (hf : rotF s c x y ≠ 0) (heta : cfg.upper.eta=cfg.vac.eta0)
    (hp : biPowerResponse4 cfg p=familyResponse s r c j x y h k) :
    rotDomain s c x |k*x-h*y| ∧
    spectralDirectBudget cfg (assign p)=rotDirect (rotReducedScalars s r c j x) |k*x-h*y| ∧
    spectralCouplingBudget cfg (assign p)=rotCoupling (rotReducedScalars s r c j x) |k*x-h*y| := by
  have hbds := every_completion_spectral_budgets cfg p s r c j x y h k hr hc hx hb hf heta hp
  have hred := resources_reduced s r c j x y |k*x-h*y| hx
  exact ⟨reduced_domain_of_circles s c x y h k hx hb hf,
    hbds.1.trans hred.1, hbds.2.trans hred.2⟩

def physicalResourceImage (cfg : Config) (s r c j : ℝ) : Set (ℝ × ℝ) :=
  {b | ∃ φ β : ℝ, ∃ p : BIParams,
    rotF s c (Real.cos φ) (Real.sin φ) ≠ 0 ∧
    biPowerResponse4 cfg p=familyResponse s r c j
      (Real.cos φ) (Real.sin φ) (Real.cos β) (Real.sin β) ∧
    b=(spectralDirectBudget cfg (assign p), spectralCouplingBudget cfg (assign p))}

theorem exact_physical_resource_image (cfg : Config) (s r c j : ℝ)
    (hr : r^2+s^2=1) (hc : j^2+c^2=1) (heta : cfg.upper.eta=cfg.vac.eta0)
    (b : ℝ × ℝ) :
    b ∈ physicalResourceImage cfg s r c j ↔
      ∃ x v : ℝ, rotDomain s c x v ∧
        b=(rotDirect (rotReducedScalars s r c j x) v,
          rotCoupling (rotReducedScalars s r c j x) v) := by
  constructor
  · rintro ⟨φ,β,p,hF,hp,rfl⟩
    have hh := every_completion_reduced_budgets cfg p s r c j
      (Real.cos φ) (Real.sin φ) (Real.cos β) (Real.sin β)
      hr hc (Real.sin_sq_add_cos_sq φ) (Real.sin_sq_add_cos_sq β) hF heta hp
    exact ⟨_,_,hh.1, Prod.ext hh.2.1 hh.2.2⟩
  · rintro ⟨x,v,hd,hb⟩
    obtain ⟨φ,β,hx,hv,hsc⟩ := rotDomain_surjective s r c j x v
      hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1
    have hxy : 0 ≤ 1-x^2 := by nlinarith [hd.1,hd.2.1]
    have hFeq : rotF s c (Real.cos φ) (Real.sin φ)=
        rotF s c x (Real.sqrt (1-x^2)) := by
      have hsin := Real.sin_sq_add_cos_sq φ
      rw [hx] at hsin
      dsimp [rotF]
      rw [hx,Real.sq_sqrt hxy,show Real.sin φ^2=1-x^2 by linarith]
    have hF : rotF s c (Real.cos φ) (Real.sin φ) ≠ 0 := hFeq.trans_ne hd.2.2.2.2
    let p := parametersForResponse cfg (familyResponse s r c j
      (Real.cos φ) (Real.sin φ) (Real.cos β) (Real.sin β))
    have hp := familyResponse_recovered cfg s r c j (Real.cos φ) (Real.sin φ)
      (Real.cos β) (Real.sin β) hr hc
      (Real.sin_sq_add_cos_sq φ) (Real.sin_sq_add_cos_sq β) hF
    have hbud := recovered_spectral_budgets cfg s r c j (Real.cos φ) (Real.sin φ)
      (Real.cos β) (Real.sin β) hr hc
      (Real.sin_sq_add_cos_sq φ) (Real.sin_sq_add_cos_sq β) hF heta
    rw [relativePhase_trig, hv, hsc] at hbud
    refine ⟨φ,β,p,hF,hp,?_⟩
    exact hb.trans (Prod.ext hbud.1 hbud.2).symm

end GSTC.Scattering.RotatedRankOneRecovery
