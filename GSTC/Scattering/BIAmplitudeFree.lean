/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing

public import GSTC.Scattering.BIConversionEquivalence
public import GSTC.Scattering.BIPolynomials

public import Mathlib.Algebra.MvPolynomial.Degrees

public section

namespace GSTC.Scattering
namespace BIAmplitudeFree

open scoped Matrix
open BIFeasibility
open BIPhysicalFeasibility
open BIPolynomials

noncomputable section

@[expose] def ofComplex (z : ℂ) : CPoly :=
  ⟨MvPolynomial.C z.re, MvPolynomial.C z.im⟩

theorem ofComplex_eval (a : BICoord → ℝ) (z : ℂ) :
    CPoly.evalHom a (ofComplex z) = z := by
  apply Complex.ext <;>
    simp [CPoly.evalHom, CPoly.eval, ofComplex, MvPolynomial.eval_C]

@[expose] def numVecPoly (cfg : Config) (u : Vec2) (i : Fin 2) : CPoly :=
  (biNumeratorTPoly cfg i 0) * ofComplex (u 0)
    + (biNumeratorTPoly cfg i 1) * ofComplex (u 1)

theorem numVecPoly_eval (cfg : Config) (p : BIParams) (u : Vec2) (i : Fin 2) :
    CPoly.evalHom (assign p) (numVecPoly cfg u i) = (biNumeratorT cfg p *ᵥ u) i := by
  have h0 : CPoly.evalHom (assign p) (biNumeratorTPoly cfg i 0) = biNumeratorT cfg p i 0 :=
    CPoly.evalHom_eq_of_map_eq (biNumeratorTPoly_eval cfg p) i 0
  have h1 : CPoly.evalHom (assign p) (biNumeratorTPoly cfg i 1) = biNumeratorT cfg p i 1 :=
    CPoly.evalHom_eq_of_map_eq (biNumeratorTPoly_eval cfg p) i 1
  rw [numVecPoly]
  rw [map_add, map_mul, map_mul, h0, h1, ofComplex_eval, ofComplex_eval]
  rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]

@[expose] def collinearityPoly (cfg : Config) (u v : Vec2) : CPoly :=
  ofComplex (v 0) * numVecPoly cfg u 1 - ofComplex (v 1) * numVecPoly cfg u 0

theorem collinearityPoly_eval (cfg : Config) (p : BIParams) (u v : Vec2) :
    CPoly.evalHom (assign p) (collinearityPoly cfg u v)
      = (v 0) * ((biNumeratorT cfg p *ᵥ u) 1) - (v 1) * ((biNumeratorT cfg p *ᵥ u) 0) := by
  rw [collinearityPoly]
  rw [map_sub, map_mul, map_mul]
  rw [numVecPoly_eval, numVecPoly_eval, ofComplex_eval, ofComplex_eval]

@[expose] def numRePoly (cfg : Config) (i k : Fin 2) : MvPolynomial BICoord ℝ :=
  (biNumeratorTPoly cfg i k).re

@[expose] def numImPoly (cfg : Config) (i k : Fin 2) : MvPolynomial BICoord ℝ :=
  (biNumeratorTPoly cfg i k).im

@[expose] def detRePoly (cfg : Config) : MvPolynomial BICoord ℝ :=
  (biDetPoly cfg).re

@[expose] def detImPoly (cfg : Config) : MvPolynomial BICoord ℝ :=
  (biDetPoly cfg).im

@[expose] def transRePoly (cfg : Config) (u : Vec2) (i : Fin 2) :
    MvPolynomial BICoord ℝ :=
  numRePoly cfg i 0 * MvPolynomial.C (u 0).re
    + numRePoly cfg i 1 * MvPolynomial.C (u 1).re
    - (numImPoly cfg i 0 * MvPolynomial.C (u 0).im
        + numImPoly cfg i 1 * MvPolynomial.C (u 1).im)

@[expose] def transImPoly (cfg : Config) (u : Vec2) (i : Fin 2) :
    MvPolynomial BICoord ℝ :=
  numRePoly cfg i 0 * MvPolynomial.C (u 0).im
    + numRePoly cfg i 1 * MvPolynomial.C (u 1).im
    + (numImPoly cfg i 0 * MvPolynomial.C (u 0).re
        + numImPoly cfg i 1 * MvPolynomial.C (u 1).re)

@[expose] def effPoly (cfg : Config) (u : Vec2) (η : ℝ) : MvPolynomial BICoord ℝ :=
  transRePoly cfg u 0 ^ 2 + transImPoly cfg u 0 ^ 2
    + transRePoly cfg u 1 ^ 2 + transImPoly cfg u 1 ^ 2
    - MvPolynomial.C η * (detRePoly cfg ^ 2 + detImPoly cfg ^ 2)

theorem numRePoly_eval (cfg : Config) (p : BIParams) (i k : Fin 2) :
    (numRePoly cfg i k).eval (assign p) = (biNumeratorT cfg p i k).re := by
  rw [numRePoly]
  exact biNumeratorTPoly_eval_re cfg p i k

theorem numImPoly_eval (cfg : Config) (p : BIParams) (i k : Fin 2) :
    (numImPoly cfg i k).eval (assign p) = (biNumeratorT cfg p i k).im := by
  rw [numImPoly]
  exact biNumeratorTPoly_eval_im cfg p i k

theorem detRePoly_eval (cfg : Config) (p : BIParams) :
    (detRePoly cfg).eval (assign p) = (biDet cfg p).re := by
  rw [detRePoly]
  exact biDetPoly_eval_re cfg p

theorem detImPoly_eval (cfg : Config) (p : BIParams) :
    (detImPoly cfg).eval (assign p) = (biDet cfg p).im := by
  rw [detImPoly]
  exact biDetPoly_eval_im cfg p

private lemma star_mul_self_re (z : ℂ) : (star z * z).re = z.normSq := by
  rw [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Complex.normSq_apply]
  ring

theorem jonesNormSqR_eq_sum_normSq (u : Vec2) :
    jonesNormSqR u = (u 0).normSq + (u 1).normSq := by
  rw [jonesNormSqR, jonesNormSq, jonesInner]
  simp only [Complex.add_re]
  rw [star_mul_self_re, star_mul_self_re]

theorem transRePoly_eval (cfg : Config) (p : BIParams) (u : Vec2) (i : Fin 2) :
    (transRePoly cfg u i).eval (assign p) = ((biNumeratorT cfg p *ᵥ u) i).re := by
  rw [transRePoly]
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, numRePoly_eval, numImPoly_eval]
  rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  simp only [Complex.add_re, Complex.mul_re]
  ring

theorem transImPoly_eval (cfg : Config) (p : BIParams) (u : Vec2) (i : Fin 2) :
    (transImPoly cfg u i).eval (assign p) = ((biNumeratorT cfg p *ᵥ u) i).im := by
  rw [transImPoly]
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    numRePoly_eval, numImPoly_eval]
  rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  simp only [Complex.add_im, Complex.mul_im]
  ring

theorem effPoly_eval (cfg : Config) (p : BIParams) (u : Vec2) (η : ℝ) :
    (effPoly cfg u η).eval (assign p)
      = jonesNormSqR (biNumeratorT cfg p *ᵥ u) - η * (biDet cfg p).normSq := by
  rw [effPoly]
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_pow]
  rw [transRePoly_eval, transImPoly_eval, transRePoly_eval, transImPoly_eval,
    detRePoly_eval, detImPoly_eval]
  rw [jonesNormSqR_eq_sum_normSq]
  simp only [Complex.normSq_apply]
  ring

theorem vec2_ext {x y : Vec2} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i
  fin_cases i
  · show x 0 = y 0
    exact h0
  · show x 1 = y 1
    exact h1

theorem collinearity_components {v w : Vec2} (h : (v 0) * (w 1) - (v 1) * (w 0) = 0)
    (hv : v ≠ 0) : ∃ β : ℂ, w 0 = β * v 0 ∧ w 1 = β * v 1 := by
  have h' : (v 0) * (w 1) = (v 1) * (w 0) := sub_eq_zero.mp h
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i
      · exact hv0
      · exact h1
    have hw0 : w 0 = 0 := by
      have hz : (v 1) * (w 0) = 0 := by
        rw [← mul_zero (v 1), ← h']
        rw [hv0]
        ring
      exact mul_eq_zero.mp hz |>.resolve_left hv1
    refine ⟨(w 1) / (v 1), ?_, ?_⟩
    · rw [hw0, hv0]
      ring
    · field_simp
  · refine ⟨(w 0) / (v 0), ?_, ?_⟩
    · field_simp
    · have hz : (w 1) = (v 1) * (w 0) / (v 0) := by
        field_simp
        calc w 1 * v 0 = v 0 * w 1 := mul_comm _ _
          _ = v 1 * w 0 := h'
      rw [hz]
      field_simp

theorem collinearity_eq_smul {v w : Vec2} (h : (v 0) * (w 1) - (v 1) * (w 0) = 0)
    (hv : v ≠ 0) : ∃ β : ℂ, w = β • v := by
  obtain ⟨β, h0, h1⟩ := collinearity_components h hv
  exact ⟨β, vec2_ext h0 h1⟩

theorem conversion_iff_amplitudeFree (cfg : Config) (p : BIParams) (u v : Vec2)
    (η : ℝ) (hv : isNormalizedJones v) :
    (∃ α : ℂ, biForwardT cfg p *ᵥ u = α • v ∧ efficiency α = η)
      ↔ (CPoly.evalHom (assign p) (collinearityPoly cfg u v) = 0 ∧
          (effPoly cfg u η).eval (assign p) = 0) := by
  constructor
  · rintro ⟨α, hT, hη⟩
    have hη' : Complex.normSq α = η := hη
    have hcleared : biNumeratorT cfg p *ᵥ u = (biDet cfg p * α) • v :=
      (biForwardT_eq_iff_cleared cfg p u v α).mp hT
    have hQ0 : (biNumeratorT cfg p *ᵥ u) 0 = (biDet cfg p * α) * (v 0) := by
      have h := congrArg (fun w : Vec2 => w 0) hcleared
      simpa [Pi.smul_apply, smul_eq_mul] using h
    have hQ1 : (biNumeratorT cfg p *ᵥ u) 1 = (biDet cfg p * α) * (v 1) := by
      have h := congrArg (fun w : Vec2 => w 1) hcleared
      simpa [Pi.smul_apply, smul_eq_mul] using h
    refine ⟨?_, ?_⟩
    · rw [collinearityPoly_eval, hQ0, hQ1]
      ring
    · rw [effPoly_eval]
      have hnorm : jonesNormSqR (biNumeratorT cfg p *ᵥ u)
          = Complex.normSq (biDet cfg p * α) * jonesNormSqR v := by
        rw [hcleared, jonesNormSqR_smul]
      rw [hnorm, jonesNormSqR_eq_one_of_normalized hv, Complex.normSq_mul, hη']
      ring
  · rintro ⟨hcol, heff⟩
    have hcol' : (v 0) * ((biNumeratorT cfg p *ᵥ u) 1)
        - (v 1) * ((biNumeratorT cfg p *ᵥ u) 0) = 0 := by
      rw [← collinearityPoly_eval cfg p u v]
      exact hcol
    have hvne : v ≠ 0 := by
      intro h
      have hz : jonesNormSqR v = 0 := (jonesNormSqR_eq_zero_iff v).mpr h
      have hone : jonesNormSqR v = 1 := jonesNormSqR_eq_one_of_normalized hv
      rw [hone] at hz
      exact absurd hz one_ne_zero
    obtain ⟨β, hβ⟩ := collinearity_eq_smul hcol' hvne
    have heff' : jonesNormSqR (biNumeratorT cfg p *ᵥ u)
        - η * (biDet cfg p).normSq = 0 := by
      rw [← effPoly_eval cfg p u η]
      exact heff
    have hβsq : Complex.normSq β = η * (biDet cfg p).normSq := by
      have hn : jonesNormSqR (biNumeratorT cfg p *ᵥ u)
          = η * (biDet cfg p).normSq := by
        linarith [heff']
      rw [hβ, jonesNormSqR_smul, jonesNormSqR_eq_one_of_normalized hv] at hn
      linarith
    have hdne : biDet cfg p ≠ 0 := biDet_ne_zero cfg p
    have hdne' : (biDet cfg p).normSq ≠ 0 :=
      fun h => hdne (Complex.normSq_eq_zero.mp h)
    refine ⟨β * (biDet cfg p)⁻¹, ?_, ?_⟩
    · have hde : biDet cfg p * (β * (biDet cfg p)⁻¹) = β := by
        field_simp
      have hcleared : biNumeratorT cfg p *ᵥ u
          = (biDet cfg p * (β * (biDet cfg p)⁻¹)) • v := by
        rw [hde, hβ]
      exact (biForwardT_eq_iff_cleared cfg p u v _).mpr hcleared
    · have hde : biDet cfg p * (β * (biDet cfg p)⁻¹) = β := by
        field_simp
      have h1 : Complex.normSq (biDet cfg p) * Complex.normSq (β * (biDet cfg p)⁻¹)
          = Complex.normSq β := by
        calc
          Complex.normSq (biDet cfg p) * Complex.normSq (β * (biDet cfg p)⁻¹)
              = Complex.normSq (biDet cfg p * (β * (biDet cfg p)⁻¹)) := by
                rw [Complex.normSq_mul (biDet cfg p) (β * (biDet cfg p)⁻¹)]
          _ = Complex.normSq β := by rw [hde]
      have h3 : Complex.normSq (biDet cfg p) * Complex.normSq (β * (biDet cfg p)⁻¹)
          = Complex.normSq (biDet cfg p) * η := by
        rw [h1, hβsq]
        ring
      have h2 : Complex.normSq (β * (biDet cfg p)⁻¹) = η := mul_left_cancel₀ hdne' h3
      simpa [efficiency] using h2

@[expose] def AmplitudeFreePolynomialFeasible (cfg : Config) (c : SheetClass) (b : Budget)
    (u₁ u₂ v₁ v₂ : Vec2) (η₁ η₂ : ℝ) : Prop :=
  isNormalizedJones u₁ ∧ isNormalizedJones u₂ ∧ isNormalizedJones v₁ ∧
    isNormalizedJones v₂ ∧
  ∃ p : BIParams, InClass c p ∧ WithinBudget b p ∧
    CPoly.evalHom (assign p) (collinearityPoly cfg u₁ v₁) = 0 ∧
    (effPoly cfg u₁ η₁).eval (assign p) = 0 ∧
    CPoly.evalHom (assign p) (collinearityPoly cfg u₂ v₂) = 0 ∧
    (effPoly cfg u₂ η₂).eval (assign p) = 0

theorem physicalFeasible_iff_amplitudeFreePolynomialFeasible (cfg : Config)
    (c : SheetClass) (b : Budget) (u₁ u₂ v₁ v₂ : Vec2) (η₁ η₂ : ℝ) :
    PhysicalFeasible cfg c b u₁ u₂ v₁ v₂ η₁ η₂
      ↔ AmplitudeFreePolynomialFeasible cfg c b u₁ u₂ v₁ v₂ η₁ η₂ := by
  constructor
  · rintro ⟨hn₁, hn₂, hn₃, hn₄, p, hc, hb, α₁, α₂, ht₁, ht₂, he₁, he₂⟩
    have h1 := (conversion_iff_amplitudeFree cfg p u₁ v₁ η₁ hn₃).mp ⟨α₁, ht₁, he₁⟩
    have h2 := (conversion_iff_amplitudeFree cfg p u₂ v₂ η₂ hn₄).mp ⟨α₂, ht₂, he₂⟩
    exact ⟨hn₁, hn₂, hn₃, hn₄, p, hc, hb, h1.1, h1.2, h2.1, h2.2⟩
  · rintro ⟨hn₁, hn₂, hn₃, hn₄, p, hc, hb, hc₁, he₁, hc₂, he₂⟩
    obtain ⟨α₁, ht₁, ha₁⟩ :=
      (conversion_iff_amplitudeFree cfg p u₁ v₁ η₁ hn₃).mpr ⟨hc₁, he₁⟩
    obtain ⟨α₂, ht₂, ha₂⟩ :=
      (conversion_iff_amplitudeFree cfg p u₂ v₂ η₂ hn₄).mpr ⟨hc₂, he₂⟩
    exact ⟨hn₁, hn₂, hn₃, hn₄, p, hc, hb, α₁, α₂, ht₁, ht₂, ha₁, ha₂⟩

theorem collinearityPoly_eq_zero_iff (cfg : Config) (p : BIParams) (u v : Vec2) :
    CPoly.evalHom (assign p) (collinearityPoly cfg u v) = 0
      ↔ (collinearityPoly cfg u v).re.eval (assign p) = 0
        ∧ (collinearityPoly cfg u v).im.eval (assign p) = 0 := by
  constructor
  · intro h
    have hre : (collinearityPoly cfg u v).re.eval (assign p) = 0 := by
      have h' := congrArg Complex.re h
      rw [CPoly.evalHom_apply] at h'
      rwa [← CPoly.eval_re] at h'
    have him : (collinearityPoly cfg u v).im.eval (assign p) = 0 := by
      have h' := congrArg Complex.im h
      rw [CPoly.evalHom_apply] at h'
      rwa [← CPoly.eval_im] at h'
    exact ⟨hre, him⟩
  · rintro ⟨hre, him⟩
    have h' : (CPoly.evalHom (assign p) (collinearityPoly cfg u v)).re = 0 := by
      rw [CPoly.evalHom_apply, ← CPoly.eval_re]
      exact hre
    have h'' : (CPoly.evalHom (assign p) (collinearityPoly cfg u v)).im = 0 := by
      rw [CPoly.evalHom_apply, ← CPoly.eval_im]
      exact him
    exact Complex.ext h' h''

theorem amplitudeFreeConstraints_vanishing (cfg : Config) (p : BIParams)
    (u₁ u₂ v₁ v₂ : Vec2) (η₁ η₂ : ℝ) :
    (CPoly.evalHom (assign p) (collinearityPoly cfg u₁ v₁) = 0 ∧
      (effPoly cfg u₁ η₁).eval (assign p) = 0 ∧
      CPoly.evalHom (assign p) (collinearityPoly cfg u₂ v₂) = 0 ∧
      (effPoly cfg u₂ η₂).eval (assign p) = 0)
      ↔ ((collinearityPoly cfg u₁ v₁).re.eval (assign p) = 0 ∧
        (collinearityPoly cfg u₁ v₁).im.eval (assign p) = 0 ∧
        (effPoly cfg u₁ η₁).eval (assign p) = 0 ∧
        (collinearityPoly cfg u₂ v₂).re.eval (assign p) = 0 ∧
        (collinearityPoly cfg u₂ v₂).im.eval (assign p) = 0 ∧
        (effPoly cfg u₂ η₂).eval (assign p) = 0) := by
  constructor
  · rintro ⟨hc₁, he₁, hc₂, he₂⟩
    have h1 := (collinearityPoly_eq_zero_iff cfg p u₁ v₁).mp hc₁
    have h2 := (collinearityPoly_eq_zero_iff cfg p u₂ v₂).mp hc₂
    exact ⟨h1.1, h1.2, he₁, h2.1, h2.2, he₂⟩
  · rintro ⟨hr₁, hi₁, he₁, hr₂, hi₂, he₂⟩
    have h1 := (collinearityPoly_eq_zero_iff cfg p u₁ v₁).mpr ⟨hr₁, hi₁⟩
    have h2 := (collinearityPoly_eq_zero_iff cfg p u₂ v₂).mpr ⟨hr₂, hi₂⟩
    exact ⟨h1, he₁, h2, he₂⟩

end

end BIAmplitudeFree

end GSTC.Scattering
