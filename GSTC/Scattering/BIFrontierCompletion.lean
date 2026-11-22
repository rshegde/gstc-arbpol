/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BICompletionMinimum
public import GSTC.Scattering.BIRankOneTheorem

public section
set_option autoImplicit false
namespace GSTC.Scattering.BIFrontierCompletion
open Matrix Operator BIInverse BICompletionMinimum BIRankOneCompletion BIRankOneTheorem
open FeasibilityRotation
open scoped Matrix

theorem readT_completion (X Z Y : Ten2) (u : Vec2) :
    readT (completion X Z Y *ᵥ pack u 0) = X *ᵥ u := by
  rw [completion, block, scatteringMatrix4_mulVec, readT_pack]
  simp [ScatteringMatrix.out2]

theorem symmetric_eq_completion (S : Matrix (Fin 4) (Fin 4) ℂ) (X : Ten2)
    (hs : S.transpose = S) (ht : (asScattering S).t21 = X) :
    S = completion X (asScattering S).r1 (asScattering S).r2 := by
  have h12 : (asScattering S).t12 = X.transpose := by
    rw [← ht]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simpa [asScattering, Matrix.transpose_apply] using
        congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M _ _) hs.symm
  calc
    S = scatteringMatrix4 (asScattering S) := (scatteringMatrix4_asScattering S).symm
    _ = completion X (asScattering S).r1 (asScattering S).r2 := by
      unfold completion block
      congr 1
      cases h : asScattering S
      simp_all

theorem admissible_iff_rankOne (X Z Y : Ten2) (n : Vec2) (d : ℝ)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hX : X.det ≠ 0) (hn : star n ⬝ᵥ n = 1) (hd : 0 ≤ d)
    (hdefect : 1 - X.transpose * X.map star = (d : ℂ) • projection n) :
    admissible u₁ u₂ v₁ v₂ η (completion X Z Y) ↔
      (∃ θ : ℝ,
        Z = (Complex.exp ((θ : ℂ) * Complex.I) * (Real.sqrt d : ℂ)) • symmetricOuter n ∧
        Y = forcedY X Z) ∧
      IsUnit ((1 + Theta * completion X Z Y).det) ∧
      cross v₁ (X *ᵥ u₁) = 0 ∧ cross v₂ (X *ᵥ u₂) = 0 ∧
      jonesNormSqR (X *ᵥ u₁) = η.1 ∧ jonesNormSqR (X *ᵥ u₂) = η.2 := by
  have hr := rank_one_completion_iff X Z Y n d hX hn hd hdefect
  simp only [admissible, readT_completion]
  constructor
  · rintro ⟨hs, hu, hp, h₁, h₂, he₁, he₂⟩
    exact ⟨hr.mp ⟨hs,hu⟩, hp, h₁, h₂, he₁, he₂⟩
  · rintro ⟨hphase, hp, h₁, h₂, he₁, he₂⟩
    exact ⟨(hr.mpr hphase).1, (hr.mpr hphase).2, hp, h₁, h₂, he₁, he₂⟩

theorem admissible_has_rankOne (S : Matrix (Fin 4) (Fin 4) ℂ) (X : Ten2)
    (n : Vec2) (d : ℝ) (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hX : X.det ≠ 0) (hn : star n ⬝ᵥ n = 1) (hd : 0 ≤ d)
    (hdefect : 1 - X.transpose * X.map star = (d : ℂ) • projection n)
    (ht : (asScattering S).t21 = X) (hS : admissible u₁ u₂ v₁ v₂ η S) :
    ∃ θ : ℝ, ∃ Z : Ten2,
      Z = (Complex.exp ((θ : ℂ) * Complex.I) * (Real.sqrt d : ℂ)) • symmetricOuter n ∧
      S = completion X Z (forcedY X Z) := by
  have hs := symmetric_eq_completion S X hS.1 ht
  have ha := hS
  rw [hs] at ha
  obtain ⟨⟨θ,hZ,hY⟩, _⟩ := (admissible_iff_rankOne X (asScattering S).r1
    (asScattering S).r2 n d u₁ u₂ v₁ v₂ η hX hn hd hdefect).mp ha
  exact ⟨θ, (asScattering S).r1, hZ, by rw [← hY]; exact hs⟩

end GSTC.Scattering.BIFrontierCompletion
