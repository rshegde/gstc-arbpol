/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIAmplitudeFree

public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Order.Compact

public section
namespace GSTC.Scattering.MaterialSpace
open BIFeasibility BIPhysicalFeasibility BIPolynomials BIAmplitudeFree
open scoped Matrix

abbrev MaterialCoordinates := BICoord → ℝ

@[expose] def parameters (x : MaterialCoordinates) : BIParams :=
  ⟨x .ee00, x .ee01, x .ee11, x .mm00, x .mm01, x .mm11,
    x .g00, x .g01, x .g10, x .g11⟩
theorem assign_parameters (x : MaterialCoordinates) : assign (parameters x) = x := by
  funext k
  cases k <;> rfl
theorem parameters_assign (p : BIParams) : parameters (assign p) = p := by
  cases p
  rfl

@[expose] def classCoordinates (c : SheetClass) : Set MaterialCoordinates :=
  {x | InClass c (parameters x)}
theorem classCoordinates_closed (c : SheetClass) : IsClosed (classCoordinates c) := by
  have h (k : BICoord) : IsClosed {x : MaterialCoordinates | x k = 0} :=
    isClosed_eq (continuous_apply k) continuous_const
  cases c
  · change IsClosed {x : MaterialCoordinates | x .mm00 = 0 ∧ x .mm01 = 0 ∧ x .mm11 = 0 ∧
      x .g00 = 0 ∧ x .g01 = 0 ∧ x .g10 = 0 ∧ x .g11 = 0}
    exact (h .mm00).inter ((h .mm01).inter ((h .mm11).inter ((h .g00).inter
      ((h .g01).inter ((h .g10).inter (h .g11))))))
  · change IsClosed {x : MaterialCoordinates | x .g00 = 0 ∧ x .g01 = 0 ∧ x .g10 = 0 ∧ x .g11 = 0}
    exact (h .g00).inter ((h .g01).inter ((h .g10).inter (h .g11)))
  · exact isClosed_univ

@[expose] noncomputable def denominatorPower (cfg : Config) : MvPolynomial BICoord ℝ :=
  detRePoly cfg ^ 2 + detImPoly cfg ^ 2
theorem denominatorPower_eval (cfg : Config) (p : BIParams) :
    (denominatorPower cfg).eval (assign p) = (biDet cfg p).normSq := by
  simp only [denominatorPower, map_add, map_pow, detRePoly_eval, detImPoly_eval]
  simp only [Complex.normSq_apply]
  ring
theorem denominatorPower_ne_zero (cfg : Config) (x : MaterialCoordinates) :
    (denominatorPower cfg).eval x ≠ 0 := by
  have h := denominatorPower_eval cfg (parameters x)
  rw [assign_parameters] at h
  rw [h]
  exact fun hz => biDet_ne_zero cfg (parameters x) (Complex.normSq_eq_zero.mp hz)

@[expose] noncomputable def stateEfficiency (cfg : Config) (u : Vec2) (x : MaterialCoordinates) : ℝ :=
  (effPoly cfg u 0).eval x / (denominatorPower cfg).eval x
theorem stateEfficiency_continuous (cfg : Config) (u : Vec2) : Continuous (stateEfficiency cfg u) :=
  (MvPolynomial.continuous_eval _).div (MvPolynomial.continuous_eval _) (denominatorPower_ne_zero cfg)

theorem effPoly_zero_iff (cfg : Config) (u : Vec2) (x : MaterialCoordinates) (η : ℝ) :
    (effPoly cfg u η).eval x = 0 ↔ stateEfficiency cfg u x = η := by
  have h : (effPoly cfg u η).eval x =
      (effPoly cfg u 0).eval x - η * (denominatorPower cfg).eval x := by
    simp [effPoly, denominatorPower]
  rw [h]
  unfold stateEfficiency
  rw [div_eq_iff (denominatorPower_ne_zero cfg x)]
  exact sub_eq_zero

@[expose] noncomputable def efficiencyPair (cfg : Config) (u₁ u₂ : Vec2) (x : MaterialCoordinates) : ℝ × ℝ :=
  (stateEfficiency cfg u₁ x, stateEfficiency cfg u₂ x)
theorem efficiencyPair_continuous (cfg : Config) (u₁ u₂ : Vec2) : Continuous (efficiencyPair cfg u₁ u₂) :=
  (stateEfficiency_continuous cfg u₁).prodMk (stateEfficiency_continuous cfg u₂)

@[expose] noncomputable def collinearCoordinates (cfg : Config) (u v : Vec2) : Set MaterialCoordinates :=
  {x | (collinearityPoly cfg u v).re.eval x = 0 ∧ (collinearityPoly cfg u v).im.eval x = 0}
theorem collinearCoordinates_closed (cfg : Config) (u v : Vec2) : IsClosed (collinearCoordinates cfg u v) :=
  (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const).inter
    (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const)

@[expose] noncomputable def conversionMaterials (cfg : Config) (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    Set MaterialCoordinates :=
  (collinearCoordinates cfg u₁ v₁ ∩ collinearCoordinates cfg u₂ v₂) ∩
    (efficiencyPair cfg u₁ u₂) ⁻¹' {η}

theorem conversionMaterials_closed (cfg : Config) (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    IsClosed (conversionMaterials cfg u₁ u₂ v₁ v₂ η) :=
  ((collinearCoordinates_closed cfg u₁ v₁).inter
    (collinearCoordinates_closed cfg u₂ v₂)).inter
    (isClosed_singleton.preimage (efficiencyPair_continuous cfg u₁ u₂))

theorem conversionMaterials_iff_conversions (cfg : Config) (u₁ u₂ v₁ v₂ : Vec2)
    (η : ℝ × ℝ) (x : MaterialCoordinates)
    (hv₁ : isNormalizedJones v₁) (hv₂ : isNormalizedJones v₂) :
    x ∈ conversionMaterials cfg u₁ u₂ v₁ v₂ η ↔
      (∃ α₁ : ℂ, biForwardT cfg (parameters x) *ᵥ u₁ = α₁ • v₁ ∧ efficiency α₁ = η.1) ∧
      (∃ α₂ : ℂ, biForwardT cfg (parameters x) *ᵥ u₂ = α₂ • v₂ ∧ efficiency α₂ = η.2) := by
  rw [conversion_iff_amplitudeFree cfg (parameters x) u₁ v₁ η.1 hv₁,
    conversion_iff_amplitudeFree cfg (parameters x) u₂ v₂ η.2 hv₂,
    collinearityPoly_eq_zero_iff, collinearityPoly_eq_zero_iff]
  simp only [assign_parameters]
  rcases η with ⟨η₁, η₂⟩
  simp only [conversionMaterials, collinearCoordinates, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    efficiencyPair, Prod.mk.injEq, ← effPoly_zero_iff]
  tauto

end GSTC.Scattering.MaterialSpace
