/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.SusceptibilityBudgetPolynomials

public section
set_option autoImplicit false

namespace GSTC.Scattering.ClassMinimumBudget
open BIFeasibility BIPolynomials BIAmplitudeFree  SusceptibilityBudget
open MaterialSpace ClassFeasibility ClassPeakEfficiency
open SusceptibilityBudgetPolynomials
open Classical

@[expose] noncomputable def budgetValues (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) : Set ℝ :=
  spectralTotalBudget cfg '' classMaterials cfg c u₁ u₂ v₁ v₂ η

@[expose] noncomputable def finiteMinimumBudget (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) : ℝ :=
  sInf (budgetValues cfg c u₁ u₂ v₁ v₂ η)

@[expose] noncomputable def minimumBudget (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) : WithTop ℝ :=
  if (classMaterials cfg c u₁ u₂ v₁ v₂ η).Nonempty then
    (finiteMinimumBudget cfg c u₁ u₂ v₁ v₂ η : WithTop ℝ)
  else ⊤

@[expose] noncomputable def capFeasible (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) (β : ℝ) : Prop :=
  ∃ x ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η, spectralTotalBudget cfg x ≤ β

@[expose] noncomputable def feasibleCaps (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) : Set ℝ :=
  {β | capFeasible cfg c u₁ u₂ v₁ v₂ η β}

theorem budgetValues_bddBelow (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    BddBelow (budgetValues cfg c u₁ u₂ v₁ v₂ η) :=
  ⟨0, by rintro _ ⟨x,_,rfl⟩; exact spectralTotalBudget_nonneg cfg x⟩

theorem minimumBudget_eq_top_iff (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    minimumBudget cfg c u₁ u₂ v₁ v₂ η = ⊤ ↔
      ¬ (classMaterials cfg c u₁ u₂ v₁ v₂ η).Nonempty := by
  simp only [minimumBudget]
  split <;> simp_all

theorem minimizer_exists (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hne : (classMaterials cfg c u₁ u₂ v₁ v₂ η).Nonempty) :
    ∃ x ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η,
      ∀ y ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η,
        spectralTotalBudget cfg x ≤ spectralTotalBudget cfg y :=
  spectralBudget_minOn_closed cfg (freeSpaceK0_pos cfg) _
    (classMaterials_closed cfg c u₁ u₂ v₁ v₂ η) hne

theorem finiteMinimumBudget_eq_of_minimizer (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) (x : MaterialCoordinates)
    (hx : x ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η)
    (hmin : ∀ y ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η,
      spectralTotalBudget cfg x ≤ spectralTotalBudget cfg y) :
    finiteMinimumBudget cfg c u₁ u₂ v₁ v₂ η = spectralTotalBudget cfg x := by
  apply le_antisymm
  · exact csInf_le (budgetValues_bddBelow cfg c u₁ u₂ v₁ v₂ η) ⟨x,hx,rfl⟩
  · apply le_csInf (show (budgetValues cfg c u₁ u₂ v₁ v₂ η).Nonempty from
      ⟨_,x,hx,rfl⟩)
    rintro _ ⟨y,hy,rfl⟩
    exact hmin y hy

theorem minimumBudget_attained (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hne : (classMaterials cfg c u₁ u₂ v₁ v₂ η).Nonempty) :
    ∃ x ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η,
      minimumBudget cfg c u₁ u₂ v₁ v₂ η = (spectralTotalBudget cfg x : WithTop ℝ) ∧
      ∀ y ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η,
        spectralTotalBudget cfg x ≤ spectralTotalBudget cfg y := by
  obtain ⟨x,hx,hm⟩ := minimizer_exists cfg c u₁ u₂ v₁ v₂ η hne
  refine ⟨x,hx,?_,hm⟩
  rw [minimumBudget, ite_eq_left hne, finiteMinimumBudget_eq_of_minimizer cfg c u₁ u₂ v₁ v₂ η x hx hm]

theorem minimumBudget_le_of_mem (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) (x : MaterialCoordinates)
    (hx : x ∈ classMaterials cfg c u₁ u₂ v₁ v₂ η) :
    minimumBudget cfg c u₁ u₂ v₁ v₂ η ≤ (spectralTotalBudget cfg x : WithTop ℝ) := by
  rw [minimumBudget, ite_eq_left (show (classMaterials cfg c u₁ u₂ v₁ v₂ η).Nonempty from ⟨x,hx⟩)]
  apply WithTop.coe_le_coe.mpr
  exact csInf_le (budgetValues_bddBelow cfg c u₁ u₂ v₁ v₂ η) ⟨x,hx,rfl⟩

theorem capFeasible_mono (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) {β β' : ℝ} (hβ : β ≤ β')
    (h : capFeasible cfg c u₁ u₂ v₁ v₂ η β) :
    capFeasible cfg c u₁ u₂ v₁ v₂ η β' := by
  obtain ⟨x,hx,hb⟩ := h
  exact ⟨x,hx,hb.trans hβ⟩

theorem capFeasible_iff_minimumBudget_le (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) (β : ℝ) :
    capFeasible cfg c u₁ u₂ v₁ v₂ η β ↔ minimumBudget cfg c u₁ u₂ v₁ v₂ η ≤ (β : WithTop ℝ) := by
  constructor
  · rintro ⟨x,hx,hb⟩
    exact (minimumBudget_le_of_mem cfg c u₁ u₂ v₁ v₂ η x hx).trans (WithTop.coe_le_coe.mpr hb)
  · intro h
    by_cases hne : (classMaterials cfg c u₁ u₂ v₁ v₂ η).Nonempty
    · obtain ⟨x,hx,hm,_⟩ := minimumBudget_attained cfg c u₁ u₂ v₁ v₂ η hne
      rw [hm] at h
      exact ⟨x,hx,WithTop.coe_le_coe.mp h⟩
    · simp [minimumBudget, hne] at h

theorem feasibleCaps_eq_Ici (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hne : (classMaterials cfg c u₁ u₂ v₁ v₂ η).Nonempty) :
    feasibleCaps cfg c u₁ u₂ v₁ v₂ η = Set.Ici (finiteMinimumBudget cfg c u₁ u₂ v₁ v₂ η) := by
  ext β
  change capFeasible cfg c u₁ u₂ v₁ v₂ η β ↔ _
  rw [capFeasible_iff_minimumBudget_le, minimumBudget, ite_eq_left hne]
  exact WithTop.coe_le_coe

theorem feasibleCaps_eq_empty (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ)
    (hne : ¬ (classMaterials cfg c u₁ u₂ v₁ v₂ η).Nonempty) :
    feasibleCaps cfg c u₁ u₂ v₁ v₂ η = ∅ := by
  ext β
  simp only [feasibleCaps, Set.mem_ofPred_eq, capFeasible_iff_minimumBudget_le,
    minimumBudget, ite_eq_right hne]
  simp

theorem feasibleCaps_closed (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    IsClosed (feasibleCaps cfg c u₁ u₂ v₁ v₂ η) := by
  by_cases hne : (classMaterials cfg c u₁ u₂ v₁ v₂ η).Nonempty
  · rw [feasibleCaps_eq_Ici cfg c u₁ u₂ v₁ v₂ η hne]
    exact isClosed_Ici
  · rw [feasibleCaps_eq_empty cfg c u₁ u₂ v₁ v₂ η hne]
    exact isClosed_empty

theorem minimumBudget_BI_le_NB (cfg : Config) (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) :
    minimumBudget cfg .BI u₁ u₂ v₁ v₂ η ≤ minimumBudget cfg .NB u₁ u₂ v₁ v₂ η := by
  by_cases hne : (classMaterials cfg .NB u₁ u₂ v₁ v₂ η).Nonempty
  · obtain ⟨x,hx,hm,_⟩ := minimumBudget_attained cfg .NB u₁ u₂ v₁ v₂ η hne
    rw [hm]
    exact minimumBudget_le_of_mem cfg .BI u₁ u₂ v₁ v₂ η x
      (classMaterials_NB_subset_BI cfg u₁ u₂ v₁ v₂ η hx)
  · rw [(minimumBudget_eq_top_iff cfg .NB u₁ u₂ v₁ v₂ η).mpr hne]
    exact le_top

theorem capFeasible_polynomial (cfg : Config) (c : SheetClass)
    (u₁ u₂ v₁ v₂ : Vec2) (η : ℝ × ℝ) (β : ℝ) (hβ : 0 ≤ β) :
    capFeasible cfg c u₁ u₂ v₁ v₂ η β ↔ ∃ x : MaterialCoordinates,
      InClass c (parameters x) ∧
      (collinearityPoly cfg u₁ v₁).re.eval x = 0 ∧
      (collinearityPoly cfg u₁ v₁).im.eval x = 0 ∧
      (collinearityPoly cfg u₂ v₂).re.eval x = 0 ∧
      (collinearityPoly cfg u₂ v₂).im.eval x = 0 ∧
      (effPoly cfg u₁ η.1).eval x = 0 ∧ (effPoly cfg u₂ η.2).eval x = 0 ∧
      (∀ i, 0 ≤ (capPolys ((MvPolynomial.C (freeSpaceK0 cfg) : Poly) • electricPolys) β i).eval x) ∧
      (∀ i, 0 ≤ (capPolys ((MvPolynomial.C (freeSpaceK0 cfg) : Poly) • magneticPolys) β i).eval x) ∧
      (∀ i, 0 ≤ (capPolys ((MvPolynomial.C (freeSpaceK0 cfg) : Poly) • couplingPolys) β i).eval x) := by
  rcases η with ⟨η₁,η₂⟩
  simp only [capFeasible, mem_classMaterials_iff, conversionMaterials,
    collinearCoordinates, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
    Set.mem_singleton_iff, efficiencyPair, Prod.mk.injEq, ← effPoly_zero_iff,
    spectralTotalBudget_polynomial cfg (freeSpaceK0_pos cfg) _ β hβ]
  apply exists_congr
  intro x
  tauto

end GSTC.Scattering.ClassMinimumBudget
