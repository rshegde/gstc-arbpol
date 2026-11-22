/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.SusceptibilityBudget

public section
set_option autoImplicit false

namespace GSTC.Scattering.SusceptibilityBudgetPolynomials
open BIPolynomials   SusceptibilityBudget
open MaterialSpace ClassFeasibility ClassPeakEfficiency
open scoped Matrix

abbrev Poly := MvPolynomial BICoord ℝ
abbrev PolyMatrix := Matrix (Fin 2) (Fin 2) Poly

@[expose] noncomputable def electricPolys : PolyMatrix :=
  !![MvPolynomial.X .ee00, MvPolynomial.X .ee01;
     MvPolynomial.X .ee01, MvPolynomial.X .ee11]
@[expose] noncomputable def magneticPolys : PolyMatrix :=
  !![MvPolynomial.X .mm00, MvPolynomial.X .mm01;
     MvPolynomial.X .mm01, MvPolynomial.X .mm11]
@[expose] noncomputable def couplingPolys : PolyMatrix :=
  !![MvPolynomial.X .g00, MvPolynomial.X .g01;
     MvPolynomial.X .g10, MvPolynomial.X .g11]

@[expose] noncomputable def capPolys (M : PolyMatrix) (β : ℝ) : Fin 3 → Poly :=
  let a := MvPolynomial.C (β^2) - ((M 0 0)^2 + (M 1 0)^2)
  let d := MvPolynomial.C (β^2) - ((M 0 1)^2 + (M 1 1)^2)
  let b := M 0 0 * M 0 1 + M 1 0 * M 1 1
  ![a, d, a*d-b^2]

theorem eval_capPolys (M : PolyMatrix) (β : ℝ) (x : MaterialCoordinates) :
    (∀ i, 0 ≤ (capPolys M β i).eval x) ↔
      polynomialCap (M.map (MvPolynomial.eval x)) β := by
  simp [capPolys, polynomialCap, Fin.forall_fin_succ]

theorem eval_scaled_blocks (k : ℝ) (x : MaterialCoordinates) :
    (((MvPolynomial.C k : Poly) • electricPolys).map (MvPolynomial.eval x)) = k • electricBlock x ∧
    (((MvPolynomial.C k : Poly) • magneticPolys).map (MvPolynomial.eval x)) = k • magneticBlock x ∧
    (((MvPolynomial.C k : Poly) • couplingPolys).map (MvPolynomial.eval x)) = k • couplingBlock x := by
  refine ⟨?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [electricPolys, magneticPolys, couplingPolys, electricBlock, magneticBlock,
      couplingBlock, smul_eq_mul]

theorem spectralSeparateBudgets_polynomial (cfg : Config) (hk : 0 < freeSpaceK0 cfg)
    (x : MaterialCoordinates) (βd βc : ℝ) (hd : 0 ≤ βd) (hc : 0 ≤ βc) :
    (spectralDirectBudget cfg x ≤ βd ∧ spectralCouplingBudget cfg x ≤ βc) ↔
      (∀ i, 0 ≤ (capPolys ((MvPolynomial.C (freeSpaceK0 cfg) : Poly) • electricPolys) βd i).eval x) ∧
      (∀ i, 0 ≤ (capPolys ((MvPolynomial.C (freeSpaceK0 cfg) : Poly) • magneticPolys) βd i).eval x) ∧
      (∀ i, 0 ≤ (capPolys ((MvPolynomial.C (freeSpaceK0 cfg) : Poly) • couplingPolys) βc i).eval x) := by
  rw [spectralSeparateBudgets_cap cfg hk x βd βc hd hc,
    eval_capPolys, eval_capPolys, eval_capPolys,
    (eval_scaled_blocks (freeSpaceK0 cfg) x).1,
    (eval_scaled_blocks (freeSpaceK0 cfg) x).2.1,
    (eval_scaled_blocks (freeSpaceK0 cfg) x).2.2]

theorem spectralTotalBudget_polynomial (cfg : Config) (hk : 0 < freeSpaceK0 cfg)
    (x : MaterialCoordinates) (β : ℝ) (hβ : 0 ≤ β) :
    spectralTotalBudget cfg x ≤ β ↔
      (∀ i, 0 ≤ (capPolys ((MvPolynomial.C (freeSpaceK0 cfg) : Poly) • electricPolys) β i).eval x) ∧
      (∀ i, 0 ≤ (capPolys ((MvPolynomial.C (freeSpaceK0 cfg) : Poly) • magneticPolys) β i).eval x) ∧
      (∀ i, 0 ≤ (capPolys ((MvPolynomial.C (freeSpaceK0 cfg) : Poly) • couplingPolys) β i).eval x) := by
  rw [spectralTotalBudget, max_le_iff]
  exact spectralSeparateBudgets_polynomial cfg hk x β β hβ hβ

end GSTC.Scattering.SusceptibilityBudgetPolynomials
