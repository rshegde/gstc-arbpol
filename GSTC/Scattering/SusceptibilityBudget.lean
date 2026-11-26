/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIRotation
public import GSTC.Scattering.ClassPeakEfficiency
public import GSTC.Scattering.SpectralMatrixSupport

public section
set_option autoImplicit false

namespace GSTC.Scattering.SusceptibilityBudget
open BIPolynomials
open MaterialSpace ClassFeasibility ClassPeakEfficiency
open SpectralMatrixSupport
open scoped Matrix

@[expose] def electricBlock (x : MaterialCoordinates) : Mat :=
  !![x .ee00, x .ee01; x .ee01, x .ee11]
@[expose] def magneticBlock (x : MaterialCoordinates) : Mat :=
  !![x .mm00, x .mm01; x .mm01, x .mm11]
@[expose] def couplingBlock (x : MaterialCoordinates) : Mat :=
  !![x .g00, x .g01; x .g10, x .g11]

theorem electricBlock_symmetric (x : MaterialCoordinates) :
    (electricBlock x).transpose = electricBlock x := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
theorem magneticBlock_symmetric (x : MaterialCoordinates) :
    (magneticBlock x).transpose = magneticBlock x := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def spectralDirectCost (x : MaterialCoordinates) : ℝ :=
  max (opNorm (electricBlock x)) (opNorm (magneticBlock x))
@[expose] noncomputable def spectralCouplingCost (x : MaterialCoordinates) : ℝ :=
  opNorm (couplingBlock x)
@[expose] noncomputable def spectralCost (x : MaterialCoordinates) : ℝ :=
  max (spectralDirectCost x) (spectralCouplingCost x)
@[expose] noncomputable def spectralDirectBudget (cfg : Config) (x : MaterialCoordinates) : ℝ :=
  freeSpaceK0 cfg * spectralDirectCost x
@[expose] noncomputable def spectralCouplingBudget (cfg : Config) (x : MaterialCoordinates) : ℝ :=
  freeSpaceK0 cfg * spectralCouplingCost x
@[expose] noncomputable def spectralTotalBudget (cfg : Config) (x : MaterialCoordinates) : ℝ :=
  max (spectralDirectBudget cfg x) (spectralCouplingBudget cfg x)

theorem electricBlock_continuous : Continuous electricBlock := by
  unfold electricBlock; fun_prop
theorem magneticBlock_continuous : Continuous magneticBlock := by
  unfold magneticBlock; fun_prop
theorem couplingBlock_continuous : Continuous couplingBlock := by
  unfold couplingBlock; fun_prop
theorem spectralDirectCost_continuous : Continuous spectralDirectCost :=
  (continuous_opNorm.comp electricBlock_continuous).max
    (continuous_opNorm.comp magneticBlock_continuous)
theorem spectralCouplingCost_continuous : Continuous spectralCouplingCost :=
  continuous_opNorm.comp couplingBlock_continuous

theorem spectralDirectBudget_continuous (cfg : Config) : Continuous (spectralDirectBudget cfg) :=
  continuous_const.mul spectralDirectCost_continuous
theorem spectralCouplingBudget_continuous (cfg : Config) : Continuous (spectralCouplingBudget cfg) :=
  continuous_const.mul spectralCouplingCost_continuous
theorem spectralTotalBudget_continuous (cfg : Config) : Continuous (spectralTotalBudget cfg) :=
  (spectralDirectBudget_continuous cfg).max (spectralCouplingBudget_continuous cfg)

theorem spectralDirectCost_nonneg (x : MaterialCoordinates) : 0 ≤ spectralDirectCost x :=
  le_max_of_le_left (opNorm_nonneg _)

theorem spectralDirectBudget_nonneg (cfg : Config) (x : MaterialCoordinates) :
    0 ≤ spectralDirectBudget cfg x :=
  mul_nonneg (freeSpaceK0_nonneg cfg) (spectralDirectCost_nonneg x)

theorem spectralTotalBudget_nonneg (cfg : Config) (x : MaterialCoordinates) :
    0 ≤ spectralTotalBudget cfg x := le_max_of_le_left (spectralDirectBudget_nonneg cfg x)

theorem spectralTotalBudget_eq (cfg : Config) (x : MaterialCoordinates) :
    spectralTotalBudget cfg x = freeSpaceK0 cfg * spectralCost x := by
  exact (mul_max_of_nonneg (spectralDirectCost x) (spectralCouplingCost x)
    (freeSpaceK0_nonneg cfg)).symm

theorem coordinate_le_spectralCost (x : MaterialCoordinates) (k : BICoord) :
    |x k| ≤ spectralCost x := by
  have ha (i j : Fin 2) : |electricBlock x i j| ≤ spectralCost x :=
    (entry_le_opNorm _ i j).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hd (i j : Fin 2) : |magneticBlock x i j| ≤ spectralCost x :=
    (entry_le_opNorm _ i j).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hg (i j : Fin 2) : |couplingBlock x i j| ≤ spectralCost x :=
    (entry_le_opNorm _ i j).trans (le_max_right _ _)
  cases k
  · exact ha 0 0
  · exact ha 0 1
  · exact ha 1 1
  · exact hd 0 0
  · exact hd 0 1
  · exact hd 1 1
  · exact hg 0 0
  · exact hg 0 1
  · exact hg 1 0
  · exact hg 1 1

theorem coordinate_bound (cfg : Config) (hk : 0 < freeSpaceK0 cfg)
    (x : MaterialCoordinates) (β : ℝ) (hβ : spectralTotalBudget cfg x ≤ β) (k : BICoord) :
    |x k| ≤ β / freeSpaceK0 cfg := by
  apply (le_div_iff₀ hk).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (coordinate_le_spectralCost x k) hk.le).trans
    ((spectralTotalBudget_eq cfg x) ▸ hβ)

theorem spectralSublevel_compact (cfg : Config) (hk : 0 < freeSpaceK0 cfg) (β : ℝ) :
    IsCompact {x : MaterialCoordinates | spectralTotalBudget cfg x ≤ β} := by
  have hbox : IsCompact {x : MaterialCoordinates | ∀ k, x k ∈
      Set.Icc (-(β / freeSpaceK0 cfg)) (β / freeSpaceK0 cfg)} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_le (spectralTotalBudget_continuous cfg) continuous_const)
  intro x hx k
  exact abs_le.mp (coordinate_bound cfg hk x β hx k)

@[expose] def coordinatesOfBlocks (A D G : Mat) : MaterialCoordinates
  | .ee00 => A 0 0 | .ee01 => A 0 1 | .ee11 => A 1 1
  | .mm00 => D 0 0 | .mm01 => D 0 1 | .mm11 => D 1 1
  | .g00 => G 0 0 | .g01 => G 0 1 | .g10 => G 1 0 | .g11 => G 1 1

theorem blocks_coordinatesOfBlocks (A D G : Mat)
    (hA : A.transpose = A) (hD : D.transpose = D) :
    electricBlock (coordinatesOfBlocks A D G) = A ∧
    magneticBlock (coordinatesOfBlocks A D G) = D ∧
    couplingBlock (coordinatesOfBlocks A D G) = G := by
  have ha : A 1 0 = A 0 1 := congrArg (fun M : Mat => M 0 1) hA
  have hd : D 1 0 = D 0 1 := congrArg (fun M : Mat => M 0 1) hD
  refine ⟨?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [electricBlock, magneticBlock, couplingBlock, coordinatesOfBlocks, ha, hd]

theorem symmetric_conjugation (Q M : Mat) (hM : M.transpose = M) :
    (Q * M * Q.transpose).transpose = Q * M * Q.transpose := by
  simp [Matrix.transpose_mul, hM, Matrix.mul_assoc]

@[expose] def conjugateCoordinates (Q : Mat) (x : MaterialCoordinates) : MaterialCoordinates :=
  coordinatesOfBlocks (Q * electricBlock x * Q.transpose)
    (Q * magneticBlock x * Q.transpose) (Q * couplingBlock x * Q.transpose)

theorem blocks_conjugateCoordinates (Q : Mat) (x : MaterialCoordinates) :
    electricBlock (conjugateCoordinates Q x) = Q * electricBlock x * Q.transpose ∧
    magneticBlock (conjugateCoordinates Q x) = Q * magneticBlock x * Q.transpose ∧
    couplingBlock (conjugateCoordinates Q x) = Q * couplingBlock x * Q.transpose :=
  blocks_coordinatesOfBlocks _ _ _
    (symmetric_conjugation Q _ (electricBlock_symmetric x))
    (symmetric_conjugation Q _ (magneticBlock_symmetric x))

theorem spectralCosts_conjugate (Q : Mat) (hQ : Q.transpose * Q = 1) (x : MaterialCoordinates) :
    spectralDirectCost (conjugateCoordinates Q x) = spectralDirectCost x ∧
    spectralCouplingCost (conjugateCoordinates Q x) = spectralCouplingCost x ∧
    spectralCost (conjugateCoordinates Q x) = spectralCost x := by
  have hh := blocks_conjugateCoordinates Q x
  have hd : spectralDirectCost (conjugateCoordinates Q x) = spectralDirectCost x := by
    simp only [spectralDirectCost, hh.1, hh.2.1, opNorm_orthogonal_conjugation _ Q hQ]
  have hg : spectralCouplingCost (conjugateCoordinates Q x) = spectralCouplingCost x := by
    simp only [spectralCouplingCost, hh.2.2, opNorm_orthogonal_conjugation _ Q hQ]
  exact ⟨hd,hg,by simp only [spectralCost, hd, hg]⟩

theorem spectralBudgets_conjugate (cfg : Config) (Q : Mat)
    (hQ : Q.transpose * Q = 1) (x : MaterialCoordinates) :
    spectralDirectBudget cfg (conjugateCoordinates Q x) = spectralDirectBudget cfg x ∧
    spectralCouplingBudget cfg (conjugateCoordinates Q x) = spectralCouplingBudget cfg x ∧
    spectralTotalBudget cfg (conjugateCoordinates Q x) = spectralTotalBudget cfg x := by
  have hh := spectralCosts_conjugate Q hQ x
  simp only [spectralDirectBudget, spectralCouplingBudget, spectralTotalBudget_eq,
    hh.1, hh.2.1, hh.2.2, and_self]

@[expose] def polynomialCap (M : Mat) (β : ℝ) : Prop :=
  0 ≤ β^2 - ((M 0 0)^2 + (M 1 0)^2) ∧
  0 ≤ β^2 - ((M 0 1)^2 + (M 1 1)^2) ∧
  0 ≤ (β^2 - ((M 0 0)^2 + (M 1 0)^2)) *
      (β^2 - ((M 0 1)^2 + (M 1 1)^2)) -
      (M 0 0 * M 0 1 + M 1 0 * M 1 1)^2

theorem scaled_opNorm_le_iff (M : Mat) (k β : ℝ) (hk : 0 ≤ k) (hβ : 0 ≤ β) :
    k * opNorm M ≤ β ↔ polynomialCap (k • M) β :=
  (scaled_opNorm_cap M k β hk).trans (opNorm_le_iff_polynomial (k • M) β hβ)

theorem spectralDirectBudget_cap (cfg : Config) (hk : 0 < freeSpaceK0 cfg)
    (x : MaterialCoordinates) (β : ℝ) (hβ : 0 ≤ β) :
    spectralDirectBudget cfg x ≤ β ↔
      polynomialCap (freeSpaceK0 cfg • electricBlock x) β ∧
      polynomialCap (freeSpaceK0 cfg • magneticBlock x) β := by
  unfold spectralDirectBudget spectralDirectCost
  rw [mul_max_of_nonneg _ _ hk.le, max_le_iff]
  exact and_congr (scaled_opNorm_le_iff _ _ _ hk.le hβ)
    (scaled_opNorm_le_iff _ _ _ hk.le hβ)

theorem spectralCouplingBudget_cap (cfg : Config) (hk : 0 < freeSpaceK0 cfg)
    (x : MaterialCoordinates) (β : ℝ) (hβ : 0 ≤ β) :
    spectralCouplingBudget cfg x ≤ β ↔
      polynomialCap (freeSpaceK0 cfg • couplingBlock x) β :=
  scaled_opNorm_le_iff _ _ _ hk.le hβ

theorem spectralSeparateBudgets_cap (cfg : Config) (hk : 0 < freeSpaceK0 cfg)
    (x : MaterialCoordinates) (βd βc : ℝ) (hd : 0 ≤ βd) (hc : 0 ≤ βc) :
    (spectralDirectBudget cfg x ≤ βd ∧ spectralCouplingBudget cfg x ≤ βc) ↔
      polynomialCap (freeSpaceK0 cfg • electricBlock x) βd ∧
      polynomialCap (freeSpaceK0 cfg • magneticBlock x) βd ∧
      polynomialCap (freeSpaceK0 cfg • couplingBlock x) βc := by
  rw [spectralDirectBudget_cap cfg hk x βd hd,
    spectralCouplingBudget_cap cfg hk x βc hc, and_assoc]

@[expose] noncomputable def realRotation (γ : ℝ) : Mat :=
  !![Real.cos γ, -Real.sin γ; Real.sin γ, Real.cos γ]

theorem realRotation_orthogonal (γ : ℝ) :
    (realRotation γ).transpose * realRotation γ = 1 ∧
    realRotation γ * (realRotation γ).transpose = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [realRotation, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq γ]

@[expose] noncomputable def complexify (M : Mat) : Ten2 := M.map (algebraMap ℝ ℂ)

theorem complexify_injective : Function.Injective complexify := by
  intro M N h
  ext i j
  exact Complex.ofReal_injective (congrArg (fun A : Ten2 => A i j) h)

theorem complexify_mul (M N : Mat) : complexify (M*N) = complexify M * complexify N :=
  Matrix.map_mul
theorem complexify_transpose (M : Mat) : complexify M.transpose = (complexify M).transpose := rfl

theorem complexify_blocks (p : BIParams) :
    complexify (electricBlock (assign p)) = p.eeBlock ∧
    complexify (magneticBlock (assign p)) = p.mmBlock ∧
    complexify (couplingBlock (assign p)) = BIRotation.gBlock p := by
  refine ⟨?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;> rfl

theorem complexify_realRotation (γ : ℝ) : complexify (realRotation γ) = TransverseRotation.rotation γ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [complexify, realRotation, TransverseRotation.rotation]

theorem coordinates_ext (x y : MaterialCoordinates)
    (hA : electricBlock x = electricBlock y)
    (hD : magneticBlock x = magneticBlock y)
    (hG : couplingBlock x = couplingBlock y) : x = y := by
  have ha (i j : Fin 2) := congrArg (fun M : Mat => M i j) hA
  have hd (i j : Fin 2) := congrArg (fun M : Mat => M i j) hD
  have hg (i j : Fin 2) := congrArg (fun M : Mat => M i j) hG
  funext k
  cases k
  · exact ha 0 0
  · exact ha 0 1
  · exact ha 1 1
  · exact hd 0 0
  · exact hd 0 1
  · exact hd 1 1
  · exact hg 0 0
  · exact hg 0 1
  · exact hg 1 0
  · exact hg 1 1

theorem rotateParams_eq_conjugate (γ : ℝ) (p : BIParams) :
    assign (BIRotation.rotateParams γ p) =
      conjugateCoordinates (realRotation γ).transpose (assign p) := by
  have hb := blocks_conjugateCoordinates (realRotation γ).transpose (assign p)
  apply coordinates_ext
  · rw [hb.1]
    apply complexify_injective
    rw [(complexify_blocks _).1, complexify_mul, complexify_mul,
      complexify_transpose, Matrix.transpose_transpose, complexify_realRotation,
      (complexify_blocks _).1]
    exact BIRotation.rotateParams_eeBlock γ p
  · rw [hb.2.1]
    apply complexify_injective
    rw [(complexify_blocks _).2.1, complexify_mul, complexify_mul,
      complexify_transpose, Matrix.transpose_transpose, complexify_realRotation,
      (complexify_blocks _).2.1]
    exact BIRotation.rotateParams_mmBlock γ p
  · rw [hb.2.2]
    apply complexify_injective
    rw [(complexify_blocks _).2.2, complexify_mul, complexify_mul,
      complexify_transpose, Matrix.transpose_transpose, complexify_realRotation,
      (complexify_blocks _).2.2]
    exact BIRotation.rotateParams_gBlock γ p

theorem spectralBudgets_rotateParams (cfg : Config) (γ : ℝ) (p : BIParams) :
    spectralDirectBudget cfg (assign (BIRotation.rotateParams γ p)) =
      spectralDirectBudget cfg (assign p) ∧
    spectralCouplingBudget cfg (assign (BIRotation.rotateParams γ p)) =
      spectralCouplingBudget cfg (assign p) ∧
    spectralTotalBudget cfg (assign (BIRotation.rotateParams γ p)) =
      spectralTotalBudget cfg (assign p) := by
  rw [rotateParams_eq_conjugate]
  apply spectralBudgets_conjugate
  simpa using (realRotation_orthogonal γ).2

theorem spectralSeparateSublevel_compact (cfg : Config) (hk : 0 < freeSpaceK0 cfg) (βd βc : ℝ) :
    IsCompact {x : MaterialCoordinates |
      spectralDirectBudget cfg x ≤ βd ∧ spectralCouplingBudget cfg x ≤ βc} := by
  apply (spectralSublevel_compact cfg hk (max βd βc)).of_isClosed_subset
    ((isClosed_le (spectralDirectBudget_continuous cfg) continuous_const).inter
      (isClosed_le (spectralCouplingBudget_continuous cfg) continuous_const))
  intro x hx
  exact max_le (hx.1.trans (le_max_left _ _)) (hx.2.trans (le_max_right _ _))

theorem spectralBudget_minOn_closed (cfg : Config) (hk : 0 < freeSpaceK0 cfg)
    (S : Set MaterialCoordinates) (hS : IsClosed S) (hne : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, spectralTotalBudget cfg x ≤ spectralTotalBudget cfg y := by
  obtain ⟨x₀,hx₀⟩ := hne
  have hc := (spectralSublevel_compact cfg hk (spectralTotalBudget cfg x₀)).inter_right hS
  have hne' : ({x | spectralTotalBudget cfg x ≤ spectralTotalBudget cfg x₀} ∩ S).Nonempty :=
    ⟨x₀, (show spectralTotalBudget cfg x₀ ≤ spectralTotalBudget cfg x₀ from le_rfl), hx₀⟩
  obtain ⟨x,hx,hmin⟩ := hc.exists_isMinOn hne'
    (spectralTotalBudget_continuous cfg).continuousOn
  refine ⟨x,hx.2,?_⟩
  intro y hy
  by_cases hb : spectralTotalBudget cfg y ≤ spectralTotalBudget cfg x₀
  · exact hmin ⟨hb,hy⟩
  · exact hx.1.trans (le_of_lt (lt_of_not_ge hb))

theorem blocks_smul (c : ℝ) (x : MaterialCoordinates) :
    electricBlock (c • x) = c • electricBlock x ∧
    magneticBlock (c • x) = c • magneticBlock x ∧
    couplingBlock (c • x) = c • couplingBlock x := by
  refine ⟨?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;> rfl

theorem spectralCosts_smul (c : ℝ) (hc : 0 ≤ c) (x : MaterialCoordinates) :
    spectralDirectCost (c • x) = c * spectralDirectCost x ∧
    spectralCouplingCost (c • x) = c * spectralCouplingCost x ∧
    spectralCost (c • x) = c * spectralCost x := by
  have hd : spectralDirectCost (c • x) = c * spectralDirectCost x := by
    simp only [spectralDirectCost, (blocks_smul c x).1, (blocks_smul c x).2.1,
      opNorm_smul, abs_of_nonneg hc]
    exact (mul_max_of_nonneg _ _ hc).symm
  have hg : spectralCouplingCost (c • x) = c * spectralCouplingCost x := by
    simp only [spectralCouplingCost, (blocks_smul c x).2.2, opNorm_smul, abs_of_nonneg hc]
  refine ⟨hd,hg,?_⟩
  simp only [spectralCost, hd, hg]
  exact (mul_max_of_nonneg _ _ hc).symm

theorem spectralBudgets_smul (cfg : Config) (c : ℝ) (hc : 0 ≤ c) (x : MaterialCoordinates) :
    spectralDirectBudget cfg (c • x) = c * spectralDirectBudget cfg x ∧
    spectralCouplingBudget cfg (c • x) = c * spectralCouplingBudget cfg x ∧
    spectralTotalBudget cfg (c • x) = c * spectralTotalBudget cfg x := by
  have hh := spectralCosts_smul c hc x
  simp only [spectralDirectBudget, spectralCouplingBudget, spectralTotalBudget_eq,
    hh.1, hh.2.1, hh.2.2]
  constructor
  · ring
  constructor <;> ring

theorem spectralTotalBudget_eq_zero_iff (cfg : Config) (hk : 0 < freeSpaceK0 cfg)
    (x : MaterialCoordinates) : spectralTotalBudget cfg x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext k
    have hh := coordinate_bound cfg hk x 0 h.le k
    simpa using abs_eq_zero.mp (le_antisymm (by simpa using hh) (abs_nonneg _))
  · rintro rfl
    have hh := (spectralBudgets_smul cfg 0 (by norm_num) (0 : MaterialCoordinates)).2.2
    simpa using hh

end GSTC.Scattering.SusceptibilityBudget
