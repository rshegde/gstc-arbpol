/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.NBOutgoingUniqueness

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic.NoncommRing

public section
namespace GSTC.Scattering
open scoped Matrix

@[expose] noncomputable def nbCayley (E : Ten2) : Ten2 := (1 + E)⁻¹ * (1 - E)

@[expose] noncomputable def nbInvCayley (U : Ten2) : Ten2 := (1 - U) * (1 + U)⁻¹

theorem nb_mul_cancel_left (A B C : Ten2) (hA : A.det ≠ 0)
    (h : A * B = A * C) : B = C := by
  have hh := congrArg (fun M : Ten2 => A⁻¹ * M) h
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),
    Matrix.one_mul] using hh

theorem nb_mul_cancel_right (A B C : Ten2) (hA : A.det ≠ 0)
    (h : B * A = C * A) : B = C := by
  have hh := congrArg (fun M : Ten2 => M * A⁻¹) h
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
    Matrix.mul_one] using hh

theorem nb_commute_inv (A B : Ten2) (hB : B.det ≠ 0) (h : A * B = B * A) :
    A * B⁻¹ = B⁻¹ * A := by
  apply nb_mul_cancel_left B _ _ hB
  rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB), Matrix.mul_one,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB),
    Matrix.one_mul]

theorem nb_one_add_skew_det_ne_zero (E : Ten2) (hE : E.conjTranspose = -E) :
    (1 + E).det ≠ 0 := by
  have ha : ∀ i j, E i j = -star (E j i) := by
    intro i j
    have h := congrArg (fun M : Ten2 => M i j) hE
    change star (E j i) = -E i j at h
    linear_combination h
  have hinj : Function.Injective (fun w : Vec2 => (1 + E) *ᵥ w) := by
    intro w w' h
    apply add_antiHermitian_injective E ha
    simpa only [Matrix.add_mulVec, Matrix.one_mulVec] using h
  exact (isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det (1 + E)).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hinj)))

theorem nbCayley_equation (E : Ten2) (hE : (1 + E).det ≠ 0) :
    (1 + E) * nbCayley E = 1 - E := by
  exact Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr hE)

theorem nbCayley_commute (E : Ten2) (hE : (1 + E).det ≠ 0) :
    (1 - E) * (1 + E)⁻¹ = (1 + E)⁻¹ * (1 - E) :=
  nb_commute_inv (1 - E) (1 + E) hE (by noncomm_ring)

theorem nbCayley_symmetric (E : Ten2) (hS : E.transpose = E)
    (hE : (1 + E).det ≠ 0) : (nbCayley E).transpose = nbCayley E := by
  simp only [nbCayley, Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_nonsing_inv, Matrix.transpose_add, hS]
  exact nbCayley_commute E hE

theorem nbCayley_unitary (E : Ten2) (hE : E.conjTranspose = -E) :
    nbCayley E ∈ unitary Ten2 := by
  have hp := nb_one_add_skew_det_ne_zero E hE
  have hm : (1 - E).det ≠ 0 := by
    simpa only [sub_eq_add_neg] using nb_one_add_skew_det_ne_zero (-E) (by
      simp only [Matrix.conjTranspose_neg, hE, neg_neg])
  have hcomm : (1 + E) * (1 - E)⁻¹ = (1 - E)⁻¹ * (1 + E) :=
    nb_commute_inv (1 + E) (1 - E) hm (by noncomm_ring)
  rw [Unitary.mem_iff]
  change (nbCayley E).conjTranspose * nbCayley E = 1 ∧
    nbCayley E * (nbCayley E).conjTranspose = 1
  have hstar : (nbCayley E).conjTranspose = (1 + E) * (1 - E)⁻¹ := by
    simp only [nbCayley, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_add, hE, sub_neg_eq_add, ← sub_eq_add_neg]
  rw [hstar, nbCayley]
  constructor
  · rw [hcomm, Matrix.mul_assoc, ← Matrix.mul_assoc (1 + E),
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp), Matrix.one_mul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hm)]
  · have hc : (1 - E) * (1 + E) = (1 + E) * (1 - E) := by noncomm_ring
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (1 + E)⁻¹, hc,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hp),
      Matrix.one_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hm)]

theorem nbCayley_pole_free (E : Ten2) (hE : E.conjTranspose = -E) :
    (1 + nbCayley E).det ≠ 0 := by
  have hp := nb_one_add_skew_det_ne_zero E hE
  have heq : (1 + E) * (1 + nbCayley E) = (1 : Ten2) + 1 := by
    rw [Matrix.mul_add, Matrix.mul_one, nbCayley_equation E hp]
    noncomm_ring
  have hd := congrArg Matrix.det heq
  rw [Matrix.det_mul] at hd
  have htwo : ((1 : Ten2) + 1).det = 4 := by
    have hh : (1 : Ten2) + 1 = (2 : ℂ) • (1 : Ten2) := by rw [two_smul]
    rw [hh, Matrix.det_smul]
    norm_num
  rw [htwo] at hd
  intro hz
  rw [hz, mul_zero] at hd
  norm_num at hd

theorem nbInvCayley_equation (U : Ten2) (hp : (1 + U).det ≠ 0) :
    nbInvCayley U * (1 + U) = 1 - U := by
  exact Matrix.nonsing_inv_mul_cancel_right _ _ (isUnit_iff_ne_zero.mpr hp)

theorem nbInvCayley_symmetric (U : Ten2) (hS : U.transpose = U)
    (hp : (1 + U).det ≠ 0) : (nbInvCayley U).transpose = nbInvCayley U := by
  simp only [nbInvCayley, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, hS]
  exact (nbCayley_commute U hp).symm

theorem nbInvCayley_skew (U : Ten2) (hU : U ∈ unitary Ten2)
    (hp : (1 + U).det ≠ 0) :
    (nbInvCayley U).conjTranspose = -(nbInvCayley U) := by
  have hu : U.conjTranspose * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hU).1
  have hpstar : ((1 + U).conjTranspose).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.mpr hp
  have heq := nbInvCayley_equation U hp
  have hdag : (1 + U).conjTranspose * (nbInvCayley U).conjTranspose
      = (1 - U).conjTranspose := by
    rw [← Matrix.conjTranspose_mul, heq]
  have hz : (1 + U).conjTranspose *
      ((nbInvCayley U).conjTranspose + nbInvCayley U) * (1 + U) = 0 := by
    calc _ = ((1 + U).conjTranspose * (nbInvCayley U).conjTranspose) * (1 + U)
        + (1 + U).conjTranspose * (nbInvCayley U * (1 + U)) := by noncomm_ring
      _ = (1 - U).conjTranspose * (1 + U) + (1 + U).conjTranspose * (1 - U) := by
        rw [hdag, heq]
      _ = 2 * (1 - U.conjTranspose * U) := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
          Matrix.conjTranspose_one]
        noncomm_ring
      _ = 0 := by rw [hu]; noncomm_ring
  have hz' : ((nbInvCayley U).conjTranspose + nbInvCayley U) * (1 + U) = 0 := by
    apply nb_mul_cancel_left (1 + U).conjTranspose _ _ hpstar
    simpa only [Matrix.mul_assoc, Matrix.mul_zero] using hz
  have hz'' : (nbInvCayley U).conjTranspose + nbInvCayley U = 0 := by
    apply nb_mul_cancel_right (1 + U) _ _ hp
    simpa only [Matrix.zero_mul] using hz'
  exact eq_neg_of_add_eq_zero_left hz''

theorem nbCayley_nbInvCayley (U : Ten2) (hU : U ∈ unitary Ten2)
    (hp : (1 + U).det ≠ 0) : nbCayley (nbInvCayley U) = U := by
  let E := nbInvCayley U
  have hE := nbInvCayley_skew U hU hp
  have hden := nb_one_add_skew_det_ne_zero E hE
  have heq : E * (1 + U) = 1 - U := nbInvCayley_equation U hp
  have hpar : (1 + E) * U = 1 - E := by
    apply eq_sub_iff_add_eq.mpr
    calc (1 + E) * U + E = E * (1 + U) + U := by noncomm_ring
      _ = 1 := by rw [heq]; abel
  apply nb_mul_cancel_left (1 + E) _ _ hden
  rw [nbCayley_equation E hden, hpar]

theorem nbInvCayley_nbCayley (E : Ten2) (hE : E.conjTranspose = -E) :
    nbInvCayley (nbCayley E) = E := by
  have hp := nb_one_add_skew_det_ne_zero E hE
  have hcp := nbCayley_pole_free E hE
  have heq := nbCayley_equation E hp
  have hrel : E * (1 + nbCayley E) = 1 - nbCayley E := by
    apply eq_sub_iff_add_eq.mpr
    calc E * (1 + nbCayley E) + nbCayley E
        = (1 + E) * nbCayley E + E := by noncomm_ring
      _ = 1 := by rw [heq]; abel
  apply nb_mul_cancel_right (1 + nbCayley E) _ _ hcp
  rw [nbInvCayley_equation _ hcp, hrel]

@[expose] def PoleFreeSymmetricMidpoint (T : Ten2) : Prop :=
  ∃ X Y : Ten2, X.transpose = X ∧ Y.transpose = Y ∧
    X ∈ unitary Ten2 ∧ Y ∈ unitary Ten2 ∧
    (1 + X).det ≠ 0 ∧ (1 + Y).det ≠ 0 ∧ T = (1 / 2 : ℂ) • (X + Y)

theorem poleFreeSymmetricMidpoint_iff_responses (T : Ten2) :
    PoleFreeSymmetricMidpoint T ↔
      ∃ E F : Ten2, E.transpose = E ∧ F.transpose = F ∧
        E.conjTranspose = -E ∧ F.conjTranspose = -F ∧
        T = (1 / 2 : ℂ) • (nbCayley E + nbCayley F) := by
  constructor
  · rintro ⟨X, Y, hXS, hYS, hX, hY, hpX, hpY, hT⟩
    refine ⟨nbInvCayley X, nbInvCayley Y,
      nbInvCayley_symmetric X hXS hpX, nbInvCayley_symmetric Y hYS hpY,
      nbInvCayley_skew X hX hpX, nbInvCayley_skew Y hY hpY, ?_⟩
    rw [nbCayley_nbInvCayley X hX hpX, nbCayley_nbInvCayley Y hY hpY]
    exact hT
  · rintro ⟨E, F, hES, hFS, hE, hF, hT⟩
    exact ⟨nbCayley E, nbCayley F,
      nbCayley_symmetric E hES (nb_one_add_skew_det_ne_zero E hE),
      nbCayley_symmetric F hFS (nb_one_add_skew_det_ne_zero F hF),
      nbCayley_unitary E hE, nbCayley_unitary F hF,
      nbCayley_pole_free E hE, nbCayley_pole_free F hF, hT⟩

end GSTC.Scattering
