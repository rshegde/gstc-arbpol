/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.NBPoleExclusions

public section
namespace GSTC.Scattering
open scoped Matrix

@[expose] def diag2 (a b : ℂ) : Ten2 := !![a, 0; 0, b]

@[expose] def diagR (a b : ℝ) : Ten2 := !![(a : ℂ), 0; 0, (b : ℂ)]

structure Takagi2 (T : Ten2) where

  Q : Ten2

  hQ : Q ∈ unitary Ten2

  s1 : ℝ

  s2 : ℝ

  hs1 : 0 ≤ s1

  hs2 : 0 ≤ s2

  hs2le : s2 ≤ s1

  hT : T = Q * diagR s1 s2 * Q.transpose

theorem map_star_transpose (M : Ten2) :
    (M.map star).transpose = M.conjTranspose := by
  ext i j
  simp [Matrix.transpose_apply, Matrix.conjTranspose_apply, Matrix.map_apply]

theorem unitary_transpose_conj (Q : Ten2) (hQ : Q ∈ unitary Ten2) :
    Q.transpose * Q.map star = 1 := by
  have h1 : star Q * Q = 1 := (Unitary.mem_iff.mp hQ).1
  have hM : (Q.transpose * Q.map star).transpose = 1 := by
    rw [Matrix.transpose_mul, map_star_transpose, Matrix.transpose_transpose,
      ← Matrix.star_eq_conjTranspose]
    exact h1
  have hM' := congrArg (fun M : Ten2 => M.transpose) hM
  simpa using hM'

theorem unitary_conj_transpose (Q : Ten2) (hQ : Q ∈ unitary Ten2) :
    Q.map star * Q.transpose = 1 := by
  have h2 : Q * star Q = 1 := (Unitary.mem_iff.mp hQ).2
  have hM : (Q.map star * Q.transpose).transpose = 1 := by
    rw [Matrix.transpose_mul, map_star_transpose, Matrix.transpose_transpose,
      ← Matrix.star_eq_conjTranspose]
    exact h2
  have hM' := congrArg (fun M : Ten2 => M.transpose) hM
  simpa using hM'

theorem conjTranspose_eq_map_star_of_symmetric {M : Ten2} (h : M.transpose = M) :
    M.conjTranspose = M.map star := by
  have hM : M.transpose.conjTranspose = M.map star := Matrix.transpose_conjTranspose M
  rw [h] at hM
  exact hM

theorem unitary_congruence {Q W : Ten2} (hQ : Q ∈ unitary Ten2)
    (hW : W.transpose = W) (hWW : star W * W = 1) :
    Q * W * Q.transpose ∈ unitary Ten2 ∧ (Q * W * Q.transpose).transpose = Q * W * Q.transpose := by
  have hstar : star (Q * W * Q.transpose)
      = Q.map star * star W * star Q := by
    simp only [star_mul, Matrix.star_eq_conjTranspose,
      Matrix.transpose_conjTranspose, Matrix.mul_assoc]
  have hWS : W * star W = 1 := by
    exact (mul_eq_one_comm).mp hWW
  constructor
  · rw [Unitary.mem_iff, hstar]
    have hQQ : star Q * Q = 1 := (Unitary.mem_iff.mp hQ).1
    have hQQ' : Q * star Q = 1 := (Unitary.mem_iff.mp hQ).2
    have hWQ : Q.map star * Q.transpose = 1 := unitary_conj_transpose Q hQ
    have hTQ : Q.transpose * Q.map star = 1 := unitary_transpose_conj Q hQ
    constructor
    · calc
        _ = Q.map star * (star W * (star Q * Q) * W) * Q.transpose := by
          simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hQQ, Matrix.mul_one, hWW, Matrix.mul_one, hWQ]
    · calc
        _ = Q * (W * (Q.transpose * Q.map star) * star W) * star Q := by
          simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hTQ, Matrix.mul_one, hWS, Matrix.mul_one, hQQ']
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_mul, hW]
    simp only [Matrix.mul_assoc]

@[expose] def SymmetricMidpointDefect (S Z : Ten2) : Prop :=
  Z.transpose = Z ∧ star Z * Z = 1 - S * S ∧
    Z * star Z = 1 - S * S ∧ S * Z + star Z * S = 0

theorem midpoint_defect_unitary (S Z : Ten2) (hS : star S = S)
    (hn : star Z * Z = 1 - S * S) (hc : S * Z + star Z * S = 0) :
    S + Z ∈ unitary Ten2 ∧ S - Z ∈ unitary Ten2 := by
  have hp : star (S + Z) * (S + Z) = 1 := by
    rw [star_add, hS]
    calc
      _ = S * S + star Z * Z + (S * Z + star Z * S) := by noncomm_ring
      _ = 1 := by rw [hn, hc]; abel
  have hm : star (S - Z) * (S - Z) = 1 := by
    rw [star_sub, hS]
    calc
      _ = S * S + star Z * Z - (S * Z + star Z * S) := by noncomm_ring
      _ = 1 := by rw [hn, hc]; abel
  exact ⟨Unitary.mem_iff.mpr ⟨hp, mul_eq_one_comm.mp hp⟩,
    Unitary.mem_iff.mpr ⟨hm, mul_eq_one_comm.mp hm⟩⟩

theorem diagR_star (a b : ℝ) : star (diagR a b) = diagR a b := by
  change (diagR a b).conjTranspose = diagR a b
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagR, Matrix.conjTranspose_apply]

theorem diagR_transpose (a b : ℝ) : (diagR a b).transpose = diagR a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagR, Matrix.transpose_apply]

end GSTC.Scattering
