/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.NBTakagi

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Complex.Polynomial.Basic

public section
namespace GSTC.Scattering
open scoped Matrix

theorem nb_hermitian_spectral2 (H : Ten2) (hH : H.IsHermitian) :
    ∃ Q : Ten2, Q ∈ unitary Ten2 ∧ ∃ a b : ℝ,
      H = Q * diagR a b * star Q := by
  refine ⟨hH.eigenvectorUnitary, hH.eigenvectorUnitary.property,
    hH.eigenvalues 0, hH.eigenvalues 1, ?_⟩
  have he := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at he
  have hd : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
      diagR (hH.eigenvalues 0) (hH.eigenvalues 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagR, Matrix.diagonal]
  rw [hd] at he
  exact he

theorem nb_congruence_recover (Q X : Ten2) (hQ : Q ∈ unitary Ten2) :
    Q * (star Q * X * Q.map star) * Q.transpose = X := by
  have h1 := (Unitary.mem_iff.mp hQ).2
  have h2 := unitary_conj_transpose Q hQ
  calc
    _ = (Q * star Q) * X * (Q.map star * Q.transpose) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem nb_congruence_pull_symmetric (Q X : Ten2) (hX : X.transpose = X) :
    (star Q * X * Q.map star).transpose = star Q * X * Q.map star := by
  simp only [Matrix.transpose_mul, map_star_transpose, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_transpose, hX, Matrix.mul_assoc]

theorem nb_congruence_pull_gram (Q X : Ten2) (hQ : Q ∈ unitary Ten2) :
    (star Q * X * Q.map star) * star (star Q * X * Q.map star) =
      star Q * (X * star X) * Q := by
  have h1 := unitary_conj_transpose Q hQ
  have htrans : star (Q.map star) = Q.transpose := by
    ext i j
    simp [Matrix.map_apply, Matrix.transpose_apply]
  simp only [star_mul, star_star, htrans]
  calc
    _ = star Q * X * (Q.map star * Q.transpose) * star X * Q := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem nb_scalar_takagi (z : ℂ) :
    ∃ c : ℂ, star c * c = 1 ∧ z = c^2 * (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · subst z
    exact ⟨1, by simp, by simp⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnc : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (z / (‖z‖ : ℂ)) (by decide : 0 < 2)
  have hnorm : ‖c‖^2 = 1 := by
    have he := congrArg norm hc
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg z), div_self hn] at he
    exact he
  refine ⟨c, ?_, ?_⟩
  · rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hnorm]
    rfl
  · rw [hc, div_mul_cancel₀ _ hnc]

theorem nb_real_spectral2 (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.transpose = A) :
    ∃ O : Matrix (Fin 2) (Fin 2) ℝ, O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
      ∃ a b : ℝ, A = O * !![a, 0; 0, b] * O.transpose := by
  have hH : A.IsHermitian := by
    change A.conjTranspose = A
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hA]
  let O : Matrix (Fin 2) (Fin 2) ℝ := hH.eigenvectorUnitary
  have hO : O ∈ unitary (Matrix (Fin 2) (Fin 2) ℝ) :=
    hH.eigenvectorUnitary.property
  have hl := (Unitary.mem_iff.mp hO).1
  have hr := (Unitary.mem_iff.mp hO).2
  simp only [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at hl hr
  refine ⟨O, hl, hr, hH.eigenvalues 0, hH.eigenvalues 1, ?_⟩
  have he := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at he
  have hd : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
      !![hH.eigenvalues 0, 0; 0, hH.eigenvalues 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [hd, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at he
  exact he

theorem nb_real_orthogonal_unitary (O : Matrix (Fin 2) (Fin 2) ℝ)
    (hO : O.transpose * O = 1) :
    O.map Complex.ofReal ∈ unitary Ten2 := by
  have hstar : star (O.map Complex.ofReal) = O.transpose.map Complex.ofReal := by
    ext i j
    simp [Matrix.map_apply, Matrix.transpose_apply]
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
    M.map (Complex.ofRealHom)) hO
  rw [Matrix.map_mul] at he
  have hf : (Complex.ofRealHom : ℝ → ℂ) = Complex.ofReal := by
    funext r; exact Complex.ofRealHom_eq_coe r
  rw [hf] at he
  have he' : star (O.map Complex.ofReal) * O.map Complex.ofReal = 1 := by
    rw [hstar]
    simpa using he
  exact Unitary.mem_iff.mpr ⟨he', mul_eq_one_comm.mp he'⟩

theorem nb_real_simultaneous2 (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) (hc : A * B = B * A) :
    ∃ O : Matrix (Fin 2) (Fin 2) ℝ, O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
      ∃ a b c d : ℝ, A = O * !![a, 0; 0, b] * O.transpose ∧
        B = O * !![c, 0; 0, d] * O.transpose := by
  obtain ⟨O, hl, hr, a, b, he⟩ := nb_real_spectral2 A hA
  by_cases hab : a = b
  · subst b
    have hd : (!![a, 0; 0, a] : Matrix (Fin 2) (Fin 2) ℝ) = a • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hAs : A = a • 1 := by
      rw [he, hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hr]
    obtain ⟨P, hpl, hpr, c, d, hBe⟩ := nb_real_spectral2 B hB
    refine ⟨P, hpl, hpr, a, a, c, d, ?_, hBe⟩
    rw [hAs, hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hpr]
  · let C := O.transpose * B * O
    have hCe : O * C * O.transpose = B := by
      dsimp [C]
      calc
        _ = (O * O.transpose) * B * (O * O.transpose) := by
          simp only [Matrix.mul_assoc]
        _ = B := by rw [hr, Matrix.one_mul, Matrix.mul_one]
    have hD : O.transpose * A * O = !![a, 0; 0, b] := by
      rw [he]
      calc
        _ = (O.transpose * O) * !![a, 0; 0, b] * (O.transpose * O) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hl, Matrix.one_mul, Matrix.mul_one]
    have hcancel (M : Matrix (Fin 2) (Fin 2) ℝ) : O * (O.transpose * M) = M := by
      rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
    have hcomm : (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℝ) * C =
        C * !![a, 0; 0, b] := by
      rw [← hD]
      dsimp [C]
      calc
        _ = O.transpose * (A * B) * O := by
          simp only [Matrix.mul_assoc, hcancel]
        _ = O.transpose * (B * A) * O := by rw [hc]
        _ = _ := by simp only [Matrix.mul_assoc, hcancel]
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hcomm
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) hcomm
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
    have hz01 : C 0 1 = 0 := by
      apply (mul_eq_zero.mp (show (a-b)*C 0 1 = 0 by linear_combination h01)).resolve_left
        (sub_ne_zero.mpr hab)
    have hz10 : C 1 0 = 0 := by
      apply (mul_eq_zero.mp (show (a-b)*C 1 0 = 0 by linear_combination -1*h10)).resolve_left
        (sub_ne_zero.mpr hab)
    have hCd : C = !![C 0 0, 0; 0, C 1 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hz01, hz10]
    exact ⟨O, hl, hr, a, b, C 0 0, C 1 1, he, by rw [← hCd, hCe]⟩

theorem nb_normal_parts_commute (T : Ten2) (hT : T.transpose = T)
    (hn : T * star T = star T * T) :
    T.map Complex.re * T.map Complex.im = T.map Complex.im * T.map Complex.re := by
  have hs : T 1 0 = T 0 1 := congrArg (fun M : Ten2 => M 0 1) hT
  ext i j
  have he := congrArg (fun M : Ten2 => (M i j).im) hn
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Complex.mul_im,
      hs] at he ⊢
  all_goals linear_combination (-1/2) * he

theorem nb_normal_symmetric_diagonal (T : Ten2) (hT : T.transpose = T)
    (hn : T * star T = star T * T) :
    ∃ Q : Ten2, Q ∈ unitary Ten2 ∧ ∃ z w : ℂ,
      T = Q * diag2 z w * Q.transpose := by
  let A := T.map Complex.re
  let B := T.map Complex.im
  have hA : A.transpose = A := by
    ext i j
    exact congrArg Complex.re (congrArg (fun M : Ten2 => M i j) hT)
  have hB : B.transpose = B := by
    ext i j
    exact congrArg Complex.im (congrArg (fun M : Ten2 => M i j) hT)
  obtain ⟨O, hl, _, a, b, c, d, hAe, hBe⟩ :=
    nb_real_simultaneous2 A B hA hB (nb_normal_parts_commute T hT hn)
  refine ⟨O.map Complex.ofReal, nb_real_orthogonal_unitary O hl,
    (a : ℂ) + Complex.I*c, (b : ℂ) + Complex.I*d, ?_⟩
  have hTc : T = A.map Complex.ofReal + Complex.I • B.map Complex.ofReal := by
    ext i j
    change T i j = ((T i j).re : ℂ) + Complex.I * (T i j).im
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im (T i j)).symm
  rw [hTc, hAe, hBe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
      Matrix.transpose_apply, Complex.ofReal_add, Complex.ofReal_mul]
    <;> ring

theorem nb_symmetric_unitary_diagonal (T : Ten2) (hT : T.transpose = T) :
    ∃ Q : Ten2, Q ∈ unitary Ten2 ∧ ∃ z w : ℂ,
      T = Q * diag2 z w * Q.transpose := by
  have hH : (T * star T).IsHermitian := by
    change (T * star T).conjTranspose = T * star T
    simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  obtain ⟨Q, hQ, a, b, hspec⟩ := nb_hermitian_spectral2 (T * star T) hH
  let B := star Q * T * Q.map star
  have hB : B.transpose = B := nb_congruence_pull_symmetric Q T hT
  have hnorm : B * star B = diagR a b := by
    rw [nb_congruence_pull_gram Q T hQ, hspec]
    have hq := (Unitary.mem_iff.mp hQ).1
    calc
      _ = (star Q * Q) * diagR a b * (star Q * Q) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hq, Matrix.one_mul, Matrix.mul_one]
  have hbs : (star B).transpose = star B := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_transpose,
      conjTranspose_eq_map_star_of_symmetric hB]
  have hnorm' : star B * B = diagR a b := by
    have he := congrArg (fun M : Ten2 => M.transpose) hnorm
    simpa only [Matrix.transpose_mul, hbs, hB, diagR_transpose] using he
  obtain ⟨P, hP, z, w, he⟩ :=
    nb_normal_symmetric_diagonal B hB (hnorm.trans hnorm'.symm)
  refine ⟨Q * P, (unitary Ten2).mul_mem hQ hP, z, w, ?_⟩
  calc
    T = Q * B * Q.transpose := (nb_congruence_recover Q T hQ).symm
    _ = (Q * P) * diag2 z w * (Q * P).transpose := by
      rw [he, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]

theorem nb_diag2_unitary (c d : ℂ) (hc : star c * c = 1) (hd : star d * d = 1) :
    diag2 c d ∈ unitary Ten2 := by
  have he : star (diag2 c d) * diag2 c d = 1 := by
    simp only [Complex.star_def] at hc hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diag2, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, hc, hd]
  exact Unitary.mem_iff.mpr ⟨he, mul_eq_one_comm.mp he⟩

theorem nb_takagi_unsorted (T : Ten2) (hT : T.transpose = T) :
    ∃ Q : Ten2, Q ∈ unitary Ten2 ∧ ∃ a b : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ T = Q * diagR a b * Q.transpose := by
  obtain ⟨Q, hQ, z, w, he⟩ := nb_symmetric_unitary_diagonal T hT
  obtain ⟨c, hc, hz⟩ := nb_scalar_takagi z
  obtain ⟨d, hd, hw⟩ := nb_scalar_takagi w
  let P := diag2 c d
  have hp : P ∈ unitary Ten2 := nb_diag2_unitary c d hc hd
  have hdiag : diag2 z w = P * diagR ‖z‖ ‖w‖ * P.transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, diag2, diagR, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.transpose_apply]
    · linear_combination hz
    · linear_combination hw
  refine ⟨Q * P, (unitary Ten2).mul_mem hQ hp, ‖z‖, ‖w‖,
    norm_nonneg z, norm_nonneg w, ?_⟩
  rw [he, hdiag, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem nb_takagi_exists (T : Ten2) (hT : T.transpose = T) : Nonempty (Takagi2 T) := by
  obtain ⟨Q, hQ, a, b, ha, hb, he⟩ := nb_takagi_unsorted T hT
  by_cases hab : b ≤ a
  · exact ⟨⟨Q, hQ, a, b, ha, hb, hab, he⟩⟩
  · let P : Ten2 := !![0, 1; 1, 0]
    have hp : P ∈ unitary Ten2 := by
      have hl : star P * P = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [P, Matrix.mul_apply, Fin.sum_univ_two]
      exact Unitary.mem_iff.mpr ⟨hl, mul_eq_one_comm.mp hl⟩
    have hd : diagR a b = P * diagR b a * P.transpose := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, diagR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    refine ⟨⟨Q * P, (unitary Ten2).mul_mem hQ hp, b, a, hb, ha,
      le_of_lt (lt_of_not_ge hab), ?_⟩⟩
    rw [he, hd, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

theorem nb_imaginary_diagonal_defect (s t r q : ℝ)
    (hr : s^2+r^2=1) (hq : t^2+q^2=1) :
    SymmetricMidpointDefect (diagR s t) (diag2 (Complex.I*r) (Complex.I*q)) := by
  have hi : star Complex.I = -Complex.I := by simp
  have hr' : (s : ℂ)^2+(r : ℂ)^2=1 := by exact_mod_cast hr
  have hq' : (t : ℂ)^2+(q : ℂ)^2=1 := by exact_mod_cast hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2, Matrix.transpose_apply]
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diag2, diagR, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    all_goals
      first
      | (solve | ring)
      | (ring_nf; rw [Complex.I_sq];
          first | linear_combination hr' | linear_combination hq')

end GSTC.Scattering
