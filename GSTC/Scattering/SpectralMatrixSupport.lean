/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section
set_option autoImplicit false

namespace GSTC.Scattering.SpectralMatrixSupport
open scoped Matrix Matrix.Norms.L2Operator

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

@[expose] noncomputable def opNorm (M : Mat) : ℝ := ‖M‖
@[expose] def quadForm (S : Mat) (v : Fin 2 → ℝ) : ℝ := v ⬝ᵥ (S *ᵥ v)

theorem norm_sq_vec (v : Fin 2 → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖^2 = quadForm 1 v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [quadForm, Matrix.one_mulVec, Fin.sum_univ_two, dotProduct]
  ring

theorem norm_sq_mulVec (M : Mat) (v : Fin 2 → ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) M (WithLp.toLp 2 v)‖^2 =
      quadForm (M.transpose * M) v := by
  rw [EuclideanSpace.real_norm_sq_eq, Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_toLp]
  simp only [quadForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.transpose_apply]
  ring

theorem opNorm_le_iff_quad (M : Mat) (t : ℝ) (ht : 0 ≤ t) :
    opNorm M ≤ t ↔ ∀ v, quadForm (M.transpose * M) v ≤ t^2 * quadForm 1 v := by
  constructor
  · intro h v
    have hT : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) M‖ ≤ t := h
    have hv := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) M).le_opNorm
      (WithLp.toLp 2 v)
    have hh := hv.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht (norm_nonneg _))).mpr hh
    simpa only [mul_pow, norm_sq_vec, norm_sq_mulVec] using hs
  · intro h
    change ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) M‖ ≤ t
    apply ContinuousLinearMap.opNorm_le_bound _ ht
    intro x
    have hh := h (WithLp.ofLp x)
    rw [← norm_sq_mulVec, ← norm_sq_vec] at hh
    simp only [WithLp.toLp_ofLp] at hh
    rw [← mul_pow] at hh
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht (norm_nonneg _))).mp hh

theorem opNorm_le_iff_psd (M : Mat) (t : ℝ) (ht : 0 ≤ t) :
    opNorm M ≤ t ↔ (t^2 • (1 : Mat) - M.transpose * M).PosSemidef := by
  rw [opNorm_le_iff_quad M t ht, Matrix.posSemidef_iff_dotProduct_mulVec]
  have hsym : (t^2 • (1 : Mat) - M.transpose * M).IsHermitian := by
    change (t^2 • (1 : Mat) - M.transpose * M).conjTranspose = _
    simp [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul]
  simp only [hsym, true_and]
  apply forall_congr'
  intro v
  have he : star v ⬝ᵥ ((t^2 • (1 : Mat) - M.transpose * M) *ᵥ v) =
      t^2 * quadForm 1 v - quadForm (M.transpose * M) v := by
    simp [quadForm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul]
  rw [he]
  exact sub_nonneg.symm

theorem opNorm_orthogonal_conjugation (M Q : Mat) (hQ : Q.transpose * Q = 1) :
    opNorm (Q * M * Q.transpose) = opNorm M := by
  have hu : Q ∈ unitary Mat := by
    apply Unitary.mem_iff.mpr
    constructor
    · simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        using hQ
    · have hi : Q.transpose = Q⁻¹ := (Matrix.inv_eq_left_inv hQ).symm
      simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, hi]
        using Matrix.mul_nonsing_inv Q (Matrix.isUnit_det_of_left_inverse hQ)
  have hut : Q.transpose ∈ unitary Mat := by
    have hh := Unitary.star_mem hu
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hh
  exact (CStarRing.norm_mul_mem_unitary _ hut).trans (CStarRing.norm_mem_unitary_mul _ hu)

theorem psd_iff_principal_minors (S : Mat) (hS : S.transpose = S) :
    S.PosSemidef ↔ 0 ≤ S 0 0 ∧ 0 ≤ S 1 1 ∧ 0 ≤ S.det := by
  constructor
  · intro h
    exact ⟨h.diag_nonneg, h.diag_nonneg, h.det_nonneg⟩
  · rintro ⟨ha,hd,hdet⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hS
    intro v
    have hb : S 1 0 = S 0 1 := congrArg (fun M : Mat => M 0 1) hS
    have hdet' : 0 ≤ S 0 0 * S 1 1 - (S 0 1)^2 := by
      simpa [Matrix.det_fin_two, hb, sq] using hdet
    have q : 0 ≤ S 0 0 * (v 0)^2 + 2*S 0 1*v 0*v 1 + S 1 1*(v 1)^2 := by
      by_cases hz : S 0 0 = 0
      · have hbz : S 0 1 = 0 := by rw [hz] at hdet'; nlinarith [sq_nonneg (S 0 1)]
        simp only [hz, hbz, mul_zero, zero_mul, zero_add]
        exact mul_nonneg hd (sq_nonneg _)
      · have hp : 0 < S 0 0 := lt_of_le_of_ne ha (Ne.symm hz)
        have he : S 0 0 * (S 0 0 * (v 0)^2 + 2*S 0 1*v 0*v 1 + S 1 1*(v 1)^2) =
            (S 0 0*v 0 + S 0 1*v 1)^2 +
              (S 0 0*S 1 1-(S 0 1)^2)*(v 1)^2 := by ring
        have hh : 0 ≤ S 0 0 *
            (S 0 0 * (v 0)^2 + 2*S 0 1*v 0*v 1 + S 1 1*(v 1)^2) := by
          rw [he]
          exact add_nonneg (sq_nonneg _) (mul_nonneg hdet' (sq_nonneg _))
        exact nonneg_of_mul_nonneg_right hh hp
    have he : star v ⬝ᵥ (S *ᵥ v) =
        S 0 0 * (v 0)^2 + 2*S 0 1*v 0*v 1 + S 1 1*(v 1)^2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, hb]
      ring
    rwa [he]

theorem opNorm_le_iff_polynomial (M : Mat) (t : ℝ) (ht : 0 ≤ t) :
    opNorm M ≤ t ↔
      0 ≤ t^2 - ((M 0 0)^2 + (M 1 0)^2) ∧
      0 ≤ t^2 - ((M 0 1)^2 + (M 1 1)^2) ∧
      0 ≤ (t^2 - ((M 0 0)^2 + (M 1 0)^2)) *
          (t^2 - ((M 0 1)^2 + (M 1 1)^2)) -
          (M 0 0*M 0 1 + M 1 0*M 1 1)^2 := by
  rw [opNorm_le_iff_psd M t ht, psd_iff_principal_minors]
  · simp [Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two, sq,
      mul_comm]
    ring_nf
    simp
  · simp [Matrix.transpose_mul]

theorem scaled_opNorm_cap (M : Mat) (k β : ℝ) (hk : 0 ≤ k) :
    k * opNorm M ≤ β ↔ opNorm (k • M) ≤ β := by
  simp [opNorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hk]

theorem continuous_opNorm : Continuous opNorm := continuous_norm

theorem opNorm_nonneg (M : Mat) : 0 ≤ opNorm M := norm_nonneg M

theorem opNorm_eq_zero_iff (M : Mat) : opNorm M = 0 ↔ M = 0 := norm_eq_zero

theorem opNorm_smul (c : ℝ) (M : Mat) : opNorm (c • M) = |c| * opNorm M := by
  exact norm_smul c M

theorem entry_le_opNorm (M : Mat) (i j : Fin 2) : |M i j| ≤ opNorm M := by
  have hh := (opNorm_le_iff_quad M (opNorm M) (opNorm_nonneg M)).mp le_rfl
    (Pi.single j 1)
  have hn := opNorm_nonneg M
  fin_cases j <;> fin_cases i <;>
    simp [quadForm, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      dotProduct, Fin.sum_univ_two, Pi.single_apply] at hh ⊢ <;>
    rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg (M 0 0),
      sq_nonneg (M 0 1), sq_nonneg (M 1 0), sq_nonneg (M 1 1)]

theorem opNorm_diagonal2 (u v : ℝ) :
    opNorm (!![u, 0; 0, v] : Mat) = max |u| |v| := by
  have key : ∀ t : ℝ, 0 ≤ t →
      (opNorm (!![u, 0; 0, v] : Mat) ≤ t ↔ max |u| |v| ≤ t) := by
    intro t ht
    rw [opNorm_le_iff_polynomial _ t ht]
    simp
    constructor
    · rintro ⟨hA, hB, -⟩
      have h1 : |u| ≤ t := abs_le_of_sq_le_sq hA ht
      have h2 : |v| ≤ t := abs_le_of_sq_le_sq hB ht
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hu2 : u ^ 2 ≤ t ^ 2 := by
        have hh := mul_self_le_mul_self (abs_nonneg u) h1
        nlinarith [hh, sq_abs u, sq_abs t]
      have hv2 : v ^ 2 ≤ t ^ 2 := by
        have hh := mul_self_le_mul_self (abs_nonneg v) h2
        nlinarith [hh, sq_abs v, sq_abs t]
      refine ⟨by nlinarith, by nlinarith, ?_⟩
      have e1 : 0 ≤ t ^ 2 - u ^ 2 := by nlinarith
      have e2 : 0 ≤ t ^ 2 - v ^ 2 := by nlinarith
      have hm : 0 ≤ (t ^ 2 - u ^ 2) * (t ^ 2 - v ^ 2) := mul_nonneg e1 e2
      nlinarith [hm]
  apply le_antisymm
  · exact (key _ (le_trans (abs_nonneg u) (le_max_left _ _))).mpr (le_refl _)
  · exact (key _ (opNorm_nonneg _)).mp le_rfl

theorem opNorm_scalar_tracelessSymm2 (c p q : ℝ) :
    opNorm (c • (1 : Mat) + !![p, q; q, -p] : Mat) = |c| + Real.sqrt (p^2 + q^2) := by
  have hM : (c • (1 : Mat) + !![p, q; q, -p] : Mat) = !![c + p, q; q, c - p] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, Matrix.add_apply, sub_eq_add_neg]
  have key : ∀ t : ℝ, 0 ≤ t →
      (opNorm (c • (1 : Mat) + !![p, q; q, -p] : Mat) ≤ t
        ↔ |c| + Real.sqrt (p^2 + q^2) ≤ t) := by
    intro t ht
    rw [hM, opNorm_le_iff_polynomial _ t ht]
    simp
    have hs : 0 ≤ p ^ 2 + q ^ 2 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hρ : (Real.sqrt (p ^ 2 + q ^ 2)) ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt hs
    have hcρ : 0 ≤ |c| * Real.sqrt (p ^ 2 + q ^ 2) :=
      mul_nonneg (abs_nonneg c) (Real.sqrt_nonneg _)
    constructor
    · rintro ⟨hA, hB, hC⟩
      have hC'' : (2 * |c| * Real.sqrt (p ^ 2 + q ^ 2)) ^ 2
          ≤ (t ^ 2 - c ^ 2 - (p ^ 2 + q ^ 2)) ^ 2 := by
        nlinarith [hC, hρ, sq_abs c]
      have hu0 : 0 ≤ t ^ 2 - c ^ 2 - (p ^ 2 + q ^ 2) := by nlinarith [hA, hB]
      have hsq : Real.sqrt ((2 * |c| * Real.sqrt (p ^ 2 + q ^ 2)) ^ 2)
          ≤ Real.sqrt ((t ^ 2 - c ^ 2 - (p ^ 2 + q ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hC''
      have habs : 2 * |c| * Real.sqrt (p ^ 2 + q ^ 2)
          ≤ t ^ 2 - c ^ 2 - (p ^ 2 + q ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at hsq
        rw [abs_of_nonneg (show 0 ≤ t ^ 2 - c ^ 2 - (p ^ 2 + q ^ 2) by nlinarith [hu0]),
          abs_of_nonneg (show 0 ≤ 2 * |c| * Real.sqrt (p ^ 2 + q ^ 2) by positivity)] at hsq
        exact hsq
      have hsq' : (|c| + Real.sqrt (p ^ 2 + q ^ 2)) ^ 2 ≤ t ^ 2 := by
        nlinarith [habs, hρ, sq_abs c]
      have hnonneg : 0 ≤ |c| + Real.sqrt (p ^ 2 + q ^ 2) := by positivity
      have h1 : |c| + Real.sqrt (p ^ 2 + q ^ 2) ≤ t := by
        have hh := (Real.le_sqrt hnonneg (by nlinarith [ht])).mpr hsq'
        rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg ht] at hh
      exact h1
    · intro h
      have hsq := mul_self_le_mul_self
        (show 0 ≤ |c| + Real.sqrt (p ^ 2 + q ^ 2) from by positivity) h
      have hu2 : 2 * |c| * Real.sqrt (p ^ 2 + q ^ 2)
          ≤ t ^ 2 - c ^ 2 - (p ^ 2 + q ^ 2) := by
        nlinarith [hsq, hρ, sq_abs c, hcρ]
      have hρp : |p| ≤ Real.sqrt (p ^ 2 + q ^ 2) := by
        have h1 : p ^ 2 ≤ p ^ 2 + q ^ 2 := by nlinarith [sq_nonneg q]
        have h2 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq_eq_abs] at h2
      have hcp : c * p ≤ |c| * Real.sqrt (p ^ 2 + q ^ 2) := by
        calc c * p ≤ |c * p| := le_abs_self _
          _ = |c| * |p| := abs_mul c p
          _ ≤ |c| * Real.sqrt (p ^ 2 + q ^ 2) :=
            mul_le_mul_of_nonneg_left hρp (abs_nonneg c)
      have hcp' : -c * p ≤ |c| * Real.sqrt (p ^ 2 + q ^ 2) := by
        calc -c * p ≤ |(-c) * p| := le_abs_self _
          _ = |c| * |p| := by rw [abs_mul, abs_neg]
          _ ≤ |c| * Real.sqrt (p ^ 2 + q ^ 2) :=
            mul_le_mul_of_nonneg_left hρp (abs_nonneg c)
      refine ⟨?_, ?_, ?_⟩
      · nlinarith [hu2, hcp]
      · nlinarith [hu2, hcp']
      · have hmul : 0 ≤
              (t ^ 2 - c ^ 2 - (p ^ 2 + q ^ 2)
                - 2 * |c| * Real.sqrt (p ^ 2 + q ^ 2))
              * (t ^ 2 - c ^ 2 - (p ^ 2 + q ^ 2)
                + 2 * |c| * Real.sqrt (p ^ 2 + q ^ 2)) :=
          mul_nonneg (by nlinarith [hu2]) (by nlinarith [hu2])
        nlinarith [hmul, hρ, sq_abs c]
  apply le_antisymm
  · exact (key _ (by positivity)).mpr (le_refl _)
  · exact (key _ (opNorm_nonneg _)).mp le_rfl

end GSTC.Scattering.SpectralMatrixSupport
