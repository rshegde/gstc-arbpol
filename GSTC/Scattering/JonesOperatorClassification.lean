/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.NBPhaseConstraints
public import GSTC.Scattering.OrthogonalClasses

public section

namespace GSTC.Scattering
namespace JonesOperatorClassification

open scoped Matrix
open scoped ComplexConjugate
open OrthogonalClasses
open BIFeasibility

@[expose] noncomputable def jonesOverlap (u v : Vec2) : ℝ := ‖jonesInner u v‖

@[expose] def JonesIndependent (u₁ u₂ : Vec2) : Prop :=
  ∀ c₁ c₂ : ℂ, c₁ • u₁ + c₂ • u₂ = 0 → c₁ = 0 ∧ c₂ = 0

@[expose] def JonesUnitary (T : Ten2) : Prop := ten2Adjoint T * T = (1 : Ten2)

theorem jonesUnitary_iff_mem_unitary (T : Ten2) :
    JonesUnitary T ↔ T ∈ unitary Ten2 := by
  constructor
  · intro hT
    rw [Unitary.mem_iff]
    refine ⟨hT, ?_⟩

    have hdet : T.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hT
    have hunit : IsUnit T.det := isUnit_iff_ne_zero.mpr hdet
    have hmul : (T * ten2Adjoint T) * T = T * (1 : Ten2) := by
      rw [Matrix.mul_assoc, hT, Matrix.mul_one]
    have h2 := congrArg (fun M : Ten2 => M * T⁻¹) hmul
    calc T * ten2Adjoint T = (T * ten2Adjoint T) * (1 : Ten2) := (Matrix.mul_one _).symm
      _ = (T * ten2Adjoint T) * (T * T⁻¹) := by rw [Matrix.mul_nonsing_inv T hunit]
      _ = (T * ten2Adjoint T) * T * T⁻¹ := by rw [← Matrix.mul_assoc]
      _ = T * (1 : Ten2) * T⁻¹ := h2
      _ = (1 : Ten2) := by rw [Matrix.mul_one, Matrix.mul_nonsing_inv T hunit]
  · intro hT
    rcases hT with ⟨h₁, h₂⟩
    exact h₁

theorem hc_eq_jonesInner_swap (u v : Vec2) : hc u v = jonesInner v u := by
  simp [hc, dot2, conjV, jonesInner]
  ring

theorem jonesInner_of_jonesUnitary {T : Ten2} (hT : JonesUnitary T) (u v : Vec2) :
    jonesInner (T *ᵥ u) (T *ᵥ v) = jonesInner u v := by
  have h := hc_ten2Adjoint T u (T *ᵥ v)
  rw [Matrix.mulVec_mulVec v (ten2Adjoint T) T, hT, Matrix.one_mulVec] at h
  rw [hc_eq_jonesInner_swap, hc_eq_jonesInner_swap] at h
  have h' := congrArg star h
  rw [jonesInner_conj, jonesInner_conj] at h'
  exact h'.symm

theorem unit_phase_star_mul (z : ℂ) (hz : ‖z‖ = 1) : star z * z = 1 := by
  exact NBPhaseConstraints.nb_phase_star_mul z hz

theorem exists_unit_phase (d c : ℂ) (h : ‖d‖ = ‖c‖) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ z * c = d := by
  by_cases hc : c = 0
  · have hd0 : ‖d‖ = 0 := h.trans (by rw [hc, norm_zero])
    have hd : d = 0 := norm_eq_zero.mp hd0
    refine ⟨1, ?_, ?_⟩
    · simp
    · rw [hd, hc, mul_zero]
  · have hcne : ‖c‖ ≠ 0 := fun hz => hc (norm_eq_zero.mp hz)
    have hdne : ‖d‖ ≠ 0 := by rw [h]; exact hcne
    refine ⟨d / c, ?_, ?_⟩
    · rw [norm_div, h.symm, div_self_eq_one₀.mpr hdne]
    · field_simp

theorem ten2Adjoint_mul (A B : Ten2) :
    ten2Adjoint (A * B) = ten2Adjoint B * ten2Adjoint A := by
  ext i j
  simp only [Matrix.mul_apply, ten2Adjoint_apply, Fin.sum_univ_two, star_add, star_mul]

@[expose] def jonesColMatrix (u₁ u₂ : Vec2) : Ten2 :=
  fun i j => Fin.cases (u₁ i) (fun _ => u₂ i) j

theorem jonesColMatrix_apply_zero (u₁ u₂ : Vec2) (i : Fin 2) :
    jonesColMatrix u₁ u₂ i 0 = u₁ i := rfl

theorem jonesColMatrix_apply_one (u₁ u₂ : Vec2) (i : Fin 2) :
    jonesColMatrix u₁ u₂ i 1 = u₂ i := rfl

theorem jonesColMatrix_apply_zero' (u₁ u₂ : Vec2) (i : Fin 2) (h : 0 < 2) :
    jonesColMatrix u₁ u₂ i ⟨0, h⟩ = u₁ i := rfl

theorem jonesColMatrix_apply_one' (u₁ u₂ : Vec2) (i : Fin 2) (h : 1 < 2) :
    jonesColMatrix u₁ u₂ i ⟨1, h⟩ = u₂ i := rfl

@[expose] def jonesGram (u₁ u₂ : Vec2) : Ten2 :=
  ten2Adjoint (jonesColMatrix u₁ u₂) * jonesColMatrix u₁ u₂

theorem jonesGram_hermitian (u₁ u₂ : Vec2) :
    ten2Adjoint (jonesGram u₁ u₂) = jonesGram u₁ u₂ := by
  unfold jonesGram
  rw [ten2Adjoint_mul, ten2Adjoint_involutive]

theorem jonesNormSq_smul_unit (c : ℂ) (hc : star c * c = 1) (v : Vec2) :
    star (c * v 0) * (c * v 0) + star (c * v 1) * (c * v 1)
      = star (v 0) * v 0 + star (v 1) * v 1 := by
  calc star (c * v 0) * (c * v 0) + star (c * v 1) * (c * v 1)
      = (star (v 0) * (star c * c)) * v 0 + (star (v 1) * (star c * c)) * v 1 := by
        simp only [star_mul]
        ring
    _ = star (v 0) * v 0 + star (v 1) * v 1 := by rw [hc]; ring

theorem jonesGram_eq (u₁ u₂ v₁ v₂ : Vec2) (z : ℂ)
    (hu₁ : isNormalized u₁) (hu₂ : isNormalized u₂)
    (hv₁ : isNormalized v₁) (hv₂ : isNormalized v₂)
    (hz : ‖z‖ = 1) (hzc : z * jonesInner v₁ v₂ = jonesInner u₁ u₂) :
    jonesGram u₁ u₂ = jonesGram v₁ (z • v₂) := by
  have hzstar : star z * z = 1 := unit_phase_star_mul z hz
  have hu₁' : star (u₁ 0) * u₁ 0 + star (u₁ 1) * u₁ 1 = 1 := by
    simpa only [jonesInner, isNormalized] using hu₁
  have hu₂' : star (u₂ 0) * u₂ 0 + star (u₂ 1) * u₂ 1 = 1 := by
    simpa only [jonesInner, isNormalized] using hu₂
  have hv₁' : star (v₁ 0) * v₁ 0 + star (v₁ 1) * v₁ 1 = 1 := by
    simpa only [jonesInner, isNormalized] using hv₁
  have hv₂' : star (v₂ 0) * v₂ 0 + star (v₂ 1) * v₂ 1 = 1 := by
    simpa only [jonesInner, isNormalized] using hv₂
  have h00 : jonesGram u₁ u₂ 0 0 = jonesGram v₁ (z • v₂) 0 0 := by
    simp only [jonesGram, Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply,
      jonesColMatrix_apply_zero]
    rw [hu₁', hv₁']
  have h01 : jonesGram u₁ u₂ 0 1 = jonesGram v₁ (z • v₂) 0 1 := by
    simp only [jonesGram, Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply,
      jonesColMatrix_apply_zero, jonesColMatrix_apply_one, Pi.smul_apply, smul_eq_mul]
    calc star (u₁ 0) * u₂ 0 + star (u₁ 1) * u₂ 1 = jonesInner u₁ u₂ := rfl
      _ = z * jonesInner v₁ v₂ := hzc.symm
      _ = star (v₁ 0) * (z * v₂ 0) + star (v₁ 1) * (z * v₂ 1) := by
          rw [jonesInner]
          ring
  have h11 : jonesGram u₁ u₂ 1 1 = jonesGram v₁ (z • v₂) 1 1 := by
    simp only [jonesGram, Matrix.mul_apply, Fin.sum_univ_two, ten2Adjoint_apply,
      jonesColMatrix_apply_one, Pi.smul_apply, smul_eq_mul]
    calc star (u₂ 0) * u₂ 0 + star (u₂ 1) * u₂ 1 = 1 := hu₂'
      _ = star (v₂ 0) * v₂ 0 + star (v₂ 1) * v₂ 1 := by rw [hv₂']
      _ = star (z * v₂ 0) * (z * v₂ 0) + star (z * v₂ 1) * (z * v₂ 1) := by
          symm
          exact jonesNormSq_smul_unit z hzstar v₂
  have h10 : jonesGram u₁ u₂ 1 0 = jonesGram v₁ (z • v₂) 1 0 := by
    calc jonesGram u₁ u₂ 1 0 = star (jonesGram u₁ u₂ 0 1) := by
          rw [← ten2Adjoint_apply, jonesGram_hermitian]
      _ = star (jonesGram v₁ (z • v₂) 0 1) := by rw [h01]
      _ = jonesGram v₁ (z • v₂) 1 0 := by
          rw [← ten2Adjoint_apply, jonesGram_hermitian]
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem jonesColMatrix_det (u₁ u₂ : Vec2) :
    (jonesColMatrix u₁ u₂).det = u₁ 0 * u₂ 1 - u₁ 1 * u₂ 0 := by
  rw [Matrix.det_fin_two]
  simp only [jonesColMatrix_apply_zero, jonesColMatrix_apply_one]
  ring

theorem jonesIndependent_det_ne_zero (u₁ u₂ : Vec2) (h : JonesIndependent u₁ u₂) :
    (jonesColMatrix u₁ u₂).det ≠ 0 := by
  rw [jonesColMatrix_det]
  intro hdet
  by_cases h0 : u₁ 0 = 0
  · by_cases h1 : u₁ 1 = 0
    ·
      have hrel : (1 : ℂ) • u₁ + (0 : ℂ) • u₂ = 0 := by
        ext i
        fin_cases i <;> simp [h0, h1]
      obtain ⟨hc1, _⟩ := h 1 0 hrel
      exact absurd hc1 (by simp)
    ·
      have hu20 : u₂ 0 = 0 := by
        have hzero : u₁ 1 * u₂ 0 = 0 := by
          rw [h0, zero_mul, sub_eq_zero] at hdet
          exact hdet.symm
        exact (mul_eq_zero.mp hzero).resolve_left h1
      have hrel : (-(u₂ 1 / u₁ 1)) • u₁ + (1 : ℂ) • u₂ = 0 := by
        ext i
        fin_cases i
        · simp [Pi.smul_apply, smul_eq_mul, h0, hu20]
        · have hzero : (-(u₂ 1 / u₁ 1)) * u₁ 1 + 1 * u₂ 1 = 0 := by
            field_simp
            ring
          simpa [Pi.smul_apply, smul_eq_mul] using hzero
      obtain ⟨_, hc2⟩ := h (-(u₂ 1 / u₁ 1)) 1 hrel
      exact absurd hc2 (by simp)
  ·
    have hu21 : u₂ 1 = u₁ 1 * (u₂ 0 / u₁ 0) := by
      have hkey : u₁ 0 * u₂ 1 = u₁ 1 * u₂ 0 := sub_eq_zero.mp hdet
      field_simp
      rw [mul_comm (u₂ 1) (u₁ 0), hkey]
    have hrel : (-(u₂ 0 / u₁ 0)) • u₁ + (1 : ℂ) • u₂ = 0 := by
      ext i
      fin_cases i
      · have hzero : (-(u₂ 0 / u₁ 0)) * u₁ 0 + 1 * u₂ 0 = 0 := by
          field_simp
          ring
        simpa [Pi.smul_apply, smul_eq_mul] using hzero
      · have hzero : (-(u₂ 0 / u₁ 0)) * u₁ 1 + 1 * u₂ 1 = 0 := by
          rw [hu21]
          field_simp
          ring
        simpa [Pi.smul_apply, smul_eq_mul] using hzero
    obtain ⟨_, hc2⟩ := h (-(u₂ 0 / u₁ 0)) 1 hrel
    exact absurd hc2 (by simp)

def jonesE₀ : Vec2 := ![1, 0]

def jonesE₁ : Vec2 := ![0, 1]

theorem jonesColMatrix_mulVec_e₀ (u₁ u₂ : Vec2) :
    jonesColMatrix u₁ u₂ *ᵥ jonesE₀ = u₁ := by
  ext i
  fin_cases i
  · simp [jonesE₀, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two,
      jonesColMatrix_apply_zero, jonesColMatrix_apply_one]
  · simp [jonesE₀, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two,
      jonesColMatrix_apply_zero, jonesColMatrix_apply_one]

theorem jonesColMatrix_mulVec_e₁ (u₁ u₂ : Vec2) :
    jonesColMatrix u₁ u₂ *ᵥ jonesE₁ = u₂ := by
  ext i
  fin_cases i
  · simp [jonesE₁, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two,
      jonesColMatrix_apply_zero, jonesColMatrix_apply_one]
  · simp [jonesE₁, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two,
      jonesColMatrix_apply_zero, jonesColMatrix_apply_one]

theorem ten2Adjoint_one : ten2Adjoint (1 : Ten2) = 1 := by
  ext i j
  simp only [ten2Adjoint, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem jonesUnitary_of_equal_gram (u₁ u₂ v₁ v₂ : Vec2) (z : ℂ)
    (hdet : (jonesColMatrix u₁ u₂).det ≠ 0)
    (hgram : jonesGram u₁ u₂ = jonesGram v₁ (z • v₂)) :
    ∃ T : Ten2, JonesUnitary T ∧ T *ᵥ u₁ = v₁ ∧ T *ᵥ u₂ = z • v₂ := by
  set U : Ten2 := jonesColMatrix u₁ u₂ with hU
  set V : Ten2 := jonesColMatrix v₁ (z • v₂) with hV
  set X : Ten2 := ten2_inv U hdet with hX
  have hUX : U * X = (1 : Ten2) := ten2_mul_inv U hdet
  have hXU : X * U = (1 : Ten2) := ten2_inv_mul U hdet
  have hUe₀ : U *ᵥ jonesE₀ = u₁ := by
    rw [hU]
    exact jonesColMatrix_mulVec_e₀ u₁ u₂
  have hUe₁ : U *ᵥ jonesE₁ = u₂ := by
    rw [hU]
    exact jonesColMatrix_mulVec_e₁ u₁ u₂
  have hVe₀ : V *ᵥ jonesE₀ = v₁ := by
    rw [hV]
    exact jonesColMatrix_mulVec_e₀ v₁ (z • v₂)
  have hVe₁ : V *ᵥ jonesE₁ = z • v₂ := by
    rw [hV]
    exact jonesColMatrix_mulVec_e₁ v₁ (z • v₂)
  have hXe₀ : X *ᵥ u₁ = jonesE₀ := by
    rw [← hUe₀, Matrix.mulVec_mulVec, hXU, Matrix.one_mulVec]
  have hXe₁ : X *ᵥ u₂ = jonesE₁ := by
    rw [← hUe₁, Matrix.mulVec_mulVec, hXU, Matrix.one_mulVec]
  refine ⟨V * X, ?_, ?_, ?_⟩
  ·
    have hgram' : ten2Adjoint U * U = ten2Adjoint V * V := by
      simpa [hU, hV, jonesGram] using hgram
    calc ten2Adjoint (V * X) * (V * X)
        = ten2Adjoint X * (ten2Adjoint V * (V * X)) := by
          rw [ten2Adjoint_mul]
          simp only [Matrix.mul_assoc]
      _ = ten2Adjoint X * ((ten2Adjoint V * V) * X) := by
          simp only [Matrix.mul_assoc]
      _ = ten2Adjoint X * ((ten2Adjoint U * U) * X) := by rw [hgram']
      _ = ten2Adjoint X * (ten2Adjoint U * (U * X)) := by
          simp only [Matrix.mul_assoc]
      _ = ten2Adjoint X * (ten2Adjoint U * (1 : Ten2)) := by rw [hUX]
      _ = ten2Adjoint (U * X) := by rw [Matrix.mul_one, ← ten2Adjoint_mul]
      _ = (1 : Ten2) := by rw [hUX, ten2Adjoint_one]
  ·
    calc (V * X) *ᵥ u₁ = V *ᵥ (X *ᵥ u₁) := by rw [Matrix.mulVec_mulVec]
      _ = V *ᵥ jonesE₀ := by rw [hXe₀]
      _ = v₁ := hVe₀
  ·
    calc (V * X) *ᵥ u₂ = V *ᵥ (X *ᵥ u₂) := by rw [Matrix.mulVec_mulVec]
      _ = V *ᵥ jonesE₁ := by rw [hXe₁]
      _ = z • v₂ := hVe₁

theorem exists_jonesUnitary_iff (u₁ u₂ v₁ v₂ : Vec2)
    (hu₁ : isNormalized u₁) (hu₂ : isNormalized u₂)
    (hv₁ : isNormalized v₁) (hv₂ : isNormalized v₂)
    (hind : JonesIndependent u₁ u₂) :
    jonesOverlap u₁ u₂ = jonesOverlap v₁ v₂ ↔
      ∃ T : Ten2, JonesUnitary T ∧ ∃ α₁ α₂ : ℂ,
        ‖α₁‖ = 1 ∧ ‖α₂‖ = 1 ∧
        T *ᵥ u₁ = α₁ • v₁ ∧ T *ᵥ u₂ = α₂ • v₂ := by
  constructor
  ·
    intro hov
    have hov' : ‖jonesInner u₁ u₂‖ = ‖jonesInner v₁ v₂‖ := hov
    obtain ⟨z, hz, hzc⟩ := exists_unit_phase (jonesInner u₁ u₂) (jonesInner v₁ v₂) hov'
    have hgram : jonesGram u₁ u₂ = jonesGram v₁ (z • v₂) :=
      jonesGram_eq u₁ u₂ v₁ v₂ z hu₁ hu₂ hv₁ hv₂ hz hzc
    have hdet : (jonesColMatrix u₁ u₂).det ≠ 0 :=
      jonesIndependent_det_ne_zero u₁ u₂ hind
    obtain ⟨T, hT, hT₁, hT₂⟩ := jonesUnitary_of_equal_gram u₁ u₂ v₁ v₂ z hdet hgram
    refine ⟨T, hT, 1, z, ?_, hz, ?_, hT₂⟩
    · simp
    · simpa using hT₁
  ·
    rintro ⟨T, hT, α₁, α₂, hα₁, hα₂, ht₁, ht₂⟩
    have hpair := jonesInner_of_jonesUnitary hT u₁ u₂
    rw [ht₁, ht₂] at hpair
    have hsplit : jonesInner (α₁ • v₁) (α₂ • v₂) = star α₁ * α₂ * jonesInner v₁ v₂ := by
      simp only [jonesInner, Pi.smul_apply, smul_eq_mul, star_mul]
      ring
    rw [hsplit] at hpair
    show jonesOverlap u₁ u₂ = jonesOverlap v₁ v₂
    rw [jonesOverlap, jonesOverlap, ← hpair]
    simp [hα₁, hα₂]

theorem not_exists_jonesUnitary_of_neq_overlap (u₁ u₂ v₁ v₂ : Vec2)
    (hu₁ : isNormalized u₁) (hu₂ : isNormalized u₂)
    (hv₁ : isNormalized v₁) (hv₂ : isNormalized v₂)
    (hind : JonesIndependent u₁ u₂)
    (hne : jonesOverlap u₁ u₂ ≠ jonesOverlap v₁ v₂) :
    ¬ ∃ T : Ten2, JonesUnitary T ∧ ∃ α₁ α₂ : ℂ,
        ‖α₁‖ = 1 ∧ ‖α₂‖ = 1 ∧
        T *ᵥ u₁ = α₁ • v₁ ∧ T *ᵥ u₂ = α₂ • v₂ := by
  intro h
  have hov : jonesOverlap u₁ u₂ = jonesOverlap v₁ v₂ :=
    (exists_jonesUnitary_iff u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hind).mpr h
  exact hne hov

theorem jonesInner_add_left (u v w : Vec2) :
    jonesInner (u + v) w = jonesInner u w + jonesInner v w := by
  simp only [jonesInner, Pi.add_apply, star_add]
  ring

theorem jonesInner_add_right (u v w : Vec2) :
    jonesInner u (v + w) = jonesInner u v + jonesInner u w := by
  simp only [jonesInner, Pi.add_apply]
  ring

theorem jonesInner_smul_left (c : ℂ) (u v : Vec2) :
    jonesInner (c • u) v = star c * jonesInner u v := by
  simp only [jonesInner, Pi.smul_apply, smul_eq_mul, star_mul]
  ring

theorem jonesInner_smul_right (c : ℂ) (u v : Vec2) :
    jonesInner u (c • v) = c * jonesInner u v := by
  simp only [jonesInner, Pi.smul_apply, smul_eq_mul]
  ring

theorem jonesInner_self_eq (u : Vec2) : jonesInner u u = (jonesNormSqR u : ℂ) := by
  have h1 : jonesInner u u = ((‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 : ℝ) : ℂ) := by
    simp only [jonesInner, Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have h2 : jonesNormSqR u = (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 : ℝ) := by
    simp only [jonesNormSqR, jonesNormSq]
    rw [h1]
    simp only [Complex.ofReal_re]
  rw [h1, h2]

def jonesStd (i : Fin 2) : Vec2 := fun j => if j = i then 1 else 0

theorem jonesInner_std_right (u : Vec2) (i : Fin 2) :
    jonesInner u (jonesStd i) = star (u i) := by
  fin_cases i <;> simp [jonesInner, jonesStd]

theorem jonesInner_of_norm_preserving {T : Ten2}
    (hT : ∀ w : Vec2, jonesNormSqR (T *ᵥ w) = jonesNormSqR w) (u v : Vec2) :
    jonesInner (T *ᵥ u) (T *ᵥ v) = jonesInner u v := by
  have hq : ∀ x : Vec2, jonesInner (T *ᵥ x) (T *ᵥ x) = jonesInner x x := by
    intro x
    calc jonesInner (T *ᵥ x) (T *ᵥ x) = (jonesNormSqR (T *ᵥ x) : ℂ) := jonesInner_self_eq _
      _ = (jonesNormSqR x : ℂ) := by rw [hT x]
      _ = jonesInner x x := (jonesInner_self_eq x).symm
  have e1 : jonesInner (T *ᵥ u) (T *ᵥ v) + jonesInner (T *ᵥ v) (T *ᵥ u)
      = jonesInner u v + jonesInner v u := by
    have h := hq (u + v)
    rw [Matrix.mulVec_add] at h
    simp only [jonesInner_add_left, jonesInner_add_right] at h
    rw [hq u, hq v] at h
    linear_combination h
  have e2 : (Complex.I : ℂ) * jonesInner (T *ᵥ u) (T *ᵥ v)
      + star Complex.I * jonesInner (T *ᵥ v) (T *ᵥ u)
      = (Complex.I : ℂ) * jonesInner u v + star Complex.I * jonesInner v u := by
    have h := hq (u + (Complex.I : ℂ) • v)
    rw [Matrix.mulVec_add] at h
    simp only [jonesInner_add_left, jonesInner_add_right] at h
    rw [hq u, hq ((Complex.I : ℂ) • v)] at h
    rw [Matrix.mulVec_smul] at h
    simp only [jonesInner_smul_left, jonesInner_smul_right] at h
    linear_combination h
  have hkey : (Complex.I - star Complex.I) *
      (jonesInner (T *ᵥ u) (T *ᵥ v) - jonesInner u v) = 0 := by
    linear_combination e2 - star Complex.I * e1
  have hne : (Complex.I - star Complex.I : ℂ) ≠ 0 := by
    simp
  have hz : jonesInner (T *ᵥ u) (T *ᵥ v) - jonesInner u v = 0 :=
    (mul_eq_zero.mp hkey).resolve_left hne
  exact sub_eq_zero.mp hz

theorem mulVec_jonesStd (M : Ten2) (j i : Fin 2) :
    (M *ᵥ jonesStd j) i = M i j := by
  fin_cases j <;> fin_cases i <;>
    simp [jonesStd, Matrix.mulVec_apply_eq_sum]

theorem jonesUnitary_of_pairing {T : Ten2}
    (hT : ∀ u v : Vec2, jonesInner (T *ᵥ u) (T *ᵥ v) = jonesInner u v) :
    JonesUnitary T := by
  have hkey : ∀ v : Vec2, ∀ i : Fin 2,
      ((ten2Adjoint T * T) *ᵥ v) i = v i := by
    intro v i
    have h := hc_ten2Adjoint T (jonesStd i) (T *ᵥ v)
    rw [Matrix.mulVec_mulVec] at h
    rw [hc_eq_jonesInner_swap, hc_eq_jonesInner_swap] at h
    rw [hT v (jonesStd i)] at h
    rw [jonesInner_std_right, jonesInner_std_right] at h
    have h' := congrArg star h
    rw [star_star, star_star] at h'
    exact h'
  ext i j
  have h := hkey (jonesStd j) i
  rw [mulVec_jonesStd] at h
  by_cases hij : i = j
  · subst hij
    rw [h]
    simp [jonesStd]
  · rw [h]
    simp [jonesStd, hij]

theorem ten2_eq_zero_of_mulVec_eq_zero {M : Ten2} {u₁ u₂ : Vec2}
    (h₁ : M *ᵥ u₁ = 0) (h₂ : M *ᵥ u₂ = 0)
    (hdet : (jonesColMatrix u₁ u₂).det ≠ 0) : M = 0 := by
  have hMJ : M * jonesColMatrix u₁ u₂ = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases j
    · simp only [jonesColMatrix_apply_zero']
      rw [← Matrix.mulVec_apply_eq_sum, h₁]
      simp
    · simp only [jonesColMatrix_apply_one']
      rw [← Matrix.mulVec_apply_eq_sum, h₂]
      simp
  calc M = M * (jonesColMatrix u₁ u₂ * ten2_inv (jonesColMatrix u₁ u₂) hdet) := by
        rw [ten2_mul_inv, Matrix.mul_one]
    _ = (M * jonesColMatrix u₁ u₂) * ten2_inv (jonesColMatrix u₁ u₂) hdet := by
        rw [Matrix.mul_assoc]
    _ = 0 := by rw [hMJ, Matrix.zero_mul]

theorem biForwardT_unitary_of_two_unit_efficiencies (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (u₁ u₂ v₁ v₂ : Vec2)
    (hu₁ : isNormalized u₁) (hu₂ : isNormalized u₂)
    (hv₁ : isNormalized v₁) (hv₂ : isNormalized v₂)
    (hind : JonesIndependent u₁ u₂)
    (α₁ α₂ : ℂ)
    (ht₁ : biForwardT cfg p *ᵥ u₁ = α₁ • v₁)
    (ht₂ : biForwardT cfg p *ᵥ u₂ = α₂ • v₂)
    (he₁ : efficiency α₁ = 1) (he₂ : efficiency α₂ = 1) :
    biForwardR cfg p = 0 ∧ JonesUnitary (biForwardT cfg p) := by
  have hR₁ : biForwardR cfg p *ᵥ u₁ = 0 :=
    perfect_efficiency_reflection_vanishes cfg p hk heq u₁ v₁ α₁ hu₁ hv₁ ht₁ he₁
  have hR₂ : biForwardR cfg p *ᵥ u₂ = 0 :=
    perfect_efficiency_reflection_vanishes cfg p hk heq u₂ v₂ α₂ hu₂ hv₂ ht₂ he₂
  have hdet : (jonesColMatrix u₁ u₂).det ≠ 0 := jonesIndependent_det_ne_zero u₁ u₂ hind
  have hR : biForwardR cfg p = 0 := ten2_eq_zero_of_mulVec_eq_zero hR₁ hR₂ hdet
  have hiso : ∀ w : Vec2, jonesNormSqR (biForwardT cfg p *ᵥ w) = jonesNormSqR w :=
    fun w => reflectionless_transmission_is_isometry cfg p hk heq w hR
  exact ⟨hR, jonesUnitary_of_pairing (fun u v => jonesInner_of_norm_preserving hiso u v)⟩

theorem jonesInner_smul_self (c : ℂ) (u : Vec2) :
    jonesInner (c • u) (c • u) = star c * c * jonesInner u u := by
  simp only [jonesInner, Pi.smul_apply, smul_eq_mul, star_mul]
  ring

theorem biForwardT_relative_phase_at_unit_efficiency (cfg : Config) (p : BIParams)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (u₁ u₂ v₁ v₂ : Vec2)
    (hu₁ : isNormalized u₁) (hu₂ : isNormalized u₂)
    (hv₁ : isNormalized v₁) (hv₂ : isNormalized v₂)
    (hind : JonesIndependent u₁ u₂)
    (α₁ α₂ : ℂ)
    (ht₁ : biForwardT cfg p *ᵥ u₁ = α₁ • v₁)
    (ht₂ : biForwardT cfg p *ᵥ u₂ = α₂ • v₂)
    (he₁ : efficiency α₁ = 1) (he₂ : efficiency α₂ = 1) :
    star α₁ * α₂ * jonesInner v₁ v₂ = jonesInner u₁ u₂ := by
  obtain ⟨hR, _⟩ :=
    biForwardT_unitary_of_two_unit_efficiencies cfg p hk heq u₁ u₂ v₁ v₂
      hu₁ hu₂ hv₁ hv₂ hind α₁ α₂ ht₁ ht₂ he₁ he₂
  have hiso : ∀ w : Vec2, jonesNormSqR (biForwardT cfg p *ᵥ w) = jonesNormSqR w :=
    fun w => reflectionless_transmission_is_isometry cfg p hk heq w hR
  have hpair := jonesInner_of_norm_preserving hiso u₁ u₂
  rw [ht₁, ht₂] at hpair
  calc star α₁ * α₂ * jonesInner v₁ v₂ = jonesInner (α₁ • v₁) (α₂ • v₂) := by
        simp only [jonesInner, Pi.smul_apply, smul_eq_mul, star_mul]
        ring
    _ = jonesInner u₁ u₂ := hpair

end JonesOperatorClassification

end GSTC.Scattering
