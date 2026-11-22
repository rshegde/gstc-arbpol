/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIRankOneCompletion
public import GSTC.Scattering.BIRankOneEndpoint

public section
set_option autoImplicit false

namespace GSTC.Scattering.BIRankOneTheorem

open GSTC.Scattering
open BIRankOneCompletion BIRankOneEndpoint BIInverse
open scoped Matrix

theorem sym_entries {M : Ten2} (h : M.transpose = M) (i j : Fin 2) : M i j = M j i := by
  have := congrArg (fun N => N i j) h
  simpa [Matrix.transpose_apply] using this.symm

theorem map_star_of_blocks (X Z Y : Ten2) (hZ : Z.transpose = Z) :
    (Z * X.conjTranspose + X.transpose * Y.conjTranspose).map star
      = Z.conjTranspose * X.transpose + X.conjTranspose * Y.transpose := by
  ext i j
  simp [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two]
  rw [sym_entries hZ i 0, sym_entries hZ i 1]

theorem mixed_of_block (X Z Y : Ten2) (hZ : Z.transpose = Z) (hY : Y.transpose = Y)
    (h : Z * X.conjTranspose + X.transpose * Y.conjTranspose = 0) :
    X.conjTranspose * Y + Z.conjTranspose * X.transpose = 0 := by
  have hc := congrArg (fun M => M.map star) h
  rw [map_star_of_blocks X Z Y hZ, hY] at hc
  simpa [add_comm] using hc

theorem rank_one_completion_iff
    (X Z Y : Ten2) (n : Vec2) (d : ℝ)
    (hX : X.det ≠ 0) (hn : star n ⬝ᵥ n = 1) (hd : 0 ≤ d)
    (hdefect : 1 - X.transpose * X.map star = (d : ℂ) • projection n) :
    ((completion X Z Y).transpose = completion X Z Y ∧
      (completion X Z Y).conjTranspose * (completion X Z Y) = 1)
    ↔
    (∃ θ : ℝ,
      Z = (Complex.exp ((θ : ℂ) * Complex.I) * (Real.sqrt d : ℂ)) • symmetricOuter n ∧
      Y = forcedY X Z) := by
  constructor
  · rintro ⟨hsym, hunit⟩
    obtain ⟨hZsym, hYsym⟩ := (completion_symmetric_iff X Z Y).mp hsym
    obtain ⟨b11, b12, b21, b22⟩ := (completion_unitary_iff X Z Y).mp hunit
    have hgram : Z * Z.conjTranspose = (d : ℂ) • projection n := by
      have hA : Z * Z.conjTranspose = 1 - X.transpose * X.map star :=
        eq_sub_of_add_eq b11
      exact hA.trans hdefect
    obtain ⟨θ, hZ⟩ := symmetric_rank_one_phase Z n d hn hZsym hgram
    refine ⟨θ, hZ, ?_⟩
    have hmix : X.conjTranspose * Y + Z.conjTranspose * X.transpose = 0 :=
      mixed_of_block X Z Y hZsym hYsym b12
    exact (mixed_equation_iff X Z Y hX).mp hmix
  · rintro ⟨θ, hZ, hY⟩
    obtain ⟨hZsym', hgram'⟩ := phase_rank_one_gram n d θ hn hd
    have hZsym : Z.transpose = Z := by
      rw [hZ]; simpa using hZsym'
    have hgram : Z * Z.conjTranspose = (d : ℂ) • projection n := by
      rw [hZ]; simpa using hgram'
    have hfull : Z * Z.conjTranspose + X.transpose * X.map star = 1 := by
      rw [hgram, ← hdefect]
      exact sub_add_cancel (1 : Ten2) (X.transpose * X.map star)
    obtain ⟨hsym, hunit⟩ := completion_from_reflection_gram X Z hX hZsym hfull
    refine ⟨?_, ?_⟩
    · rw [hY]; exact hsym
    · rw [hY]; exact hunit

theorem rank_one_completion_iff_explicit
    (X Z Y : Ten2) (n : Vec2) (d : ℝ)
    (hX : X.det ≠ 0) (hn : star n ⬝ᵥ n = 1) (hd : 0 ≤ d)
    (hdefect : 1 - X.transpose * X.map star = (d : ℂ) • projection n) :
    ((completion X Z Y).transpose = completion X Z Y ∧
      (completion X Z Y).conjTranspose * (completion X Z Y) = 1)
    ↔
    (∃ θ : ℝ,
      Z = (Complex.exp ((θ : ℂ) * Complex.I) * (Real.sqrt d : ℂ)) • symmetricOuter n ∧
      Y = -((X.transpose).map star)⁻¹ * Z.map star * X.transpose) := by
  have hmain := rank_one_completion_iff X Z Y n d hX hn hd hdefect
  rw [hmain]
  constructor
  · rintro ⟨θ, hZ, hY⟩
    have hZs : Z.transpose = Z := by
      rw [hZ]; simp [Matrix.transpose_smul, symmetricOuter_symmetric]
    refine ⟨θ, hZ, ?_⟩
    exact hY.trans (forcedY_eq_requested X Z hZs)
  · rintro ⟨θ, hZ, hY⟩
    have hZs : Z.transpose = Z := by
      rw [hZ]; simp [Matrix.transpose_smul, symmetricOuter_symmetric]
    refine ⟨θ, hZ, ?_⟩
    exact hY.trans (forcedY_eq_requested X Z hZs).symm

theorem endpoint_zero (X Z Y : Ten2) (hX : X.det ≠ 0)
    (hdefect0 : X.transpose * X.map star = 1)
    (hsym : (completion X Z Y).transpose = completion X Z Y)
    (hunit : (completion X Z Y).conjTranspose * (completion X Z Y) = 1) :
    Z = 0 ∧ Y = 0 := by
  obtain ⟨hZsym, hYsym⟩ := (completion_symmetric_iff X Z Y).mp hsym
  obtain ⟨b11, b12, b21, b22⟩ := (completion_unitary_iff X Z Y).mp hunit
  have hgram0 : Z * Z.conjTranspose = 0 := by
    have hA : Z * Z.conjTranspose = 1 - X.transpose * X.map star :=
      eq_sub_of_add_eq b11
    rw [hdefect0, sub_self] at hA
    exact hA
  have hZ : Z = 0 := gram_eq_zero_imp Z hgram0
  have hY : Y = 0 := by
    have h12 : X.transpose * Y.conjTranspose = 0 := by
      rw [hZ, Matrix.zero_mul] at b12
      simpa using b12
    exact mixed_eq_zero_imp X Y hX h12
  exact ⟨hZ, hY⟩

theorem endpoint_unique (X : Ten2) (hX : X.det ≠ 0)
    (hdefect0 : X.transpose * X.map star = 1) :
    ∃! S : Ten2 × Ten2,
      (completion X S.1 S.2).transpose = completion X S.1 S.2 ∧
      (completion X S.1 S.2).conjTranspose * (completion X S.1 S.2) = 1 := by
  have hgram0 : (0 : Ten2) * (0 : Ten2).conjTranspose
      + X.transpose * X.map star = 1 := by
    rw [Matrix.zero_mul, zero_add]; exact hdefect0
  obtain ⟨hsym0, hunit0⟩ := completion_from_reflection_gram X 0 hX (by simp) hgram0
  have hforced0 : forcedY X 0 = 0 := by simp [forcedY]
  refine ⟨(0, 0), ?_, ?_⟩
  · rw [hforced0] at hsym0 hunit0
    exact ⟨hsym0, hunit0⟩
  · rintro ⟨Z, Y⟩ ⟨hsym, hunit⟩
    obtain ⟨hZ, hY⟩ := endpoint_zero X Z Y hX hdefect0 hsym hunit
    simp [hZ, hY]

theorem rank_one_completion_has_bi_params
    (cfg : Config) (X Z : Ten2) (n : Vec2) (d : ℝ) (θ : ℝ)
    (hX : X.det ≠ 0) (hn : star n ⬝ᵥ n = 1) (hd : 0 ≤ d)
    (hdefect : 1 - X.transpose * X.map star = (d : ℂ) • projection n)
    (hZ : Z = (Complex.exp ((θ : ℂ) * Complex.I) * (Real.sqrt d : ℂ)) • symmetricOuter n)
    (hp : IsUnit ((1 + Theta * completion X Z (forcedY X Z)).det)) :
    ∃! p : BIParams, biPowerResponse4 cfg p = completion X Z (forcedY X Z) := by
  obtain ⟨hZsym', hgram'⟩ := phase_rank_one_gram n d θ hn hd
  have hZsym : Z.transpose = Z := by
    rw [hZ]; simpa using hZsym'
  have hgram : Z * Z.conjTranspose = (d : ℂ) • projection n := by
    rw [hZ]; simpa using hgram'
  have hfull : Z * Z.conjTranspose + X.transpose * X.map star = 1 := by
    rw [hgram, ← hdefect]
    exact sub_add_cancel (1 : Ten2) (X.transpose * X.map star)
  obtain ⟨hsym, hunit⟩ := completion_from_reflection_gram X Z hX hZsym hfull
  exact bi_inverse_complete cfg (completion X Z (forcedY X Z)) hsym hunit hp

end GSTC.Scattering.BIRankOneTheorem
