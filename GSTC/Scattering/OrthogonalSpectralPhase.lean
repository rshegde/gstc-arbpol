/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.

Licensed under the MIT License.

Part of the GSTC formalization of the manuscript
`rshegde/paper-gstc_arbpol_bounds`, Section 3B.1.
-/
module

public import GSTC.Scattering.OrthogonalSpectralNB

public section
set_option autoImplicit false

namespace GSTC.Scattering
namespace OrthogonalSpectralPhase

open scoped Matrix
open BIFeasibility
open MaterialSpace
open BIPolynomials
open ClassFeasibility
open SusceptibilityBudget
open OrthogonalSpectralOptimum
open OrthogonalSpectralPole
open OrthogonalSpectralBridge
open OrthogonalSpectralNB

theorem phaseQ_add_two_pi (c : PhaseCoefficients) (t : ℝ) :
    phaseQ c (t + 2 * Real.pi) = phaseQ c t := by
  unfold phaseQ
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem phaseRx_add_two_pi (c : PhaseCoefficients) (t : ℝ) :
    phaseRx c (t + 2 * Real.pi) = phaseRx c t := by
  unfold phaseRx
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem phaseRy_add_two_pi (c : PhaseCoefficients) (t : ℝ) :
    phaseRy c (t + 2 * Real.pi) = phaseRy c t := by
  unfold phaseRy
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem phaseRz_add_two_pi (c : PhaseCoefficients) (t : ℝ) :
    phaseRz c (t + 2 * Real.pi) = phaseRz c t := by
  unfold phaseRz
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem phaseMinimum_add_two_pi (cfg : Config) (c : PhaseCoefficients) (t : ℝ) :
    phaseMinimum cfg c (t + 2 * Real.pi) = phaseMinimum cfg c t := by
  unfold phaseMinimum
  rw [phaseQ_add_two_pi, phaseRx_add_two_pi, phaseRy_add_two_pi, phaseRz_add_two_pi]

theorem phaseMinimum_sub_two_pi (cfg : Config) (c : PhaseCoefficients) (t : ℝ) :
    phaseMinimum cfg c (t - 2 * Real.pi) = phaseMinimum cfg c t := by
  have h := phaseMinimum_add_two_pi cfg c (t - 2 * Real.pi)
  rw [show t - 2 * Real.pi + 2 * Real.pi = t by ring] at h
  exact h.symm

theorem phaseMinimum_add_two_pi_int (cfg : Config) (c : PhaseCoefficients)
    (t : ℝ) (k : ℤ) :
    phaseMinimum cfg c (t + 2 * Real.pi * k) = phaseMinimum cfg c t := by
  by_cases hk : 0 ≤ k
  · refine Int.leInduction (motive := fun n _ => phaseMinimum cfg c (t + 2 * Real.pi * n)
      = phaseMinimum cfg c t) ?_ ?_ k hk
    · simp
    · intro n _ ih
      have hrw : t + 2 * Real.pi * ((n + 1 : ℤ) : ℝ)
          = (t + 2 * Real.pi * (n : ℝ)) + 2 * Real.pi := by
        push_cast
        ring
      rw [hrw, phaseMinimum_add_two_pi, ih]
  · refine Int.leInductionDown (motive := fun n _ => phaseMinimum cfg c (t + 2 * Real.pi * n)
      = phaseMinimum cfg c t) ?_ ?_ k (le_of_not_ge hk)
    · simp
    · intro n _ ih
      have hrw : t + 2 * Real.pi * ((n - 1 : ℤ) : ℝ)
          = (t + 2 * Real.pi * (n : ℝ)) - 2 * Real.pi := by
        push_cast
        ring
      rw [hrw, phaseMinimum_sub_two_pi, ih]

theorem exists_phase_eq_add_two_pi_mul (t : ℝ) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 2 * Real.pi ∧ ∃ k : ℤ, t = s + 2 * Real.pi * k := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfloor : ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) ≤ t / (2 * Real.pi) := Int.floor_le _
  have hceil : t / (2 * Real.pi) < ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  refine ⟨t - 2 * Real.pi * ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ), ?_, ?_, ⌊t / (2 * Real.pi)⌋, ?_⟩
  · have h' : 2 * Real.pi * ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) ≤ t := by
      have h2 := (le_div_iff₀ hpi).mp hfloor
      rw [show (((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ)) * (2 * Real.pi)
          = 2 * Real.pi * ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) by ring] at h2
      exact h2
    rw [sub_nonneg]
    exact h'
  · have h' : t < 2 * Real.pi * ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) + 2 * Real.pi := by
      have h2 := (div_lt_iff₀ hpi).mp hceil
      rw [show ((((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ)) + 1) * (2 * Real.pi)
          = 2 * Real.pi * ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) + 2 * Real.pi by ring] at h2
      exact h2
    rw [sub_le_iff_le_add]
    simpa only [add_comm] using h'.le
  · ring

theorem phaseMinimum_continuous (cfg : Config) (c : PhaseCoefficients) :
    Continuous (phaseMinimum cfg c) := by
  unfold phaseMinimum
  have hQ : Continuous fun t => phaseQ c t := by
    unfold phaseQ
    fun_prop
  have hRx : Continuous fun t => phaseRx c t := by
    unfold phaseRx
    fun_prop
  have hRy : Continuous fun t => phaseRy c t := by
    unfold phaseRy
    fun_prop
  have hRz : Continuous fun t => phaseRz c t := by
    unfold phaseRz
    fun_prop
  have hsqc : Continuous fun t => phaseRx c t ^ 2 + phaseRz c t ^ 2 := by
    fun_prop
  have hsqrt : Continuous fun t => Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2) :=
    Real.continuous_sqrt.comp hsqc
  have habs : Continuous fun t => |phaseRy c t| := by
    fun_prop
  have hmax : Continuous fun t => max
      (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
        * Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2))
      (spectralChiralScale cfg * |phaseRy c t|) := by
    fun_prop
  have hden : Continuous fun t => 1 + |phaseQ c t| := by
    fun_prop
  have hne : ∀ x : ℝ, 1 + |phaseQ c x| ≠ 0 := by
    intro x hx
    have h1 : (0 : ℝ) ≤ |phaseQ c x| := abs_nonneg _
    linarith
  have hnum : Continuous fun t => freeSpaceK0 cfg * 2
      * max (max (spectralElectricScale cfg) (spectralMagneticScale cfg)
          * Real.sqrt (phaseRx c t ^ 2 + phaseRz c t ^ 2))
        (spectralChiralScale cfg * |phaseRy c t|) := by
    fun_prop
  exact hnum.div hden hne

theorem biPhaseMinimum_exists (cfg : Config) (c : PhaseCoefficients) :
    ∃ t₀ : ℝ, ∀ t : ℝ, phaseMinimum cfg c t₀ ≤ phaseMinimum cfg c t := by
  have hcont : Continuous (phaseMinimum cfg c) := phaseMinimum_continuous cfg c
  have hcomp : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi)) := isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) (2 * Real.pi)).Nonempty := ⟨0, by norm_num, by positivity⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
  have hall : ∀ y ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      phaseMinimum cfg c t₀ ≤ phaseMinimum cfg c y :=
    (Filter.eventually_principal).1 hmin
  refine ⟨t₀, ?_⟩
  intro t
  obtain ⟨s, hs0, hs1, k, hk⟩ := exists_phase_eq_add_two_pi_mul t
  have h1 : phaseMinimum cfg c t₀ ≤ phaseMinimum cfg c s := hall s ⟨hs0, hs1⟩
  have h2 : phaseMinimum cfg c t = phaseMinimum cfg c s := by
    rw [hk]
    exact phaseMinimum_add_two_pi_int cfg c s k
  linarith

theorem bi_global_lower_bound (cfg : Config) (c : PhaseCoefficients) (t₀ : ℝ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (h₁ : c.q_c ^ 2 + c.a_x ^ 2 + c.a_y ^ 2 + c.a_z ^ 2 = 1)
    (h₂ : c.q_s ^ 2 + c.b_x ^ 2 + c.b_y ^ 2 + c.b_z ^ 2 = 1)
    (h₃ : c.q_c * c.q_s + c.a_x * c.b_x + c.a_y * c.b_y + c.a_z * c.b_z = 0)
    (hmin : ∀ t : ℝ, phaseMinimum cfg c t₀ ≤ phaseMinimum cfg c t)
    (t α : ℝ) (p : BIParams) (hp : biForwardT cfg p = phaseTransmission c t α) :
    phaseMinimum cfg c t₀ ≤ spectralTotalBudget cfg (assign p) := by
  have h1 := fixedPhase_spectral_optimum_all cfg c t α hk heq (phaseUnit c h₁ h₂ h₃ t) p hp
  exact le_trans (hmin t) h1

theorem biPhaseMinimum_attained_by_sheet (cfg : Config) (c : PhaseCoefficients)
    (t₀ : ℝ)
    (h₁ : c.q_c ^ 2 + c.a_x ^ 2 + c.a_y ^ 2 + c.a_z ^ 2 = 1)
    (h₂ : c.q_s ^ 2 + c.b_x ^ 2 + c.b_y ^ 2 + c.b_z ^ 2 = 1)
    (h₃ : c.q_c * c.q_s + c.a_x * c.b_x + c.a_y * c.b_y + c.a_z * c.b_z = 0) :
    ∃ (α₀ : ℝ) (p : BIParams), biForwardT cfg p = phaseTransmission c t₀ α₀ ∧
      spectralTotalBudget cfg (assign p) = phaseMinimum cfg c t₀ := by
  have hsphere : phaseQ c t₀ ^ 2 + phaseRx c t₀ ^ 2 + phaseRy c t₀ ^ 2
      + phaseRz c t₀ ^ 2 = 1 := phaseUnit c h₁ h₂ h₃ t₀
  by_cases hq : 0 ≤ phaseQ c t₀
  · obtain ⟨p, hp, hb⟩ := fixedPhase_spectral_optimum_attained_zero cfg c t₀ hsphere hq
    exact ⟨0, p, hp, hb⟩
  · obtain ⟨p, hp, hb⟩ := fixedPhase_spectral_optimum_attained_pi cfg c t₀ hsphere
      (lt_of_not_ge hq)
    exact ⟨Real.pi, p, hp, hb⟩

theorem nb_admissible_iff (cfg : Config) (c : PhaseCoefficients) (t α : ℝ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (h₁ : c.q_c ^ 2 + c.a_x ^ 2 + c.a_y ^ 2 + c.a_z ^ 2 = 1)
    (h₂ : c.q_s ^ 2 + c.b_x ^ 2 + c.b_y ^ 2 + c.b_z ^ 2 = 1)
    (h₃ : c.q_c * c.q_s + c.a_x * c.b_x + c.a_y * c.b_y + c.a_z * c.b_z = 0) :
    (∃ z : ℂ, ∃ p : BIParams, ‖z‖ = 1 ∧ NoCoupling p ∧
        biForwardT cfg p = z • phaseTransmission c t α)
      ↔ phaseRy c t = 0 :=
  nb_phaseFamily_feasible_iff cfg c t α hk heq (phaseUnit c h₁ h₂ h₃ t)

theorem biMinimum_eq_phaseFamily (cfg : Config) (c : PhaseCoefficients) (t₀ : ℝ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (h₁ : c.q_c ^ 2 + c.a_x ^ 2 + c.a_y ^ 2 + c.a_z ^ 2 = 1)
    (h₂ : c.q_s ^ 2 + c.b_x ^ 2 + c.b_y ^ 2 + c.b_z ^ 2 = 1)
    (h₃ : c.q_c * c.q_s + c.a_x * c.b_x + c.a_y * c.b_y + c.a_z * c.b_z = 0)
    (hmin : ∀ t : ℝ, phaseMinimum cfg c t₀ ≤ phaseMinimum cfg c t) :
    (∀ (t α : ℝ) (p : BIParams), biForwardT cfg p = phaseTransmission c t α →
        phaseMinimum cfg c t₀ ≤ spectralTotalBudget cfg (assign p)) ∧
      (∀ t : ℝ, phaseMinimum cfg c t₀ ≤ phaseMinimum cfg c t) ∧
      (∃ (α₀ : ℝ) (p : BIParams), biForwardT cfg p = phaseTransmission c t₀ α₀ ∧
        spectralTotalBudget cfg (assign p) = phaseMinimum cfg c t₀) := by
  refine ⟨fun t α p hp => bi_global_lower_bound cfg c t₀ hk heq h₁ h₂ h₃ hmin t α p hp,
    hmin, ?_⟩
  obtain ⟨α₀, p, hp, hb⟩ := biPhaseMinimum_attained_by_sheet cfg c t₀ h₁ h₂ h₃
  exact ⟨α₀, p, hp, hb⟩

@[expose] def nbAdmissible (c : PhaseCoefficients) : Set ℝ := {t | phaseRy c t = 0}

theorem continuous_phaseRy (c : PhaseCoefficients) : Continuous (phaseRy c) := by
  unfold phaseRy
  fun_prop

theorem phaseRy_sub_two_pi (c : PhaseCoefficients) (t : ℝ) :
    phaseRy c (t - 2 * Real.pi) = phaseRy c t := by
  have h := phaseRy_add_two_pi c (t - 2 * Real.pi)
  rw [show t - 2 * Real.pi + 2 * Real.pi = t by ring] at h
  exact h.symm

theorem phaseRy_add_two_pi_int (c : PhaseCoefficients) (t : ℝ) (k : ℤ) :
    phaseRy c (t + 2 * Real.pi * k) = phaseRy c t := by
  by_cases hk : 0 ≤ k
  · refine Int.leInduction (motive := fun n _ => phaseRy c (t + 2 * Real.pi * n)
      = phaseRy c t) ?_ ?_ k hk
    · simp
    · intro n _ ih
      have hrw : t + 2 * Real.pi * ((n + 1 : ℤ) : ℝ)
          = (t + 2 * Real.pi * (n : ℝ)) + 2 * Real.pi := by
        push_cast
        ring
      rw [hrw, phaseRy_add_two_pi, ih]
  · refine Int.leInductionDown (motive := fun n _ => phaseRy c (t + 2 * Real.pi * n)
      = phaseRy c t) ?_ ?_ k (le_of_not_ge hk)
    · simp
    · intro n _ ih
      have hrw : t + 2 * Real.pi * ((n - 1 : ℤ) : ℝ)
          = (t + 2 * Real.pi * (n : ℝ)) - 2 * Real.pi := by
        push_cast
        ring
      rw [hrw, phaseRy_sub_two_pi, ih]

theorem nbAdmissible_nonempty (c : PhaseCoefficients) : (nbAdmissible c).Nonempty := by
  have hcont : Continuous (phaseRy c) := continuous_phaseRy c
  have hg0 : phaseRy c 0 = c.a_y := by
    unfold phaseRy
    rw [Real.cos_zero, Real.sin_zero]
    ring
  have hgpi : phaseRy c Real.pi = -c.a_y := by
    unfold phaseRy
    rw [Real.cos_pi, Real.sin_pi]
    ring
  by_cases h0 : c.a_y = 0
  · refine ⟨0, ?_⟩
    simp [nbAdmissible, hg0, h0]
  · rcases lt_or_gt_of_ne h0 with hneg | hpos
    ·
      have himem : 0 ∈ Set.Icc (phaseRy c 0) (phaseRy c Real.pi) := by
        rw [hg0, hgpi]
        constructor <;> linarith
      have himem' : Set.Icc (phaseRy c 0) (phaseRy c Real.pi)
          ⊆ phaseRy c '' Set.Icc (0 : ℝ) Real.pi := by
        exact intermediate_value_Icc (a := (0 : ℝ)) (b := Real.pi) (by positivity)
          hcont.continuousOn
      obtain ⟨t, ht, hz⟩ := himem' himem
      refine ⟨t, ?_⟩
      simp [nbAdmissible, hz]
    ·
      have himem : 0 ∈ Set.Icc (phaseRy c Real.pi) (phaseRy c 0) := by
        rw [hgpi, hg0]
        constructor <;> linarith
      have himem' : Set.Icc (phaseRy c Real.pi) (phaseRy c 0)
          ⊆ phaseRy c '' Set.Icc (0 : ℝ) Real.pi := by
        exact intermediate_value_Icc' (a := (0 : ℝ)) (b := Real.pi) (by positivity)
          hcont.continuousOn
      obtain ⟨t, ht, hz⟩ := himem' himem
      refine ⟨t, ?_⟩
      simp [nbAdmissible, hz]

theorem nbAdmissible_closed (c : PhaseCoefficients) : IsClosed (nbAdmissible c) := by
  unfold nbAdmissible
  exact (isClosed_singleton : IsClosed ({0} : Set ℝ)).preimage (continuous_phaseRy c)

theorem nbPhaseMinimum_exists (cfg : Config) (c : PhaseCoefficients) :
    ∃ t₀ : ℝ, nbAdmissible c t₀ ∧
      ∀ t : ℝ, nbAdmissible c t → phaseMinimum cfg c t₀ ≤ phaseMinimum cfg c t := by
  have hcont : Continuous (phaseMinimum cfg c) := phaseMinimum_continuous cfg c
  have hIcc : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    CompactIccSpace.isCompact_Icc
  have hK : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi) ∩ nbAdmissible c) :=
    hIcc.inter_right (nbAdmissible_closed c)
  have hne : (Set.Icc (0 : ℝ) (2 * Real.pi) ∩ nbAdmissible c).Nonempty := by
    obtain ⟨t, ht⟩ := nbAdmissible_nonempty c
    obtain ⟨s, hs0, hs1, k, hk⟩ := exists_phase_eq_add_two_pi_mul t
    refine ⟨s, ?_⟩
    have hadm : phaseRy c s = phaseRy c t := by
      rw [hk, phaseRy_add_two_pi_int]
    exact ⟨⟨hs0, hs1⟩, by show phaseRy c s = 0; rw [hadm]; exact ht⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have hall : ∀ y ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∩ nbAdmissible c,
      phaseMinimum cfg c t₀ ≤ phaseMinimum cfg c y :=
    (Filter.eventually_principal).1 hmin
  refine ⟨t₀, ht₀.2, ?_⟩
  intro t ht
  obtain ⟨s, hs0, hs1, k, hk⟩ := exists_phase_eq_add_two_pi_mul t
  have hadm : phaseRy c s = phaseRy c t := by
    rw [hk, phaseRy_add_two_pi_int]
  have hmem : s ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∩ nbAdmissible c :=
    ⟨⟨hs0, hs1⟩, by show phaseRy c s = 0; rw [hadm]; exact ht⟩
  have h1 : phaseMinimum cfg c t₀ ≤ phaseMinimum cfg c s := hall s hmem
  have h2 : phaseMinimum cfg c s = phaseMinimum cfg c t := by
    rw [hk]
    exact (phaseMinimum_add_two_pi_int cfg c s k).symm
  linarith

theorem nbMinimum_eq_phaseFamily (cfg : Config) (c : PhaseCoefficients) (t₀ : ℝ)
    (hk : cfg.kPar = 0) (heq : cfg.lower.eta = cfg.upper.eta)
    (h₁ : c.q_c ^ 2 + c.a_x ^ 2 + c.a_y ^ 2 + c.a_z ^ 2 = 1)
    (h₂ : c.q_s ^ 2 + c.b_x ^ 2 + c.b_y ^ 2 + c.b_z ^ 2 = 1)
    (h₃ : c.q_c * c.q_s + c.a_x * c.b_x + c.a_y * c.b_y + c.a_z * c.b_z = 0)
    (hadm : nbAdmissible c t₀)
    (hmin : ∀ t : ℝ, nbAdmissible c t → phaseMinimum cfg c t₀ ≤ phaseMinimum cfg c t) :
    (∀ (t α : ℝ) (p : BIParams), NoCoupling p →
        biForwardT cfg p = phaseTransmission c t α →
        phaseMinimum cfg c t₀ ≤ spectralTotalBudget cfg (assign p)) ∧
      (∀ t : ℝ, nbAdmissible c t → phaseMinimum cfg c t₀ ≤ phaseMinimum cfg c t) ∧
      (∃ (α₀ : ℝ) (p : BIParams), NoCoupling p ∧
          biForwardT cfg p = phaseTransmission c t₀ α₀ ∧
          spectralTotalBudget cfg (assign p) = phaseMinimum cfg c t₀) := by
  have hry₀ : phaseRy c t₀ = 0 := hadm
  have hsphere₀ : phaseQ c t₀ ^ 2 + phaseRx c t₀ ^ 2 + phaseRy c t₀ ^ 2
      + phaseRz c t₀ ^ 2 = 1 := phaseUnit c h₁ h₂ h₃ t₀
  refine ⟨?_, hmin, ?_⟩
  · intro t α p hnc hp
    have hry : phaseRy c t = 0 := by
      have hz : biForwardT cfg p = (1 : ℂ) • phaseTransmission c t α := by
        simpa using hp
      have := (nb_admissible_iff cfg c t α hk heq h₁ h₂ h₃).mp
        ⟨1, p, by simp, hnc, hz⟩
      exact this
    have hfix := fixedPhase_spectral_optimum_all cfg c t α hk heq (phaseUnit c h₁ h₂ h₃ t) p hp
    exact le_trans (hmin t hry) hfix
  · by_cases hq : 0 ≤ phaseQ c t₀
    · have hα : phaseCayleyScale c t₀ 0 ≠ 0 := by
        rw [phaseCayleyScale_zero]
        have : (0 : ℝ) < 1 + phaseQ c t₀ := by linarith
        exact ne_of_gt this
      refine ⟨0, phaseSheet cfg c t₀ 0, ?_,
        phaseSheet_forward cfg c t₀ 0 hsphere₀ hα, phaseBudget_attained_zero cfg c t₀ hq⟩
      rw [phaseSheet, spectralLocusSheet_eq]
      simp [NoCoupling, hry₀]
    · have hα : phaseCayleyScale c t₀ Real.pi ≠ 0 := by
        rw [phaseCayleyScale_pi]
        have : (phaseQ c t₀ - 1 : ℝ) < 0 := by linarith
        exact ne_of_lt this
      refine ⟨Real.pi, phaseSheet cfg c t₀ Real.pi, ?_,
        phaseSheet_forward cfg c t₀ Real.pi hsphere₀ hα,
        phaseBudget_attained_pi cfg c t₀ (lt_of_not_ge hq)⟩
      rw [phaseSheet, spectralLocusSheet_eq]
      simp [NoCoupling, hry₀]

end OrthogonalSpectralPhase
end GSTC.Scattering
