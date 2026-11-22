/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.NBClass

public section

namespace GSTC.Scattering

open scoped Matrix
open scoped ComplexConjugate

theorem lossless_outgoing_unique (cfg : Config) (s : Side) (sus : Susceptibilities)
    (eI eR₁ eT₁ eR₂ eT₂ : Vec2) (hk : cfg.kPar = 0)
    (hloss : sus.Lossless) (hem : chiTT sus.em = 0) (hme : chiTT sus.me = 0)
    (hmed : identicalMedia cfg s)
    (h₁ : gstcSatisfied cfg s sus eI eR₁ eT₁)
    (h₂ : gstcSatisfied cfg s sus eI eR₂ eT₂) :
    eR₁ = eR₂ ∧ eT₁ = eT₂ := by
  have hrel₁ := nb_action cfg s sus eI eR₁ eT₁ hk hem hme hmed h₁
  have hrel₂ := nb_action cfg s sus eI eR₂ eT₂ hk hem hme hmed h₂
  let Δr : Vec2 := eR₁ - eR₂
  let Δt : Vec2 := eT₁ - eT₂

  have hRΔ : (0 : Vec2) - Δr - Δt
      = eoResponseScale cfg ((Wave.medium cfg s .incident).eta)
          • ((chiTT sus.ee) *ᵥ ((0 : Vec2) + Δr + Δt)) := by
    calc (0 : Vec2) - Δr - Δt
        = (eI - eR₁ - eT₁) - (eI - eR₂ - eT₂) := by
          ext i
          simp only [Pi.sub_apply, Pi.zero_apply, Δr, Δt]
          ring
      _ = eoResponseScale cfg ((Wave.medium cfg s .incident).eta)
          • ((chiTT sus.ee) *ᵥ ((eI + eR₁ + eT₁) - (eI + eR₂ + eT₂))) := by
          rw [hrel₁.1, hrel₂.1, ← smul_sub, ← Matrix.mulVec_sub]
      _ = eoResponseScale cfg ((Wave.medium cfg s .incident).eta)
          • ((chiTT sus.ee) *ᵥ ((0 : Vec2) + Δr + Δt)) := by
          have hX : (eI + eR₁ + eT₁) - (eI + eR₂ + eT₂) = (0 : Vec2) + Δr + Δt := by
            ext i
            simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Δr, Δt]
            ring
          rw [hX]

  have hMΔ : (0 : Vec2) + Δr - Δt
      = moResponseScale cfg ((Wave.medium cfg s .incident).eta)
          • ((ncross * (chiTT sus.mm * ncross)) *ᵥ ((0 : Vec2) - Δr + Δt)) := by
    calc (0 : Vec2) + Δr - Δt
        = (eI + eR₁ - eT₁) - (eI + eR₂ - eT₂) := by
          ext i
          simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Δr, Δt]
          ring
      _ = moResponseScale cfg ((Wave.medium cfg s .incident).eta)
          • ((ncross * (chiTT sus.mm * ncross))
              *ᵥ ((eI - eR₁ + eT₁) - (eI - eR₂ + eT₂))) := by
          rw [hrel₁.2, hrel₂.2, ← smul_sub, ← Matrix.mulVec_sub]
      _ = moResponseScale cfg ((Wave.medium cfg s .incident).eta)
          • ((ncross * (chiTT sus.mm * ncross)) *ᵥ ((0 : Vec2) - Δr + Δt)) := by
          have hX : (eI - eR₁ + eT₁) - (eI - eR₂ + eT₂) = (0 : Vec2) - Δr + Δt := by
            ext i
            simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Δr, Δt]
            ring
          rw [hX]

  have hΔ : gstcSatisfied cfg s sus 0 Δr Δt :=
    nb_action_implies_gstc cfg s sus 0 Δr Δt hk hem hme hmed hRΔ hMΔ

  have hbal := power_balance_jones_identical cfg s sus 0 Δr Δt hk hloss hΔ hmed
  have hn₁ := jonesNormSqR_nonneg Δr
  have hn₂ := jonesNormSqR_nonneg Δt
  have hz₁ : jonesNormSqR Δr = 0 := by
    have hzero : jonesNormSqR (0 : Vec2) = 0 := by
      simp [jonesNormSqR_eq]
    linarith
  have hz₂ : jonesNormSqR Δt = 0 := by
    have hzero : jonesNormSqR (0 : Vec2) = 0 := by
      simp [jonesNormSqR_eq]
    linarith
  have hΔr : Δr = 0 := (jonesNormSqR_eq_zero_iff Δr).mp hz₁
  have hΔt : Δt = 0 := (jonesNormSqR_eq_zero_iff Δt).mp hz₂
  constructor
  · exact sub_eq_zero.mp hΔr
  · exact sub_eq_zero.mp hΔt

theorem ncross_mul_neg_ncross_mul (H : Ten2) :
    ncross * (-(ncross * (H * ncross)) * ncross) = -H := by
  calc ncross * (-(ncross * (H * ncross)) * ncross)
      = (ncross * (-(ncross * (H * ncross)))) * ncross := by rw [← Matrix.mul_assoc]
    _ = (-(ncross * (ncross * (H * ncross)))) * ncross := by rw [Matrix.mul_neg]
    _ = -((ncross * (ncross * (H * ncross))) * ncross) := by rw [Matrix.neg_mul]
    _ = -((-(H * ncross)) * ncross) := by rw [ncross_sq (H * ncross)]
    _ = -(-((H * ncross) * ncross)) := by rw [Matrix.neg_mul]
    _ = (H * ncross) * ncross := by simp only [neg_neg]
    _ = H * (ncross * ncross) := by rw [Matrix.mul_assoc]
    _ = H * (-(1 : Ten2)) := by rw [ncross_sq']
    _ = -(H * 1) := by rw [Matrix.mul_neg]
    _ = -H := by rw [Matrix.mul_one]

theorem mul_apply_two (A B : Ten2) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem ncross_mul_ncross_entries (A : Ten2) :
    (ncross * (A * ncross)) 0 0 = -(A 1 1) ∧
    (ncross * (A * ncross)) 0 1 = A 1 0 ∧
    (ncross * (A * ncross)) 1 0 = A 0 1 ∧
    (ncross * (A * ncross)) 1 1 = -(A 0 0) := by
  simp [mul_apply_two, ncross, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]

theorem ncross_mul_ncross_symmetric (A : Ten2) (hA : ∀ i j, A i j = A j i) :
    ∀ i j, (ncross * (A * ncross)) i j = (ncross * (A * ncross)) j i := by
  intro i j
  obtain ⟨h00, h01, h10, h11⟩ := ncross_mul_ncross_entries A
  fin_cases i
  · fin_cases j
    · show (ncross * (A * ncross)) 0 0 = (ncross * (A * ncross)) 0 0
      rw [h00]
    · show (ncross * (A * ncross)) 0 1 = (ncross * (A * ncross)) 1 0
      rw [h01, h10, hA 0 1]
  · fin_cases j
    · show (ncross * (A * ncross)) 1 0 = (ncross * (A * ncross)) 0 1
      rw [h10, h01, hA 0 1]
    · show (ncross * (A * ncross)) 1 1 = (ncross * (A * ncross)) 1 1
      rw [h11]

end GSTC.Scattering
