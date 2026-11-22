/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Susceptibility

public section

namespace GSTC.Scattering

@[expose] def Susceptibilities.Lossless (sus : Susceptibilities) : Prop :=
  (∀ i j, sus.ee i j = star (sus.ee j i)) ∧
  (∀ i j, sus.mm i j = star (sus.mm j i)) ∧
  (∀ i j, sus.em i j = star (sus.me j i))

theorem Susceptibilities.Lossless.chiTT_hermitian (sus : Susceptibilities)
    (h : sus.Lossless) :
    (∀ i j : Fin 2, chiTT sus.ee i j = star (chiTT sus.ee j i)) ∧
    (∀ i j : Fin 2, chiTT sus.mm i j = star (chiTT sus.mm j i)) ∧
    (∀ i j : Fin 2, chiTT sus.em i j = star (chiTT sus.me j i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [chiTT] <;>
      first
        | exact h.1 0 0
        | exact h.1 0 1
        | exact h.1 1 0
        | exact h.1 1 1
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [chiTT] <;>
      first
        | exact h.2.1 0 0
        | exact h.2.1 0 1
        | exact h.2.1 1 0
        | exact h.2.1 1 1
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [chiTT] <;>
      first
        | exact h.2.2 0 0
        | exact h.2.2 0 1
        | exact h.2.2 1 0
        | exact h.2.2 1 1

end GSTC.Scattering
