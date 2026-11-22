/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Scattering

open scoped Matrix

public section

namespace GSTC.Scattering.Operator

open GSTC.Scattering

abbrev Vec4 := Fin 4 → ℂ

@[expose] def pack (r t : Vec2) : Vec4 := ![r 0, r 1, t 0, t 1]

@[expose] def readR (z : Vec4) : Vec2 := ![z 0, z 1]

@[expose] def readT (z : Vec4) : Vec2 := ![z 2, z 3]

theorem readR_pack (r t : Vec2) : readR (pack r t) = r := by
  funext i
  fin_cases i <;> rfl

theorem readT_pack (r t : Vec2) : readT (pack r t) = t := by
  funext i
  fin_cases i <;> rfl

theorem pack_unpack (z : Vec4) : pack (readR z) (readT z) = z := by
  funext i
  fin_cases i <;> rfl

theorem pack_injective {r t r' t' : Vec2} (h : pack r t = pack r' t') :
    r = r' ∧ t = t' := by
  simp only [pack] at h
  obtain ⟨h0, h1⟩ := Matrix.vecCons_inj.mp h
  obtain ⟨h2, h3⟩ := Matrix.vecCons_inj.mp h1
  obtain ⟨h4, h5⟩ := Matrix.vecCons_inj.mp h3
  obtain ⟨h6, _⟩ := Matrix.vecCons_inj.mp h5
  constructor
  · funext i
    fin_cases i
    · exact h0
    · exact h2
  · funext i
    fin_cases i
    · exact h4
    · exact h6

@[expose] def Kop (b : BoundaryCoeffs) (r t : Vec2) : Vec2 × Vec2 :=
  (b.beR *ᵥ r + b.beT *ᵥ t, b.bhR *ᵥ r + b.bhT *ᵥ t)

@[expose] def Kmat (b : BoundaryCoeffs) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![b.beR 0 0, b.beR 0 1, b.beT 0 0, b.beT 0 1;
     b.beR 1 0, b.beR 1 1, b.beT 1 0, b.beT 1 1;
     b.bhR 0 0, b.bhR 0 1, b.bhT 0 0, b.bhT 0 1;
     b.bhR 1 0, b.bhR 1 1, b.bhT 1 0, b.bhT 1 1]

theorem Kmat_mulVec_pack (b : BoundaryCoeffs) (r t : Vec2) :
    Kmat b *ᵥ pack r t = pack (Kop b r t).1 (Kop b r t).2 := by
  ext i
  fin_cases i <;>
    simp [Kmat, Kop, pack, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four,
      Fin.sum_univ_two] <;>
    ring

end GSTC.Scattering.Operator
