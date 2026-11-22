/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Power

open scoped Matrix

public section

namespace GSTC.Scattering

@[expose] def ten2Adjoint (A : Ten2) : Ten2 := fun i j => star (A j i)

theorem ten2Adjoint_apply (A : Ten2) (i j : Fin 2) :
    ten2Adjoint A i j = star (A j i) := rfl

theorem ten2Adjoint_involutive (A : Ten2) : ten2Adjoint (ten2Adjoint A) = A := by
  ext i j
  simp [ten2Adjoint]

theorem hc_ten2Adjoint (A : Ten2) (u v : Vec2) :
    hc u (ten2Adjoint A *ᵥ v) = hc (A *ᵥ u) v :=
  hc_cross (ten2Adjoint A) A (fun _ _ => rfl) u v

structure ScatteringMatrix where

  r1 : Ten2

  t12 : Ten2

  t21 : Ten2

  r2 : Ten2

@[expose] def ScatteringMatrix.out1 (S : ScatteringMatrix) (a1 a2 : Vec2) : Vec2 :=
  S.r1 *ᵥ a1 + S.t12 *ᵥ a2

@[expose] def ScatteringMatrix.out2 (S : ScatteringMatrix) (a1 a2 : Vec2) : Vec2 :=
  S.t21 *ᵥ a1 + S.r2 *ᵥ a2

theorem ScatteringMatrix.out1_add (S : ScatteringMatrix) (a1 a2 b1 b2 : Vec2) :
    S.out1 (a1 + b1) (a2 + b2) = S.out1 a1 a2 + S.out1 b1 b2 := by
  simp only [ScatteringMatrix.out1, Matrix.mulVec_add]
  abel

theorem ScatteringMatrix.out2_add (S : ScatteringMatrix) (a1 a2 b1 b2 : Vec2) :
    S.out2 (a1 + b1) (a2 + b2) = S.out2 a1 a2 + S.out2 b1 b2 := by
  simp only [ScatteringMatrix.out2, Matrix.mulVec_add]
  abel

theorem ScatteringMatrix.out1_smul (S : ScatteringMatrix) (c : ℂ) (a1 a2 a1' a2' : Vec2) :
    S.out1 (a1 + c • a1') (a2 + c • a2') = S.out1 a1 a2 + c • (S.out1 a1' a2') := by
  unfold ScatteringMatrix.out1
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [smul_add]
  abel

theorem ScatteringMatrix.out2_smul (S : ScatteringMatrix) (c : ℂ) (a1 a2 a1' a2' : Vec2) :
    S.out2 (a1 + c • a1') (a2 + c • a2') = S.out2 a1 a2 + c • (S.out2 a1' a2') := by
  unfold ScatteringMatrix.out2
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [smul_add]
  abel

@[expose] def ScatteringMatrix.conjTranspose (S : ScatteringMatrix) : ScatteringMatrix where
  r1 := ten2Adjoint S.r1
  t12 := ten2Adjoint S.t21
  t21 := ten2Adjoint S.t12
  r2 := ten2Adjoint S.r2

theorem couplingVPar_transmitted_eq_reflected (cfg : Config) (sus : Susceptibilities) :
    couplingVPar cfg .above sus .transmitted = couplingVPar cfg .below sus .reflected := rfl

theorem couplingWPar_transmitted_eq_reflected (cfg : Config) (sus : Susceptibilities) :
    couplingWPar cfg .above sus .transmitted = couplingWPar cfg .below sus .reflected := rfl

@[expose] def twoPortSystem (cfg : Config) (sus : Susceptibilities)
    (a1 b1 a2 b2 : Vec2) : Prop :=
  (boundaryCoeffs cfg .above sus).beI *ᵥ a1
      + (boundaryCoeffs cfg .above sus).beR *ᵥ b1
      + (boundaryCoeffs cfg .below sus).beI *ᵥ a2
      + (boundaryCoeffs cfg .above sus).beT *ᵥ b2 = 0
    ∧ (boundaryCoeffs cfg .above sus).bhI *ᵥ a1
      + (boundaryCoeffs cfg .above sus).bhR *ᵥ b1
      + (boundaryCoeffs cfg .below sus).bhI *ᵥ a2
      + (boundaryCoeffs cfg .above sus).bhT *ᵥ b2 = 0

structure SideNonDegeneracy (b : BoundaryCoeffs) : Prop where

  hR : b.bhR.det ≠ 0

  hT : b.bhT.det ≠ 0

  hT1 : (aT1 b hR).det ≠ 0

  hR1 : (aR1 b hT).det ≠ 0

structure TwoPortSetup (cfg : Config) (sus : Susceptibilities) : Prop where

  above : SideNonDegeneracy (boundaryCoeffs cfg .above sus)

  below : SideNonDegeneracy (boundaryCoeffs cfg .below sus)

end GSTC.Scattering
