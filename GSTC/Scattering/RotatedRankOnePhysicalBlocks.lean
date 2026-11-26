/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module
public import GSTC.Scattering.RotatedRankOneNorms
public import GSTC.Scattering.RotatedRankOneRecovery

public section
set_option autoImplicit false
namespace GSTC.Scattering.RotatedRankOneRecovery
open scoped Matrix Matrix.Norms.L2Operator
open Matrix RotatedRankOneResources SpectralMatrixSupport

@[expose] noncomputable def physicalElectric (sc : RotScalars) (c j l m : ℝ) : Mat :=
  (-(sc.p0+sc.t*l)) • (1 : Mat) +
    !![-c*(sc.p1+sc.u*l)+j*sc.w*m, -j*(sc.p1+sc.u*l)-c*sc.w*m;
       -j*(sc.p1+sc.u*l)-c*sc.w*m, -(-c*(sc.p1+sc.u*l)+j*sc.w*m)]

@[expose] noncomputable def physicalMagnetic (sc : RotScalars) (c j l m : ℝ) : Mat :=
  (-(sc.p0-sc.t*l)) • (1 : Mat) +
    !![c*(sc.p1-sc.u*l)+j*sc.w*m, j*(sc.p1-sc.u*l)-c*sc.w*m;
       j*(sc.p1-sc.u*l)-c*sc.w*m, -(c*(sc.p1-sc.u*l)+j*sc.w*m)]

@[expose] noncomputable def physicalCoupling (sc : RotScalars) (c j l m : ℝ) : Mat :=
  let d := j*sc.u*m-c*sc.w*l
  let e := -c*sc.u*m-j*sc.w*l
  !![-sc.q+d, e-sc.t*m; e+sc.t*m, -sc.q-d]

theorem physicalElectric_norm (sc : RotScalars) (c j l m : ℝ)
    (hc : c^2+j^2=1) (hl : l^2+m^2=1) :
    opNorm (physicalElectric sc c j l m) =
      |sc.p0+sc.t*l| + Real.sqrt ((sc.p1+sc.u*l)^2+sc.w^2*(1-l^2)) := by
  rw [physicalElectric, opNorm_scalar_tracelessSymm2, abs_neg]
  congr 2
  linear_combination ((sc.p1+sc.u*l)^2+(sc.w*m)^2)*hc + sc.w^2*hl

theorem physicalMagnetic_norm (sc : RotScalars) (c j l m : ℝ)
    (hc : c^2+j^2=1) (hl : l^2+m^2=1) :
    opNorm (physicalMagnetic sc c j l m) =
      |sc.p0-sc.t*l| + Real.sqrt ((sc.p1-sc.u*l)^2+sc.w^2*(1-l^2)) := by
  rw [physicalMagnetic, opNorm_scalar_tracelessSymm2, abs_neg]
  congr 2
  linear_combination ((sc.p1-sc.u*l)^2+(sc.w*m)^2)*hc + sc.w^2*hl

theorem physicalDirect_norm (sc : RotScalars) (c j l m : ℝ)
    (hc : c^2+j^2=1) (hl : l^2+m^2=1) :
    max (opNorm (physicalElectric sc c j l m)) (opNorm (physicalMagnetic sc c j l m)) =
      rotDirect sc |l| := by
  rw [physicalElectric_norm sc c j l m hc hl, physicalMagnetic_norm sc c j l m hc hl]
  by_cases h : 0 ≤ l
  · simp [rotDirect, abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]
    simp only [rotDirect, mul_neg, ← sub_eq_add_neg, sub_neg_eq_add, neg_sq]
    exact max_comm _ _

theorem physicalCoupling_norm (sc : RotScalars) (c j l m : ℝ)
    (hc : c^2+j^2=1) (hl : l^2+m^2=1) (hu : sc.u^2=sc.t^2+sc.w^2) :
    opNorm (physicalCoupling sc c j l m) = rotCoupling sc |l| := by
  rw [physicalCoupling, coupling_norm]
  have hm : m^2=1-l^2 := by linarith
  have hg : (j*sc.u*m-c*sc.w*l)^2+(-c*sc.u*m-j*sc.w*l)^2 =
      sc.t^2*(1-l^2)+sc.w^2 := by
    linear_combination ((sc.u*m)^2+(sc.w*l)^2)*hc + m^2*hu +
      (sc.t^2+sc.w^2)*hl
  rw [hg]
  simp only [rotCoupling, sq_abs]
  congr 2
  rw [mul_pow, hm]
  ring

end GSTC.Scattering.RotatedRankOneRecovery
