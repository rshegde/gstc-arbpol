/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module
public import GSTC.Scattering.RotatedRankOneResources

public section
set_option autoImplicit false
namespace GSTC.Scattering.RotatedRankOneRecovery
open scoped Matrix Matrix.Norms.L2Operator
open SpectralMatrixSupport

theorem star_eq_transpose_of_real (M : Mat) : star M = M.transpose := by
  rw [Matrix.star_eq_conjTranspose]
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem coupling_norm (q a d e : ℝ) :
    opNorm (!![-q+d, e-a; e+a, -q-d] : Mat) =
      Real.sqrt (q^2+a^2) + Real.sqrt (d^2+e^2) := by
  let M : Mat := !![-q+d, e-a; e+a, -q-d]
  have hstar : star M = M.transpose := star_eq_transpose_of_real M
  have hgram : M.transpose * M =
      (q^2+a^2+d^2+e^2) • (1 : Mat) +
        !![2*(a*e-q*d), -2*(a*d+q*e); -2*(a*d+q*e), -2*(a*e-q*d)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    all_goals ring
  have hnorm : opNorm (M.transpose * M) = opNorm M ^ 2 := by
    simp only [opNorm, pow_two, ← hstar]
    exact CStarRing.norm_star_mul_self (x := M)
  have hmat : (q^2+a^2+d^2+e^2) • (1 : Mat)
        + !![2*(a*e-q*d), -2*(a*d+q*e); -2*(a*d+q*e), -2*(a*e-q*d)]
      = (q^2+a^2+d^2+e^2) • (1 : Mat)
        + !![2*(a*e-q*d), -2*(a*d+q*e); -2*(a*d+q*e), -(2*(a*e-q*d))] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, Matrix.add_apply]
  have htr : opNorm (M.transpose * M) =
      |q^2+a^2+d^2+e^2| +
        Real.sqrt ((2*(a*e-q*d))^2 + (-2*(a*d+q*e))^2) := by
    rw [hgram, hmat]
    exact opNorm_scalar_tracelessSymm2 (q^2+a^2+d^2+e^2)
      (2*(a*e-q*d)) (-2*(a*d+q*e))
  have htrM : opNorm M ^ 2 =
      |q^2+a^2+d^2+e^2| +
        Real.sqrt ((2*(a*e-q*d))^2 + (-2*(a*d+q*e))^2) := by
    rw [← hnorm]
    exact htr
  have hA : 0 ≤ q^2+a^2 := by positivity
  have hB : 0 ≤ d^2+e^2 := by positivity
  have h4 : Real.sqrt 4 = 2 := by
    rw [← show (2:ℝ)^2 = 4 by norm_num, Real.sqrt_sq (x := 2) (by norm_num)]
  have hs : Real.sqrt ((2*(a*e-q*d))^2+(-2*(a*d+q*e))^2) =
      2 * (Real.sqrt (q^2+a^2) * Real.sqrt (d^2+e^2)) := by
    have hP : (2*(a*e-q*d))^2 + (-2*(a*d+q*e))^2 =
        4 * ((q^2+a^2) * (d^2+e^2)) := by ring
    calc Real.sqrt ((2*(a*e-q*d))^2+(-2*(a*d+q*e))^2)
        = Real.sqrt (4 * ((q^2+a^2) * (d^2+e^2))) := by rw [hP]
      _ = Real.sqrt 4 * Real.sqrt ((q^2+a^2) * (d^2+e^2)) :=
        Real.sqrt_mul (x := 4) (by norm_num) ((q^2+a^2) * (d^2+e^2))
      _ = 2 * (Real.sqrt (q^2+a^2) * Real.sqrt (d^2+e^2)) := by
        have h2 : Real.sqrt ((q^2+a^2) * (d^2+e^2)) =
            Real.sqrt (q^2+a^2) * Real.sqrt (d^2+e^2) :=
          Real.sqrt_mul (x := q^2+a^2) hA (d^2+e^2)
        rw [h2, h4]
  have hsq : opNorm M ^ 2 =
      (Real.sqrt (q^2+a^2) + Real.sqrt (d^2+e^2)) ^ 2 := by
    rw [htrM, abs_of_nonneg (by positivity), hs]
    rw [show (Real.sqrt (q^2+a^2) + Real.sqrt (d^2+e^2)) ^ 2 =
        (Real.sqrt (q^2+a^2)) ^ 2
          + 2 * Real.sqrt (q^2+a^2) * Real.sqrt (d^2+e^2)
          + (Real.sqrt (d^2+e^2)) ^ 2 by ring,
      Real.sq_sqrt (x := q^2+a^2) hA, Real.sq_sqrt (x := d^2+e^2) hB]
    ring
  rw [← Real.sqrt_sq
      (x := Real.sqrt (q^2+a^2) + Real.sqrt (d^2+e^2)) (by positivity),
    ← hsq, Real.sqrt_sq (x := opNorm M) (opNorm_nonneg M)]

end GSTC.Scattering.RotatedRankOneRecovery
