/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Frame

open scoped Matrix

public section

namespace GSTC.Scattering

structure Vacuum where
  eps0 : ℝ
  mu0 : ℝ
  c0 : ℝ
  eta0 : ℝ
  eps0_pos : 0 < eps0
  mu0_pos : 0 < mu0
  c0_pos : 0 < c0
  eta0_pos : 0 < eta0
  h_c : c0 ^ 2 * eps0 * mu0 = 1
  h_eta : eta0 ^ 2 * eps0 = mu0

structure Medium where
  epsR : ℝ
  muR : ℝ
  eta : ℝ
  k : ℝ
  epsR_pos : 0 < epsR
  muR_pos : 0 < muR
  eta_pos : 0 < eta
  k_pos : 0 < k

structure Config where
  omega : ℝ
  vac : Vacuum
  upper : Medium
  lower : Medium
  kPar : ℝ
  omega_pos : 0 < omega
  kPar_nonneg : 0 ≤ kPar
  kPar_lt_upper : kPar < upper.k
  kPar_lt_lower : kPar < lower.k

inductive Side where
  | above
  | below

inductive PropDir where
  | pos
  | neg

@[expose] def PropDir.sign : PropDir → ℝ
  | .pos => 1
  | .neg => -1

inductive Wave where
  | incident
  | reflected
  | transmitted

@[expose] def Side.jumpSign : Side → ℂ
  | .above => 1
  | .below => -1

@[expose] def Wave.dir (s : Side) (w : Wave) : PropDir :=
  match s, w with
  | .above, .incident => .neg
  | .above, .reflected => .pos
  | .above, .transmitted => .neg
  | .below, .incident => .pos
  | .below, .reflected => .neg
  | .below, .transmitted => .pos

@[expose] def Wave.medium (cfg : Config) (s : Side) (w : Wave) : Medium :=
  match s, w with
  | .above, .incident => cfg.upper
  | .above, .reflected => cfg.upper
  | .above, .transmitted => cfg.lower
  | .below, .incident => cfg.lower
  | .below, .reflected => cfg.lower
  | .below, .transmitted => cfg.upper

@[expose] noncomputable def cFactor (m : Medium) (kPar : ℝ) : ℝ :=
  Real.sqrt (1 - (kPar / m.k) ^ 2)

@[expose] noncomputable def zTM (m : Medium) (kPar : ℝ) : ℝ :=
  m.eta * cFactor m kPar

@[expose] noncomputable def zTE (m : Medium) (kPar : ℝ) : ℝ :=
  m.eta / cFactor m kPar

@[expose] def kVec (kPar : ℝ) : Vec2 := ![(kPar : ℂ), 0]

@[expose] def lVec (kPar : ℝ) : Vec2 := ![0, (kPar : ℂ)]

@[expose] def kRow (kPar : ℝ) : Row2 := !![(kPar : ℂ), 0]

@[expose] def lRow (kPar : ℝ) : Row2 := !![0, (kPar : ℂ)]

@[expose] noncomputable def waveY (m : Medium) (kPar : ℝ) : Ten2 :=
  !![(1 / zTM m kPar : ℂ), 0; 0, (1 / zTE m kPar : ℂ)]

@[expose] noncomputable def hPar (cfg : Config) (s : Side) (w : Wave) (e : Vec2) : Vec2 :=
  ((PropDir.sign (Wave.dir s w) : ℂ)) • ((ncross * waveY (Wave.medium cfg s w) cfg.kPar) *ᵥ e)

theorem Vacuum.c0_mul_mu0 (v : Vacuum) : v.c0 * v.mu0 = v.eta0 := by
  have heps : v.eps0 ≠ 0 := ne_of_gt v.eps0_pos
  have h3 : v.c0 ^ 2 * v.mu0 * v.eps0 = 1 := by nlinarith [v.h_c]
  have h2 : v.c0 ^ 2 * v.mu0 = 1 / v.eps0 := by
    have hh : v.c0 ^ 2 * v.mu0 = (v.c0 ^ 2 * v.mu0 * v.eps0) / v.eps0 := by field_simp
    rw [hh, h3]
  have hm : v.mu0 = v.eta0 ^ 2 * v.eps0 := v.h_eta.symm
  have h4 : v.c0 ^ 2 * v.mu0 ^ 2 = v.eta0 ^ 2 := by
    have h5 : v.c0 ^ 2 * v.mu0 ^ 2 = v.mu0 * (v.c0 ^ 2 * v.mu0) := by ring
    have h6 : v.mu0 * (v.c0 ^ 2 * v.mu0) = v.mu0 * (1 / v.eps0) := by rw [h2]
    have h7 : v.mu0 * (1 / v.eps0) = v.mu0 / v.eps0 := by ring
    have h8 : v.mu0 / v.eps0 = (v.eta0 ^ 2 * v.eps0) / v.eps0 := by rw [hm]
    have h9 : (v.eta0 ^ 2 * v.eps0) / v.eps0 = v.eta0 ^ 2 := by field_simp
    exact h5.trans (h6.trans (h7.trans (h8.trans h9)))
  have h10 : (v.c0 * v.mu0) ^ 2 = (v.eta0) ^ 2 := by
    have hh : (v.c0 * v.mu0) ^ 2 = v.c0 ^ 2 * v.mu0 ^ 2 := by
      simp only [pow_two]
      ring
    rw [hh]
    exact h4
  nlinarith [h10, mul_pos v.c0_pos v.mu0_pos, v.eta0_pos]

theorem Vacuum.c0_mul_eps0 (v : Vacuum) : v.c0 * v.eps0 = 1 / v.eta0 := by
  have hmu : v.mu0 ≠ 0 := ne_of_gt v.mu0_pos
  have heps : v.eps0 ≠ 0 := ne_of_gt v.eps0_pos
  have h2 : v.c0 ^ 2 * v.eps0 = 1 / v.mu0 := by
    have hh : v.c0 ^ 2 * v.eps0 = (v.c0 ^ 2 * v.eps0 * v.mu0) / v.mu0 := by field_simp
    rw [hh, v.h_c]
  have hm : v.mu0 = v.eta0 ^ 2 * v.eps0 := v.h_eta.symm
  have h4 : v.c0 ^ 2 * v.eps0 ^ 2 = v.eps0 / v.mu0 := by
    have h5 : v.c0 ^ 2 * v.eps0 ^ 2 = v.eps0 * (v.c0 ^ 2 * v.eps0) := by ring
    have h6 : v.eps0 * (v.c0 ^ 2 * v.eps0) = v.eps0 * (1 / v.mu0) := by rw [h2]
    have h7 : v.eps0 * (1 / v.mu0) = v.eps0 / v.mu0 := by ring
    exact h5.trans (h6.trans h7)
  have h8 : v.eps0 / v.mu0 = 1 / (v.eta0 ^ 2) := by
    have hh : v.eps0 / v.mu0 = v.eps0 / (v.eta0 ^ 2 * v.eps0) := by rw [hm]
    rw [hh]
    field_simp
  have h10 : (v.c0 * v.eps0 * v.eta0) ^ 2 = 1 := by
    have hh : (v.c0 * v.eps0 * v.eta0) ^ 2 = v.c0 ^ 2 * v.eps0 ^ 2 * v.eta0 ^ 2 := by
      simp only [pow_two]
      ring
    rw [hh, h4, h8]
    field_simp [ne_of_gt v.eta0_pos]
  have h11 : v.c0 * v.eps0 * v.eta0 = 1 := by
    nlinarith [h10, mul_pos (mul_pos v.c0_pos v.eps0_pos) v.eta0_pos]
  have h12 : v.c0 * v.eps0 = (v.c0 * v.eps0 * v.eta0) / v.eta0 := by
    field_simp [ne_of_gt v.eta0_pos]
  rw [h12, h11]

end GSTC.Scattering
