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

end GSTC.Scattering
