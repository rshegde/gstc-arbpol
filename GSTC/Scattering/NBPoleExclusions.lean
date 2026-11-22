/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.NBRealizability

public import Mathlib.Tactic.Module

public section
namespace GSTC.Scattering
open scoped Matrix

theorem nb_realizes_symmetric (cfg : Config) (s : Side) (T : Ten2)
    (hk : cfg.kPar = 0) (hmed : identicalMedia cfg s)
    (h : NBRealizes cfg s T) : T.transpose = T := by
  obtain ⟨X, Y, hXS, hYS, _, _, _, _, hT⟩ :=
    (nb_realizes_iff_poleFreeMidpoint cfg s T hk hmed).mp h
  simp only [hT, Matrix.transpose_smul, Matrix.transpose_add, hXS, hYS]

end GSTC.Scattering
