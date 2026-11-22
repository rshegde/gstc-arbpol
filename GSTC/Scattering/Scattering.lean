/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Boundary

open scoped Matrix

public section

namespace GSTC.Scattering

@[expose] noncomputable def aT1 (b : BoundaryCoeffs) (hR : b.bhR.det ≠ 0) : Ten2 :=
  b.beT - b.beR * ten2_inv b.bhR hR * b.bhT

@[expose] noncomputable def aR1 (b : BoundaryCoeffs) (hT : b.bhT.det ≠ 0) : Ten2 :=
  b.beR - b.beT * ten2_inv b.bhT hT * b.bhR

end GSTC.Scattering
