/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Media

open scoped Matrix

public section

namespace GSTC.Scattering

abbrev Ten3 := Matrix (Fin 3) (Fin 3) ℂ

structure Susceptibilities where
  ee : Ten3
  mm : Ten3
  em : Ten3
  me : Ten3

@[expose] def chiTT (c : Ten3) : Ten2 := !![c 0 0, c 0 1; c 1 0, c 1 1]

@[expose] def chiTN (c : Ten3) : Vec2 := ![c 0 2, c 1 2]

@[expose] def chiNT (c : Ten3) : Row2 := !![c 2 0, c 2 1]

@[expose] def chiNN (c : Ten3) : ℂ := c 2 2

end GSTC.Scattering
