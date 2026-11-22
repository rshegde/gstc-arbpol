/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Scattering

open scoped Matrix

public section

namespace GSTC.Scattering

theorem chiTT_zero : chiTT (0 : Ten3) = 0 := by
  ext i j
  fin_cases i
  all_goals (fin_cases j <;> rfl)

end GSTC.Scattering
