/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIInverseCompleteness

public section
namespace GSTC.Scattering
namespace TransverseRotation
open Matrix
open scoped Matrix

@[expose] def sigmaX : Ten2 := !![0, 1; 1, 0]

@[expose] def sigmaY : Ten2 := !![0, -Complex.I; Complex.I, 0]

@[expose] def sigmaZ : Ten2 := !![1, 0; 0, -1]

@[expose] noncomputable def rotation (γ : ℝ) : Ten2 :=
  !![(Real.cos γ : ℂ), (-Real.sin γ : ℂ); (Real.sin γ : ℂ), (Real.cos γ : ℂ)]

@[expose] noncomputable def rotAtX (θ x z : ℝ) : ℝ := x * Real.cos θ - z * Real.sin θ

@[expose] noncomputable def rotAtZ (θ x z : ℝ) : ℝ := x * Real.sin θ + z * Real.cos θ

@[expose] noncomputable def rotX (γ x z : ℝ) : ℝ := rotAtX (2 * γ) x z

@[expose] noncomputable def rotZ (γ x z : ℝ) : ℝ := rotAtZ (2 * γ) x z

end TransverseRotation
end GSTC.Scattering
