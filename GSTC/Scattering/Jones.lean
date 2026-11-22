/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Azimuth

public section

namespace GSTC.Scattering

open scoped Matrix

@[expose] def jonesInner (u v : Vec2) : ℂ :=
  star (u 0) * v 0 + star (u 1) * v 1

@[expose] def jonesNormSq (u : Vec2) : ℂ := jonesInner u u

@[expose] def jonesNormSqR (u : Vec2) : ℝ := (jonesNormSq u).re

@[expose] def isNormalized (u : Vec2) : Prop := jonesInner u u = 1

theorem jonesInner_conj (u v : Vec2) :
    star (jonesInner u v) = jonesInner v u := by
  simp only [jonesInner, star_add, star_mul, star_star]

theorem star_mul_re (α : ℂ) : (star α * α).re = Complex.normSq α := by
  rw [Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self]
  exact Complex.ofReal_re _

@[expose] def efficiency (α : ℂ) : ℝ := Complex.normSq α

end GSTC.Scattering
