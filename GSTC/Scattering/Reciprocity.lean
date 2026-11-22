/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Susceptibility

public section
namespace GSTC.Scattering

@[expose] def Susceptibilities.reciprocalEE (sus : Susceptibilities) : Prop :=
  ∀ i j, sus.ee i j = sus.ee j i

@[expose] def Susceptibilities.reciprocalMM (sus : Susceptibilities) : Prop :=
  ∀ i j, sus.mm i j = sus.mm j i

@[expose] def Susceptibilities.reciprocalEM (sus : Susceptibilities) : Prop :=
  ∀ i j, sus.em i j = -(sus.me j i)

@[expose] def Susceptibilities.Reciprocal (sus : Susceptibilities) : Prop :=
  sus.reciprocalEE ∧ sus.reciprocalMM ∧ sus.reciprocalEM

end GSTC.Scattering
