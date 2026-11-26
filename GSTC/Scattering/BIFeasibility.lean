/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIScattering

public section

namespace GSTC.Scattering
namespace BIFeasibility

open scoped Matrix
open GSTC.Scattering.Operator

inductive SheetClass where

  | E : SheetClass

  | NB : SheetClass

  | BI : SheetClass
  deriving DecidableEq, Repr

@[expose] def ElectricOnly (p : BIParams) : Prop :=
  p.mm00 = 0 ∧ p.mm01 = 0 ∧ p.mm11 = 0 ∧ p.g00 = 0 ∧ p.g01 = 0 ∧ p.g10 = 0 ∧ p.g11 = 0

@[expose] def NoCoupling (p : BIParams) : Prop :=
  p.g00 = 0 ∧ p.g01 = 0 ∧ p.g10 = 0 ∧ p.g11 = 0

@[expose] def InClass : SheetClass → BIParams → Prop
  | .E, p => ElectricOnly p
  | .NB, p => NoCoupling p
  | .BI, _ => True

theorem NB_implies_BI (p : BIParams) (_h : InClass .NB p) : InClass .BI p := by
  trivial

structure Budget where

  Be : ℝ

  Bm : ℝ

  Bc : ℝ

  hBe : 0 ≤ Be

  hBm : 0 ≤ Bm

  hBc : 0 ≤ Bc

@[expose] def WithinBudget (b : Budget) (p : BIParams) : Prop :=
  |p.ee00| ≤ b.Be ∧ |p.ee01| ≤ b.Be ∧ |p.ee11| ≤ b.Be ∧
  |p.mm00| ≤ b.Bm ∧ |p.mm01| ≤ b.Bm ∧ |p.mm11| ≤ b.Bm ∧
  |p.g00| ≤ b.Bc ∧ |p.g01| ≤ b.Bc ∧ |p.g10| ≤ b.Bc ∧ |p.g11| ≤ b.Bc

@[expose] noncomputable def biForwardT (cfg : Config) (p : BIParams) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(biPowerResponse4 cfg p) 2 0, (biPowerResponse4 cfg p) 2 1;
     (biPowerResponse4 cfg p) 3 0, (biPowerResponse4 cfg p) 3 1]

theorem zero_params_in_all_classes (c : SheetClass) : InClass c biZeroParams := by
  rcases c with _ | _ | _
  · simp [InClass, ElectricOnly, biZeroParams]
  · simp [InClass, NoCoupling, biZeroParams]
  · simp [InClass]

theorem biForwardT_zero (cfg : Config) : biForwardT cfg biZeroParams = 1 := by
  have hC := bi_cayley_zero cfg
  have hR : biPowerResponse4 cfg biZeroParams = parityExchange := by
    unfold biPowerResponse4
    rw [hC, Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [biForwardT, hR, parityExchange]

end BIFeasibility

end GSTC.Scattering
