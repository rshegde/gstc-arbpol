/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.BIAdjugate

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

open scoped Matrix

public section

namespace GSTC.Scattering
namespace BIPolynomials

open BIFeasibility

noncomputable section

inductive BICoord where

  | ee00

  | ee01

  | ee11

  | mm00

  | mm01

  | mm11

  | g00

  | g01

  | g10

  | g11
  deriving DecidableEq, Repr

@[expose] def assign (p : BIParams) : BICoord → ℝ
  | .ee00 => p.ee00
  | .ee01 => p.ee01
  | .ee11 => p.ee11
  | .mm00 => p.mm00
  | .mm01 => p.mm01
  | .mm11 => p.mm11
  | .g00 => p.g00
  | .g01 => p.g01
  | .g10 => p.g10
  | .g11 => p.g11

abbrev CPoly := QuadraticAlgebra (MvPolynomial BICoord ℝ) (-1) 0

@[expose] def CPoly.eval (f : CPoly) (a : BICoord → ℝ) : ℂ :=
  (f.re.eval a) + Complex.I * (f.im.eval a)

@[expose] def CPoly.evalHom (a : BICoord → ℝ) : CPoly →+* ℂ where
  toFun f := f.eval a
  map_one' := by simp [CPoly.eval, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_zero' := by simp [CPoly.eval]
  map_add' := by
    intro f g
    simp [CPoly.eval]
    ring
  map_mul' := by
    intro f g
    simp [CPoly.eval, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    ring_nf
    simp [Complex.I_sq]; ring

theorem CPoly.eval_re (f : CPoly) (a : BICoord → ℝ) : (f.re.eval a) = (f.eval a).re := by
  rw [CPoly.eval]
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]

theorem CPoly.eval_im (f : CPoly) (a : BICoord → ℝ) : (f.im.eval a) = (f.eval a).im := by
  rw [CPoly.eval]
  simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]

@[expose] noncomputable def CPoly.ofReal (r : ℝ) : CPoly := ⟨MvPolynomial.C r, 0⟩

@[expose] noncomputable def CPoly.i : CPoly := ⟨0, 1⟩

@[expose] noncomputable def CPoly.var (c : BICoord) : CPoly := ⟨MvPolynomial.X c, 0⟩

theorem CPoly.evalHom_ofReal (a : BICoord → ℝ) (r : ℝ) :
    CPoly.evalHom a (CPoly.ofReal r) = (r : ℂ) := by
  simp [CPoly.evalHom, CPoly.eval, CPoly.ofReal, MvPolynomial.eval_C]

theorem CPoly.evalHom_i (a : BICoord → ℝ) : CPoly.evalHom a CPoly.i = Complex.I := by
  simp [CPoly.evalHom, CPoly.eval, CPoly.i]

theorem CPoly.evalHom_var (a : BICoord → ℝ) (c : BICoord) :
    CPoly.evalHom a (CPoly.var c) = (a c : ℂ) := by
  simp [CPoly.evalHom, CPoly.eval, CPoly.var, MvPolynomial.eval_X]

theorem CPoly.evalHom_apply (f : CPoly) (a : BICoord → ℝ) :
    CPoly.evalHom a f = f.eval a := rfl

@[expose] noncomputable def biMidpointMapPoly (cfg : Config) : Matrix (Fin 4) (Fin 4) CPoly :=
  let w : ℝ := Real.sqrt cfg.upper.eta
  !![CPoly.ofReal (w / 2), 0, CPoly.ofReal (w / 2), 0;
    0, CPoly.ofReal (w / 2), 0, CPoly.ofReal (w / 2);
    0, CPoly.ofReal (1 / (2 * w)), 0, CPoly.ofReal (-(1 / (2 * w)));
    CPoly.ofReal (-(1 / (2 * w))), 0, CPoly.ofReal (1 / (2 * w)), 0]

theorem biMidpointMapPoly_eval (cfg : Config) (a : BICoord → ℝ) :
    (biMidpointMapPoly cfg).map (CPoly.evalHom a) = biMidpointMap4 cfg := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, biMidpointMapPoly, biMidpointMap4, CPoly.evalHom_ofReal,
      div_eq_mul_inv, mul_inv_rev]

@[expose] noncomputable def biConstitutiveHPoly (cfg : Config) : Matrix (Fin 4) (Fin 4) CPoly :=
  let e : CPoly := CPoly.ofReal cfg.vac.eps0
  let m : CPoly := CPoly.ofReal cfg.vac.mu0
  let ci : CPoly := CPoly.ofReal cfg.vac.c0⁻¹
  !![e * CPoly.var .ee00, e * CPoly.var .ee01,
     CPoly.i * CPoly.var .g00 * ci, CPoly.i * CPoly.var .g01 * ci;
   e * CPoly.var .ee01, e * CPoly.var .ee11,
     CPoly.i * CPoly.var .g10 * ci, CPoly.i * CPoly.var .g11 * ci;
   -(CPoly.i * CPoly.var .g00 * ci), -(CPoly.i * CPoly.var .g10 * ci),
     m * CPoly.var .mm00, m * CPoly.var .mm01;
   -(CPoly.i * CPoly.var .g01 * ci), -(CPoly.i * CPoly.var .g11 * ci),
     m * CPoly.var .mm01, m * CPoly.var .mm11]

theorem biConstitutiveHPoly_eval (cfg : Config) (p : BIParams) :
    (biConstitutiveHPoly cfg).map (CPoly.evalHom (assign p)) = biConstitutiveH cfg p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, biConstitutiveHPoly, biConstitutiveH,
      CPoly.evalHom_ofReal, CPoly.evalHom_var, CPoly.evalHom_i,
      Complex.ofReal_inv, div_eq_mul_inv, assign]

@[expose] def CPoly.conj (f : CPoly) : CPoly := ⟨f.re, -f.im⟩

@[expose] def cpolyConjTranspose (M : Matrix (Fin m) (Fin n) CPoly) :
    Matrix (Fin n) (Fin m) CPoly :=
  fun i j => (M j i).conj

theorem evalHom_mapMatrix_cpolyConjTranspose (M : Matrix (Fin m) (Fin n) CPoly)
    (a : BICoord → ℝ) (i : Fin n) (j : Fin m) :
    ((cpolyConjTranspose M).map (CPoly.evalHom a)) i j
      = star ((M.map (CPoly.evalHom a)) j i) := by
  apply Complex.ext <;>
    simp [cpolyConjTranspose, CPoly.conj, CPoly.evalHom, CPoly.eval]

theorem evalHom_map_det (M : Matrix (Fin n) (Fin n) CPoly)
    (a : BICoord → ℝ) :
    (CPoly.evalHom a) M.det = (M.map (CPoly.evalHom a)).det :=
  (CPoly.evalHom a).map_det M

theorem evalHom_map_adjugate (M : Matrix (Fin n) (Fin n) CPoly)
    (a : BICoord → ℝ) :
    (M.adjugate.map (CPoly.evalHom a)) = (M.map (CPoly.evalHom a)).adjugate :=
  (CPoly.evalHom a).map_adjugate M

theorem evalHom_mapMatrix_smul (c : CPoly) (M : Matrix (Fin m) (Fin n) CPoly)
    (a : BICoord → ℝ) :
    (c • M).map (CPoly.evalHom a) = (CPoly.evalHom a c) • (M.map (CPoly.evalHom a)) := by
  ext i j
  simp [Matrix.smul_apply, Matrix.map_apply]

theorem evalHom_mapMatrix_add (M N : Matrix (Fin m) (Fin n) CPoly) (a : BICoord → ℝ) :
    (M + N).map (CPoly.evalHom a) = (M.map (CPoly.evalHom a)) + (N.map (CPoly.evalHom a)) := by
  ext i j
  simp [Matrix.map_apply, map_add]

theorem evalHom_mapMatrix_sub (M N : Matrix (Fin m) (Fin n) CPoly) (a : BICoord → ℝ) :
    (M - N).map (CPoly.evalHom a) = (M.map (CPoly.evalHom a)) - (N.map (CPoly.evalHom a)) := by
  ext i j
  simp [Matrix.map_apply, map_sub]

theorem cpolyConjTranspose_eval (M : Matrix (Fin m) (Fin n) CPoly) (a : BICoord → ℝ) :
    (cpolyConjTranspose M).map (CPoly.evalHom a) = (M.map (CPoly.evalHom a)).conjTranspose := by
  ext i j
  rw [evalHom_mapMatrix_cpolyConjTranspose, Matrix.conjTranspose_apply]

@[expose] noncomputable def biKPoly (cfg : Config) : Matrix (Fin 4) (Fin 4) CPoly :=
  CPoly.ofReal (-2 * cfg.omega) •
    (cpolyConjTranspose (biMidpointMapPoly cfg) * biConstitutiveHPoly cfg
      * biMidpointMapPoly cfg)

theorem biKPoly_eval (cfg : Config) (p : BIParams) :
    (biKPoly cfg).map (CPoly.evalHom (assign p)) = biConstitutiveK cfg p := by
  have hM : (biMidpointMapPoly cfg).map (CPoly.evalHom (assign p)) = biMidpointMap4 cfg :=
    biMidpointMapPoly_eval cfg (assign p)
  have hH : (biConstitutiveHPoly cfg).map (CPoly.evalHom (assign p)) = biConstitutiveH cfg p :=
    biConstitutiveHPoly_eval cfg p
  have hMt : (cpolyConjTranspose (biMidpointMapPoly cfg)).map (CPoly.evalHom (assign p))
      = (biMidpointMap4 cfg).conjTranspose := by
    rw [cpolyConjTranspose_eval, hM]
  rw [biKPoly, evalHom_mapMatrix_smul, Matrix.map_mul, Matrix.map_mul, hMt, hH, hM]
  simp [biConstitutiveK, CPoly.evalHom_ofReal, Complex.ofReal_mul, Complex.ofReal_neg]

theorem CPoly.evalHom_eq_of_map_eq {M : Matrix (Fin m) (Fin n) CPoly}
    {N : Matrix (Fin m) (Fin n) ℂ} {a : BICoord → ℝ}
    (h : M.map (CPoly.evalHom a) = N) (i : Fin m) (j : Fin n) :
    CPoly.evalHom a (M i j) = N i j := by
  have h' := congrArg (fun X : Matrix (Fin m) (Fin n) ℂ => X i j) h
  rwa [Matrix.map_apply] at h'

@[expose] noncomputable def biParityExchangePoly : Matrix (Fin 4) (Fin 4) CPoly :=
  !![(0 : CPoly), (0 : CPoly), (1 : CPoly), (0 : CPoly);
    (0 : CPoly), (0 : CPoly), (0 : CPoly), (1 : CPoly);
    (1 : CPoly), (0 : CPoly), (0 : CPoly), (0 : CPoly);
    (0 : CPoly), (1 : CPoly), (0 : CPoly), (0 : CPoly)]

theorem biParityExchangePoly_eval (a : BICoord → ℝ) :
    (biParityExchangePoly).map (CPoly.evalHom a) = parityExchange := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, biParityExchangePoly, parityExchange]

@[expose] noncomputable def biDenPoly (cfg : Config) : Matrix (Fin 4) (Fin 4) CPoly :=
  CPoly.ofReal 2 • (1 : Matrix (Fin 4) (Fin 4) CPoly) - CPoly.i • biKPoly cfg

@[expose] noncomputable def biNumPoly (cfg : Config) : Matrix (Fin 4) (Fin 4) CPoly :=
  CPoly.ofReal 2 • (1 : Matrix (Fin 4) (Fin 4) CPoly) + CPoly.i • biKPoly cfg

theorem biDenPoly_eval (cfg : Config) (p : BIParams) :
    (biDenPoly cfg).map (CPoly.evalHom (assign p)) = biDenominator cfg p := by
  have hK := biKPoly_eval cfg p
  have hone : ((1 : Matrix (Fin 4) (Fin 4) CPoly).map (CPoly.evalHom (assign p)))
      = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    simp [Matrix.map_one]
  rw [biDenPoly, evalHom_mapMatrix_sub, evalHom_mapMatrix_smul, evalHom_mapMatrix_smul,
    hone, hK]
  simp [CPoly.evalHom_i, biDenominator, CPoly.evalHom_ofReal];
    ext i j;
    simp [Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply]

theorem biNumPoly_eval (cfg : Config) (p : BIParams) :
    (biNumPoly cfg).map (CPoly.evalHom (assign p)) = biNumerator4 cfg p := by
  have hK := biKPoly_eval cfg p
  have hone : ((1 : Matrix (Fin 4) (Fin 4) CPoly).map (CPoly.evalHom (assign p)))
      = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    simp [Matrix.map_one]
  rw [biNumPoly, evalHom_mapMatrix_add, evalHom_mapMatrix_smul,
    evalHom_mapMatrix_smul, hone, hK]
  simp [CPoly.evalHom_i, biNumerator4, CPoly.evalHom_ofReal];
    ext i j;
    simp [Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply]

@[expose] noncomputable def biDetPoly (cfg : Config) : CPoly := (biDenPoly cfg).det

theorem biDetPoly_eval (cfg : Config) (p : BIParams) :
    CPoly.evalHom (assign p) (biDetPoly cfg) = biDet cfg p := by
  rw [biDetPoly, evalHom_map_det, biDenPoly_eval]
  rfl

@[expose] noncomputable def biAdjugateNumeratorPoly (cfg : Config) : Matrix (Fin 4) (Fin 4) CPoly :=
  biParityExchangePoly * (biDenPoly cfg).adjugate * biNumPoly cfg

theorem biAdjugateNumeratorPoly_eval (cfg : Config) (p : BIParams) :
    (biAdjugateNumeratorPoly cfg).map (CPoly.evalHom (assign p))
      = biAdjugateNumerator cfg p := by
  have hΘ := biParityExchangePoly_eval (assign p)
  have hD := biDenPoly_eval cfg p
  have hN := biNumPoly_eval cfg p
  have hadj : ((biDenPoly cfg).adjugate.map (CPoly.evalHom (assign p)))
      = (biDenominator cfg p).adjugate := by
    rw [evalHom_map_adjugate, hD]
  rw [biAdjugateNumeratorPoly, Matrix.map_mul, Matrix.map_mul, hΘ, hadj, hN]
  rfl

@[expose] noncomputable def biNumeratorTPoly (cfg : Config) : Matrix (Fin 2) (Fin 2) CPoly :=
  !![(biAdjugateNumeratorPoly cfg) 2 0, (biAdjugateNumeratorPoly cfg) 2 1;
     (biAdjugateNumeratorPoly cfg) 3 0, (biAdjugateNumeratorPoly cfg) 3 1]

theorem biNumeratorTPoly_eval (cfg : Config) (p : BIParams) :
    (biNumeratorTPoly cfg).map (CPoly.evalHom (assign p)) = biNumeratorT cfg p := by
  have hQ := biAdjugateNumeratorPoly_eval cfg p
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, biNumeratorTPoly, biNumeratorT]
  all_goals exact CPoly.evalHom_eq_of_map_eq hQ _ _

theorem biDetPoly_eval_re (cfg : Config) (p : BIParams) :
    (biDetPoly cfg).re.eval (assign p) = (biDet cfg p).re := by
  have h := congrArg Complex.re (biDetPoly_eval cfg p)
  rw [CPoly.evalHom_apply] at h
  rwa [← CPoly.eval_re] at h

theorem biDetPoly_eval_im (cfg : Config) (p : BIParams) :
    (biDetPoly cfg).im.eval (assign p) = (biDet cfg p).im := by
  have h := congrArg Complex.im (biDetPoly_eval cfg p)
  rw [CPoly.evalHom_apply] at h
  rwa [← CPoly.eval_im] at h

theorem biNumeratorTPoly_eval_re (cfg : Config) (p : BIParams) (i : Fin 2) (j : Fin 2) :
    (biNumeratorTPoly cfg i j).re.eval (assign p) = (biNumeratorT cfg p i j).re := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) (biNumeratorTPoly_eval cfg p)
  rw [Matrix.map_apply, CPoly.evalHom_apply] at h
  have hre := congrArg Complex.re h
  rwa [← CPoly.eval_re] at hre

theorem biNumeratorTPoly_eval_im (cfg : Config) (p : BIParams) (i : Fin 2) (j : Fin 2) :
    (biNumeratorTPoly cfg i j).im.eval (assign p) = (biNumeratorT cfg p i j).im := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) (biNumeratorTPoly_eval cfg p)
  rw [Matrix.map_apply, CPoly.evalHom_apply] at h
  have him := congrArg Complex.im h
  rwa [← CPoly.eval_im] at him

end

end BIPolynomials

end GSTC.Scattering
