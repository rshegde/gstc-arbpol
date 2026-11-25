/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module
public import GSTC.Scattering.RotatedRankOneBridge

public section
set_option autoImplicit false
namespace GSTC.Scattering.RotatedRankOneRecovery
open scoped Matrix Matrix.Norms.L2Operator
open Matrix BIInverse RotatedRankOneResources SpectralMatrixSupport
open SusceptibilityBudget MaterialSpace BIPolynomials ClassFeasibility

theorem vacuum_resource_scales (cfg : Config) (heta : cfg.upper.eta=cfg.vac.eta0) :
    spectralElectricScale cfg=cfg.vac.c0/cfg.omega ∧
    spectralMagneticScale cfg=cfg.vac.c0/cfg.omega ∧
    spectralChiralScale cfg=cfg.vac.c0/cfg.omega := by
  have hw := ne_of_gt cfg.omega_pos
  have he := ne_of_gt cfg.vac.eps0_pos
  have hm := ne_of_gt cfg.vac.mu0_pos
  have hη := ne_of_gt cfg.vac.eta0_pos
  have hv := cfg.vac.c0_mul_eps0
  field_simp [hη] at hv
  refine ⟨?_, ?_, rfl⟩
  · dsimp [spectralElectricScale]
    rw [heta]
    field_simp
    nlinarith
  · dsimp [spectralMagneticScale]
    rw [heta]
    field_simp
    nlinarith [cfg.vac.c0_mul_mu0]

theorem recovered_spectral_budgets (cfg : Config) (s r c j x y h k : ℝ)
    (hr : r^2+s^2=1) (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hb : k^2+h^2=1)
    (hf : rotF s c x y ≠ 0) (heta : cfg.upper.eta=cfg.vac.eta0) :
    spectralDirectBudget cfg (assign (parametersForResponse cfg (familyResponse s r c j x y h k))) =
      rotDirect (rotScalars s r c j x y) |k*x-h*y| ∧
    spectralCouplingBudget cfg (assign (parametersForResponse cfg (familyResponse s r c j x y h k))) =
      rotCoupling (rotScalars s r c j x y) |k*x-h*y| := by
  have hsc := vacuum_resource_scales cfg heta
  have hq : 0 ≤ cfg.vac.c0/cfg.omega := (div_pos cfg.vac.c0_pos cfg.omega_pos).le
  have hkq : freeSpaceK0 cfg*(cfg.vac.c0/cfg.omega)=1 := by
    dsimp [freeSpaceK0]
    field_simp [ne_of_gt cfg.omega_pos, ne_of_gt cfg.vac.c0_pos]
  have hrel := relativePhase_circle x y h k hx hb
  have hgeom : c^2+j^2=1 := by linarith
  have hu := rotScalars_relation s r c j x y hc hx hf
  simp only [parametersForResponse, theta_familyResponse,
    cayleyPreimage_rotatedC s r c j x y h k hr hc hx hb hf,
    spectralDirectBudget, spectralDirectCost, spectralCouplingBudget, spectralCouplingCost,
    recovered_electricBlock, recovered_magneticBlock, recovered_couplingBlock,
    electricRecovery_numerator s r c j x y h k hc hx hf,
    magneticRecovery_numerator s r c j x y h k hc hx hf,
    couplingRecovery_numerator s r c j x y h k hc hx hf,
    opNorm_smul, hsc.1, hsc.2.1, hsc.2.2, abs_of_nonneg hq]
  constructor
  · rw [← mul_max_of_nonneg _ _ hq,
      physicalDirect_norm (rotScalars s r c j x y) c j (k*x-h*y) (h*x+k*y) hgeom hrel,
      ← mul_assoc, hkq, one_mul]
  · rw [physicalCoupling_norm (rotScalars s r c j x y) c j (k*x-h*y) (h*x+k*y) hgeom hrel hu,
      ← mul_assoc, hkq, one_mul]

theorem every_completion_spectral_budgets (cfg : Config) (p : BIParams) (s r c j x y h k : ℝ)
    (hr : r^2+s^2=1) (hc : j^2+c^2=1) (hx : y^2+x^2=1) (hb : k^2+h^2=1)
    (hf : rotF s c x y ≠ 0) (heta : cfg.upper.eta=cfg.vac.eta0)
    (hp : biPowerResponse4 cfg p=familyResponse s r c j x y h k) :
    spectralDirectBudget cfg (assign p)=rotDirect (rotScalars s r c j x y) |k*x-h*y| ∧
    spectralCouplingBudget cfg (assign p)=rotCoupling (rotScalars s r c j x y) |k*x-h*y| := by
  rw [familyResponse_sheet_unique cfg p s r c j x y h k hr hc hx hb hf hp]
  exact recovered_spectral_budgets cfg s r c j x y h k hr hc hx hb hf heta

end GSTC.Scattering.RotatedRankOneRecovery
