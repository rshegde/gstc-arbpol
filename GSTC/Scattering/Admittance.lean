/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Power

public section

open scoped Matrix

namespace GSTC.Scattering

structure FieldPair where
  e : Vec2
  h : Vec2

@[expose] def powerPairing (u v : FieldPair) : ℂ := hc u.e v.e - hc v.h u.h

structure SheetResponse where
  ee : Ten2
  em : Ten2
  me : Ten2
  mm : Ten2

@[expose] def SheetResponse.electric (R : SheetResponse) (e h : Vec2) : Vec2 :=
  R.ee *ᵥ e + R.em *ᵥ h

@[expose] def SheetResponse.magnetic (R : SheetResponse) (e h : Vec2) : Vec2 :=
  R.me *ᵥ e + R.mm *ᵥ h

@[expose] def SheetResponse.act (R : SheetResponse) (u : FieldPair) : FieldPair :=
  ⟨R.electric u.e u.h, R.magnetic u.e u.h⟩

@[expose] noncomputable def sheetResponse (cfg : Config) (sus : Susceptibilities) :
    SheetResponse where
  ee := (cfg.vac.eps0 : ℂ) • (chiTT sus.ee)
  em := (1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.em)
  me := (1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.me)
  mm := (cfg.vac.mu0 : ℂ) • (chiTT sus.mm)

@[expose] def SheetResponse.Hermitian (R : SheetResponse) : Prop :=
  (∀ i j, R.ee i j = star (R.ee j i)) ∧
  (∀ i j, R.mm i j = star (R.mm j i)) ∧
  (∀ i j, R.em i j = star (R.me j i))

theorem smul_hermitian (c : ℂ) (hc : star c = c) (A : Ten2)
    (hA : ∀ i j, A i j = star (A j i)) :
    ∀ i j, c • A i j = star (c • A j i) := by
  intro i j
  have h := hA i j
  simp only [smul_eq_mul]
  rw [star_mul, hc, h]
  ring

theorem smul_cross (c : ℂ) (hc : star c = c) (B C : Ten2)
    (hBC : ∀ i j, B i j = star (C j i)) :
    ∀ i j, c • B i j = star (c • C j i) := by
  intro i j
  have h := hBC i j
  simp only [smul_eq_mul]
  rw [star_mul, hc, h]
  ring

theorem smul_hermitian' (c : ℂ) (hc : star c = c) (A : Ten2)
    (hA : ∀ i j, A i j = star (A j i)) (i j : Fin 2) :
    (c • A) i j = star ((c • A) j i) := by
  rw [Matrix.smul_apply, Matrix.smul_apply]
  exact smul_hermitian c hc A hA i j

theorem smul_cross' (c : ℂ) (hc : star c = c) (B C : Ten2)
    (hBC : ∀ i j, B i j = star (C j i)) (i j : Fin 2) :
    (c • B) i j = star ((c • C) j i) := by
  rw [Matrix.smul_apply, Matrix.smul_apply]
  exact smul_cross c hc B C hBC i j

theorem SheetResponse.power_real (R : SheetResponse) (hR : R.Hermitian)
    (u : FieldPair) :
    star (powerPairing u (R.act u)) = powerPairing u (R.act u) := by
  have hcross : hc u.e (R.em *ᵥ u.h) = hc (R.me *ᵥ u.e) u.h :=
    hc_cross R.em R.me hR.2.2 u.e u.h
  have hA : star (hc u.e (R.ee *ᵥ u.e)) = hc u.e (R.ee *ᵥ u.e) :=
    star_hc_hermitian R.ee hR.1 u.e
  have hD : star (hc (R.mm *ᵥ u.h) u.h) = hc (R.mm *ᵥ u.h) u.h := by
    have h := star_hc_hermitian R.mm hR.2.1 u.h
    calc star (hc (R.mm *ᵥ u.h) u.h) = star (star (hc u.h (R.mm *ᵥ u.h))) := by
          rw [hc_swap u.h (R.mm *ᵥ u.h)]
      _ = hc u.h (R.mm *ᵥ u.h) := star_star _
      _ = hc (R.mm *ᵥ u.h) u.h := by rw [hc_swap u.h (R.mm *ᵥ u.h), h]
  have hval : powerPairing u (R.act u)
      = hc u.e (R.ee *ᵥ u.e) - hc (R.mm *ᵥ u.h) u.h := by
    unfold powerPairing SheetResponse.act SheetResponse.electric SheetResponse.magnetic
    simp only [hc_add_right, hc_add_left]
    rw [hcross]
    ring
  calc star (powerPairing u (R.act u))
      = star (hc u.e (R.ee *ᵥ u.e) - hc (R.mm *ᵥ u.h) u.h) := by rw [hval]
    _ = star (hc u.e (R.ee *ᵥ u.e)) - star (hc (R.mm *ᵥ u.h) u.h) := by rw [star_sub]
    _ = hc u.e (R.ee *ᵥ u.e) - hc (R.mm *ᵥ u.h) u.h := by rw [hA, hD]
    _ = powerPairing u (R.act u) := by rw [hval]

theorem sheetResponse_hermitian (cfg : Config) (sus : Susceptibilities)
    (h : sus.Lossless) : (sheetResponse cfg sus).Hermitian := by
  have hTT := Susceptibilities.Lossless.chiTT_hermitian sus h
  have hcreal : star (1 / (cfg.vac.c0 : ℂ)) = 1 / (cfg.vac.c0 : ℂ) := by
    rw [div_eq_mul_inv, one_mul, star_inv₀, star_ofReal]
  unfold SheetResponse.Hermitian
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact smul_hermitian' (cfg.vac.eps0 : ℂ) (star_ofReal cfg.vac.eps0)
      (chiTT sus.ee) hTT.1 i j
  · intro i j
    exact smul_hermitian' (cfg.vac.mu0 : ℂ) (star_ofReal cfg.vac.mu0)
      (chiTT sus.mm) hTT.2.1 i j
  · intro i j
    exact smul_cross' (1 / (cfg.vac.c0 : ℂ)) hcreal
      (chiTT sus.em) (chiTT sus.me) hTT.2.2 i j

end GSTC.Scattering
