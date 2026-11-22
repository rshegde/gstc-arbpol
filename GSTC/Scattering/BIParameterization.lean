/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Power
public import GSTC.Scattering.Reciprocity

open scoped Matrix

public section

namespace GSTC.Scattering

theorem star_I : star (Complex.I : ℂ) = -Complex.I := by
  rw [Complex.star_def]
  exact Complex.conj_I

theorem eq_star_iff_eq_ofReal_re {z : ℂ} (h : z = star z) : z = ↑(z.re) := by
  rw [Complex.star_def] at h
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp h.symm
  have hre : z.re = r := by rw [hr]; exact Complex.ofReal_re r
  refine hr.trans ?_
  congr 1
  exact hre.symm

theorem eq_neg_star_iff_eq_I_mul_im {z : ℂ} (h : z = -star z) :
    z = Complex.I * (z.im : ℂ) := by
  rw [Complex.star_def] at h
  have hre : z.re = 0 := by
    have h' := congrArg Complex.re h
    rw [Complex.neg_re, Complex.conj_re] at h'
    linarith
  apply Complex.ext
  · rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring_nf
    exact hre
  · rw [Complex.I_mul_im, Complex.ofReal_re]

structure BIParams where

  ee00 : ℝ

  ee01 : ℝ

  ee11 : ℝ

  mm00 : ℝ

  mm01 : ℝ

  mm11 : ℝ

  g00 : ℝ

  g01 : ℝ

  g10 : ℝ

  g11 : ℝ

@[expose] def BIParams.eeBlock (p : BIParams) : Ten2 :=
  !![(p.ee00 : ℂ), (p.ee01 : ℂ); (p.ee01 : ℂ), (p.ee11 : ℂ)]

@[expose] def BIParams.mmBlock (p : BIParams) : Ten2 :=
  !![(p.mm00 : ℂ), (p.mm01 : ℂ); (p.mm01 : ℂ), (p.mm11 : ℂ)]

@[expose] def BIParams.emBlock (p : BIParams) : Ten2 :=
  !![Complex.I * (p.g00 : ℂ), Complex.I * (p.g01 : ℂ);
     Complex.I * (p.g10 : ℂ), Complex.I * (p.g11 : ℂ)]

@[expose] def BIParams.meBlock (p : BIParams) : Ten2 :=
  !![-(Complex.I * (p.g00 : ℂ)), -(Complex.I * (p.g10 : ℂ));
     -(Complex.I * (p.g01 : ℂ)), -(Complex.I * (p.g11 : ℂ))]

@[expose] def encode (p : BIParams) : Susceptibilities :=
  ⟨ten3OfTT p.eeBlock, ten3OfTT p.mmBlock, ten3OfTT p.emBlock, ten3OfTT p.meBlock⟩

@[expose] def decode (sus : Susceptibilities) : BIParams where
  ee00 := (chiTT sus.ee 0 0).re
  ee01 := (chiTT sus.ee 0 1).re
  ee11 := (chiTT sus.ee 1 1).re
  mm00 := (chiTT sus.mm 0 0).re
  mm01 := (chiTT sus.mm 0 1).re
  mm11 := (chiTT sus.mm 1 1).re
  g00 := (chiTT sus.em 0 0).im
  g01 := (chiTT sus.em 0 1).im
  g10 := (chiTT sus.em 1 0).im
  g11 := (chiTT sus.em 1 1).im

theorem encode_ee_sym (p : BIParams) (i j : Fin 3) :
    (encode p).ee i j = (encode p).ee j i := by
  fin_cases i <;> fin_cases j <;>
    simp [encode, ten3OfTT, BIParams.eeBlock, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem encode_mm_sym (p : BIParams) (i j : Fin 3) :
    (encode p).mm i j = (encode p).mm j i := by
  fin_cases i <;> fin_cases j <;>
    simp [encode, ten3OfTT, BIParams.mmBlock, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem encode_em_me (p : BIParams) (i j : Fin 3) :
    (encode p).em i j = -((encode p).me j i) := by
  fin_cases i <;> fin_cases j <;>
    simp [encode, ten3OfTT, BIParams.emBlock, BIParams.meBlock,
      Matrix.cons_val_zero, Matrix.cons_val_one]

theorem encode_reciprocal (p : BIParams) : (encode p).Reciprocal :=
  ⟨encode_ee_sym p, encode_mm_sym p, encode_em_me p⟩

theorem encode_ee_hermitian (p : BIParams) (i j : Fin 3) :
    (encode p).ee i j = star ((encode p).ee j i) := by
  fin_cases i <;> fin_cases j <;>
    simp [encode, ten3OfTT, BIParams.eeBlock, Matrix.cons_val_zero, Matrix.cons_val_one,
      star_ofReal]

theorem encode_mm_hermitian (p : BIParams) (i j : Fin 3) :
    (encode p).mm i j = star ((encode p).mm j i) := by
  fin_cases i <;> fin_cases j <;>
    simp [encode, ten3OfTT, BIParams.mmBlock, Matrix.cons_val_zero, Matrix.cons_val_one,
      star_ofReal]

theorem encode_em_hermitian (p : BIParams) (i j : Fin 3) :
    (encode p).em i j = star ((encode p).me j i) := by
  fin_cases i <;> fin_cases j <;>
    simp [encode, ten3OfTT, BIParams.emBlock, BIParams.meBlock,
      Matrix.cons_val_zero, Matrix.cons_val_one, star_neg]

theorem encode_lossless (p : BIParams) : (encode p).Lossless :=
  ⟨encode_ee_hermitian p, encode_mm_hermitian p, encode_em_hermitian p⟩

theorem encode_decode (p : BIParams) : decode (encode p) = p := by
  cases p with
  | mk ee00 ee01 ee11 mm00 mm01 mm11 g00 g01 g10 g11 =>
    simp [decode, encode, chiTT_ten3OfTT, BIParams.eeBlock, BIParams.mmBlock,
      BIParams.emBlock, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.ofReal_re]

theorem ee_00_real (sus : Susceptibilities) (hL : sus.Lossless) :
    sus.ee 0 0 = ↑((sus.ee 0 0).re) :=
  eq_star_iff_eq_ofReal_re (hL.1 0 0)

theorem ee_01_real (sus : Susceptibilities) (hR : sus.Reciprocal) (hL : sus.Lossless) :
    sus.ee 0 1 = ↑((sus.ee 0 1).re) := by
  apply eq_star_iff_eq_ofReal_re
  calc sus.ee 0 1 = sus.ee 1 0 := hR.1 0 1
    _ = star (sus.ee 0 1) := hL.1 1 0

theorem ee_11_real (sus : Susceptibilities) (hL : sus.Lossless) :
    sus.ee 1 1 = ↑((sus.ee 1 1).re) :=
  eq_star_iff_eq_ofReal_re (hL.1 1 1)

theorem mm_00_real (sus : Susceptibilities) (hL : sus.Lossless) :
    sus.mm 0 0 = ↑((sus.mm 0 0).re) :=
  eq_star_iff_eq_ofReal_re (hL.2.1 0 0)

theorem mm_01_real (sus : Susceptibilities) (hR : sus.Reciprocal) (hL : sus.Lossless) :
    sus.mm 0 1 = ↑((sus.mm 0 1).re) := by
  apply eq_star_iff_eq_ofReal_re
  calc sus.mm 0 1 = sus.mm 1 0 := hR.2.1 0 1
    _ = star (sus.mm 0 1) := hL.2.1 1 0

theorem mm_11_real (sus : Susceptibilities) (hL : sus.Lossless) :
    sus.mm 1 1 = ↑((sus.mm 1 1).re) :=
  eq_star_iff_eq_ofReal_re (hL.2.1 1 1)

theorem nb_00_pure (sus : Susceptibilities) (hR : sus.Reciprocal) (hL : sus.Lossless) :
    sus.em 0 0 = Complex.I * ((sus.em 0 0).im : ℂ) := by
  apply eq_neg_star_iff_eq_I_mul_im
  have hme : sus.me 0 0 = -(sus.em 0 0) := by rw [hR.2.2 0 0]; ring
  calc sus.em 0 0 = star (sus.me 0 0) := hL.2.2 0 0
    _ = -star (sus.em 0 0) := by rw [hme, star_neg]

theorem nb_01_pure (sus : Susceptibilities) (hR : sus.Reciprocal) (hL : sus.Lossless) :
    sus.em 0 1 = Complex.I * ((sus.em 0 1).im : ℂ) := by
  apply eq_neg_star_iff_eq_I_mul_im
  have hme : sus.me 1 0 = -(sus.em 0 1) := by rw [hR.2.2 0 1]; ring
  calc sus.em 0 1 = star (sus.me 1 0) := hL.2.2 0 1
    _ = -star (sus.em 0 1) := by rw [hme, star_neg]

theorem nb_10_pure (sus : Susceptibilities) (hR : sus.Reciprocal) (hL : sus.Lossless) :
    sus.em 1 0 = Complex.I * ((sus.em 1 0).im : ℂ) := by
  apply eq_neg_star_iff_eq_I_mul_im
  have hme : sus.me 0 1 = -(sus.em 1 0) := by rw [hR.2.2 1 0]; ring
  calc sus.em 1 0 = star (sus.me 0 1) := hL.2.2 1 0
    _ = -star (sus.em 1 0) := by rw [hme, star_neg]

theorem nb_11_pure (sus : Susceptibilities) (hR : sus.Reciprocal) (hL : sus.Lossless) :
    sus.em 1 1 = Complex.I * ((sus.em 1 1).im : ℂ) := by
  apply eq_neg_star_iff_eq_I_mul_im
  have hme : sus.me 1 1 = -(sus.em 1 1) := by rw [hR.2.2 1 1]; ring
  calc sus.em 1 1 = star (sus.me 1 1) := hL.2.2 1 1
    _ = -star (sus.em 1 1) := by rw [hme, star_neg]

theorem decode_eeBlock (sus : Susceptibilities) (hR : sus.Reciprocal) (hL : sus.Lossless) :
    (decode sus).eeBlock = chiTT sus.ee := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BIParams.eeBlock, decode, chiTT, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    first
      | exact (ee_00_real sus hL).symm
      | exact (ee_01_real sus hR hL).symm
      | exact (ee_11_real sus hL).symm
      | calc ↑((sus.ee 0 1).re) = sus.ee 0 1 := (ee_01_real sus hR hL).symm
          _ = sus.ee 1 0 := hR.1 0 1

theorem decode_mmBlock (sus : Susceptibilities) (hR : sus.Reciprocal) (hL : sus.Lossless) :
    (decode sus).mmBlock = chiTT sus.mm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BIParams.mmBlock, decode, chiTT, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    first
      | exact (mm_00_real sus hL).symm
      | exact (mm_01_real sus hR hL).symm
      | exact (mm_11_real sus hL).symm
      | calc ↑((sus.mm 0 1).re) = sus.mm 0 1 := (mm_01_real sus hR hL).symm
          _ = sus.mm 1 0 := hR.2.1 0 1

theorem decode_emBlock (sus : Susceptibilities) (hR : sus.Reciprocal) (hL : sus.Lossless) :
    (decode sus).emBlock = chiTT sus.em := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BIParams.emBlock, decode, chiTT, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    first
      | exact (nb_00_pure sus hR hL).symm
      | exact (nb_01_pure sus hR hL).symm
      | exact (nb_10_pure sus hR hL).symm
      | exact (nb_11_pure sus hR hL).symm

theorem decode_meBlock (sus : Susceptibilities) (hR : sus.Reciprocal) (hL : sus.Lossless) :
    (decode sus).meBlock = chiTT sus.me := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BIParams.meBlock, decode, chiTT, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals first
    | rw [← nb_00_pure sus hR hL, hR.2.2 0 0]; ring
    | rw [← nb_10_pure sus hR hL, hR.2.2 1 0]; ring
    | rw [← nb_01_pure sus hR hL, hR.2.2 0 1]; ring
    | rw [← nb_11_pure sus hR hL, hR.2.2 1 1]; ring

@[expose] def Tangential (sus : Susceptibilities) : Prop :=
  sus.ee = ten3OfTT (chiTT sus.ee) ∧ sus.mm = ten3OfTT (chiTT sus.mm) ∧
  sus.em = ten3OfTT (chiTT sus.em) ∧ sus.me = ten3OfTT (chiTT sus.me)

theorem decode_encode (sus : Susceptibilities) (hR : sus.Reciprocal) (hL : sus.Lossless)
    (hT : Tangential sus) : encode (decode sus) = sus := by
  have hself : sus = ⟨sus.ee, sus.mm, sus.em, sus.me⟩ := rfl
  rw [hself]
  simp only [encode, Susceptibilities.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [decode_eeBlock sus hR hL]
    exact hT.1.symm
  · rw [decode_mmBlock sus hR hL]
    exact hT.2.1.symm
  · rw [decode_emBlock sus hR hL]
    exact hT.2.2.1.symm
  · rw [decode_meBlock sus hR hL]
    exact hT.2.2.2.symm

theorem existsUnique_encoding (sus : Susceptibilities) (hR : sus.Reciprocal)
    (hL : sus.Lossless) (hT : Tangential sus) :
    ∃! p : BIParams, encode p = sus := by
  refine ⟨decode sus, decode_encode sus hR hL hT, ?_⟩
  intro p hp
  have hpe : p = decode sus := by
    rw [← hp]
    exact (encode_decode p).symm
  exact hpe

end GSTC.Scattering
