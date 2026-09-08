/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.Plates
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Increasing the exponents in a plate maximal estimate

Hölder on the normalized plate measure gives `(M f)^t ≤ M (f^t)` for `t ≥ 1`.
Consequently a local `Lᵖ → Lᑫ` bound with constant `A` gives an
`Lᵗᵖ → Lᵗᑫ` bound with constant `A^(1/t)`. A thickness loss written
as `δ^(-α/p)` retains the same deficit `α` under this operation.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ} {δ t : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

theorem plateAverage_rpow_le (hδ : 0 < δ) (ht : 1 ≤ t)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n))
    (hf : Measurable f) :
    ((∫⁻ x in plate δ V a, f x) / volume (plate δ V a)) ^ t ≤
      (∫⁻ x in plate δ V a, f x ^ t) / volume (plate δ V a) := by
  let μ := (volume (plate δ V a))⁻¹ • volume.restrict (plate δ V a)
  have hprob : IsProbabilityMeasure μ := ⟨by
    simp only [μ, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (volume_plate_pos hδ V a).ne'
      (volume_plate_lt_top δ V a).ne⟩
  have h := ENNReal.rpow_le_rpow
    (eLpNorm_le_eLpNorm_of_exponent_le (μ := μ)
      (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal t by simpa using ENNReal.ofReal_le_ofReal ht)
      hf.aestronglyMeasurable) (zero_le_one.trans ht)
  have he := eLpNorm_enorm_rpow (μ := μ) (p := 1) f (zero_lt_one.trans_le ht)
  simp only [one_mul, enorm_eq_self] at he
  rw [← he] at h
  simpa only [eLpNorm_one_eq_lintegral_enorm, enorm_eq_self, μ,
    lintegral_smul_measure, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem plateMaximal_rpow_le (hδ : 0 < δ) (ht : 1 ≤ t) (hf : Measurable f)
    (V : Grassmannian n k) :
    plateMaximal δ f V ^ t ≤ plateMaximal δ (fun x ↦ f x ^ t) V := by
  rw [← ENNReal.le_rpow_inv_iff (zero_lt_one.trans_le ht)]
  apply iSup_le
  intro a
  rw [ENNReal.le_rpow_inv_iff (zero_lt_one.trans_le ht)]
  exact (plateAverage_rpow_le hδ ht V.val a hf).trans
    (le_iSup (fun a ↦ (∫⁻ x in plate δ V.val a, f x ^ t) / volume (plate δ V.val a)) a)

/-- Increase both exponents without losing the thickness deficit. -/
theorem eLpNorm_plateMaximal_le_of_power (hδ : 0 < δ) (ht : 1 ≤ t)
    {p q A : ℝ≥0∞} {K : Set (EuclideanSpace ℝ (Fin n))}
    {ν : Measure (Grassmannian n k)}
    (hbound : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable g →
      Function.support g ⊆ K → eLpNorm (plateMaximal δ g) q ν ≤ A * eLpNorm g p volume)
    (hf : Measurable f) (hs : Function.support f ⊆ K) :
    eLpNorm (plateMaximal δ f) (q * ENNReal.ofReal t) ν ≤
      A ^ t⁻¹ * eLpNorm f (p * ENNReal.ofReal t) volume := by
  have ht0 := zero_lt_one.trans_le ht
  have hs' : Function.support (fun x ↦ f x ^ t) ⊆ K := by
    intro x hx
    apply hs
    intro hzero
    exact hx (by simp only [hzero, ENNReal.zero_rpow_of_pos ht0])
  have hmono : eLpNorm (fun V ↦ plateMaximal δ f V ^ t) q ν ≤
      eLpNorm (plateMaximal δ (fun x ↦ f x ^ t)) q ν :=
    eLpNorm_mono_enorm fun V ↦ by
      simpa only [enorm_eq_self] using plateMaximal_rpow_le hδ ht hf V
  have h := hmono.trans (hbound _ (hf.pow_const _) hs')
  have he_in := eLpNorm_enorm_rpow (μ := volume) (p := p) f ht0
  simp only [enorm_eq_self] at he_in
  rw [he_in] at h
  have he := eLpNorm_enorm_rpow (μ := ν) (p := q) (plateMaximal δ f) ht0
  simp only [enorm_eq_self] at he
  rw [he] at h
  have hp := ENNReal.rpow_le_rpow h (inv_nonneg.mpr ht0.le)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr ht0.le),
    ← ENNReal.rpow_mul, mul_inv_cancel₀ ht0.ne', ENNReal.rpow_one] using hp

end NKBesicovitch
