/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrable polynomial decay profiles

Inverse polynomial weights whose degree exceeds the dimension belong to every
finite `Lᵖ` space with `p ≥ 1`. These profiles control the spatial tails of
smoothed transforms.
-/

public section

open MeasureTheory Module
open scoped ENNReal

namespace NKBesicovitch

/-- Polynomial weights of a sum are bounded by the product of the two weights. -/
theorem one_add_norm_sq_pow_add_le {E : Type*} [NormedAddCommGroup E] (x y : E) (A : ℕ) :
    (1 + ‖x + y‖ ^ 2) ^ A ≤ 2 ^ A * (1 + ‖x‖ ^ 2) ^ A * (1 + ‖y‖ ^ 2) ^ A := by
  have h : 1 + ‖x + y‖ ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2) := by
    have hn := norm_add_le x y
    have hs := sq_le_sq₀ (norm_nonneg (x + y)) (by positivity) |>.mpr hn
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖)]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) h A

/-- Translating an inverse polynomial weight increases it by at most a polynomial factor. -/
theorem inv_one_add_norm_sq_pow_add_le {E : Type*} [NormedAddCommGroup E] (x y : E) (A : ℕ) :
    ((1 + ‖x + y‖ ^ 2) ^ A)⁻¹ ≤
      (2 ^ A * (1 + ‖x‖ ^ 2) ^ A) * ((1 + ‖y‖ ^ 2) ^ A)⁻¹ := by
  have h := one_add_norm_sq_pow_add_le (-x) (x + y) A
  simp only [neg_add_cancel_left, norm_neg] at h
  rw [← div_eq_mul_inv, ← one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul] using h

/-- Inverse polynomial decay of degree above the dimension is in every finite `Lᵖ`, `p ≥ 1`. -/
theorem memLp_inv_one_add_norm_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {N : ℕ} (hN : finrank ℝ E < N)
    {p : ℝ} (hp : 1 ≤ p) : MemLp (fun x : E ↦ ((1 + ‖x‖) ^ N)⁻¹) (ENNReal.ofReal p) μ := by
  have hp₀ : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hNp : (finrank ℝ E : ℝ) < (N : ℝ) * p := by
    exact (Nat.cast_lt.mpr hN).trans_le (le_mul_of_one_le_right (by positivity) hp)
  rw [← integrable_norm_rpow_iff (by fun_prop) (by positivity) ENNReal.ofReal_ne_top]
  convert (integrable_one_add_norm (μ := μ) hNp) using 1
  ext x
  rw [ENNReal.toReal_ofReal hp₀.le, Real.norm_of_nonneg (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_neg (by positivity), ← Real.rpow_mul (by positivity)]
  congr 1
  ring

end NKBesicovitch
