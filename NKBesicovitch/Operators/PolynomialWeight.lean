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
