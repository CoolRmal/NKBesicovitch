/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Geometric interpolation of powered block estimates

Combining the restricted estimate with the elementary fiber estimate
introduces positive powers of both dyadic scales. All quantities remain
extended nonnegative reals, so zero-volume blocks require no division.
-/

public section

open scoped ENNReal

namespace NKBesicovitch

theorem le_geometric_mean {N A B : ℝ≥0∞} {θ : ℝ} (hA : N ≤ A) (hB : N ≤ B)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) : N ≤ A ^ θ * B ^ (1 - θ) := by
  calc
    N = N ^ θ * N ^ (1 - θ) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hθ (by linarith)]
      simp only [add_sub_cancel, ENNReal.rpow_one]
    _ ≤ _ := mul_le_mul' (ENNReal.rpow_le_rpow hA hθ)
      (ENNReal.rpow_le_rpow hB (by linarith))

theorem interpolate_power_bounds {N A B : ℝ≥0∞} {q θ : ℝ}
    (hq : 0 < q) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hA : N ^ q ≤ A) (hB : N ^ q ≤ B) :
    N ≤ A ^ (θ / q) * B ^ ((1 - θ) / q) := by
  have h := ENNReal.rpow_le_rpow (le_geometric_mean hA hB hθ hθ1) (one_div_pos.mpr hq).le
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hq).le,
    ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one, mul_one_div] using h

theorem interpolate_block_bounds {N C V s a S : ℝ≥0∞} {q β θ : ℝ}
    (hq : 0 < q) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hgeometry : N ^ q ≤ C * V ^ β)
    (helementary : N ^ q ≤ s ^ q * a ^ (β - 1) * S) :
    N ≤ C ^ (θ / q) * V ^ (β * θ / q) * s ^ (1 - θ) *
      a ^ ((β - 1) * (1 - θ) / q) * S ^ ((1 - θ) / q) := by
  have h := interpolate_power_bounds hq hθ hθ1 hgeometry helementary
  have hleft : 0 ≤ θ / q := div_nonneg hθ hq.le
  have hright : 0 ≤ (1 - θ) / q := div_nonneg (by linarith) hq.le
  simp only [ENNReal.mul_rpow_of_nonneg _ _ hleft,
    ENNReal.mul_rpow_of_nonneg _ _ hright, ← ENNReal.rpow_mul] at h
  have he : q * ((1 - θ) / q) = 1 - θ := by field_simp
  simpa only [he, ← mul_div_assoc, mul_assoc] using h

end NKBesicovitch
