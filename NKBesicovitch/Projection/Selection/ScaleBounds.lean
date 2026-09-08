/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# One polynomial scale for both node reservoirs

If `0 < x ≤ 1` and `r = x/100`, both the outer and inner reservoir
thresholds are at least `r^8`. Thus input bounds of exponent `B` are
bounded uniformly by `(100/x)^(8B)`.
-/

@[expose] public section

namespace NKBesicovitch.Projection.Selection

theorem radius_pow_eight_le_outer_threshold {x : ℝ} (hx : 0 ≤ x) :
    (x / 100) ^ 8 ≤ x / 100 * x ^ 7 / 320000000000 := by
  calc
    _ = x ^ 8 / 100 ^ 8 := div_pow _ _ _
    _ ≤ x ^ 8 / 32000000000000 :=
      div_le_div_of_nonneg_left (pow_nonneg hx _) (by norm_num) (by norm_num)
    _ = _ := by ring

theorem radius_pow_eight_le_inner_threshold {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (x / 100) ^ 8 ≤ x / 100 * x ^ 5 / 8000000 := by
  calc
    _ ≤ (x / 100) ^ 6 := pow_le_pow_of_le_one (by positivity)
      (by linarith) (by norm_num)
    _ = x ^ 6 / 100 ^ 6 := div_pow _ _ _
    _ ≤ x ^ 6 / 800000000 :=
      div_le_div_of_nonneg_left (pow_nonneg hx _) (by norm_num) (by norm_num)
    _ = _ := by ring

theorem inv_pow_le_of_radius_pow_le {x τ : ℝ} (hx : 0 < x)
    (hτ : (x / 100) ^ 8 ≤ τ) (B : ℕ) : τ⁻¹ ^ B ≤ (100 / x) ^ (8 * B) := by
  have hr : 0 < (x / 100) ^ 8 := by positivity
  calc
    _ ≤ (((x / 100) ^ 8)⁻¹) ^ B :=
      pow_le_pow_left₀ (inv_nonneg.mpr (hr.trans_le hτ).le)
        ((inv_le_inv₀ (hr.trans_le hτ) hr).mpr hτ) B
    _ = _ := by rw [← inv_pow, ← pow_mul, inv_div]

end NKBesicovitch.Projection.Selection
