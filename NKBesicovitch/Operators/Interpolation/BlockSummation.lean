/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Interpolation.BlockScaling
public import NKBesicovitch.Operators.Interpolation.GeometricSeries

/-!
# Uniform summation of the interpolated block bounds

All geometric constants, the initial fiber scale, and the direction measure
are fixed before choosing the input volume or block norms. Summing both
dyadic indices therefore leaves only the input-volume power.
-/

public section

open scoped ENNReal

namespace NKBesicovitch

theorem exists_interpolated_series_constant {C S : ℝ≥0∞} {B q β θ : ℝ}
    (hC : C ≠ ∞) (hS : S ≠ ∞) (hB : 0 < B) (hq : 0 < q) (hβ : 1 < β)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (V : ℝ≥0∞) (N : ℕ → ℕ → ℝ≥0∞),
      (∀ j l, ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) * N j l ≤
        C ^ (θ / q) * V ^ (β * θ / q) * ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ^ (1 - θ) *
          ENNReal.ofReal (B * (1 / 2 : ℝ) ^ l) ^ ((β - 1) * (1 - θ) / q) *
            S ^ ((1 - θ) / q)) →
      (∑' j : ℕ, ∑' l : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * N j l) ≤
        ENNReal.ofReal D * V ^ (β * θ / q) := by
  have hu : 0 < 1 - θ := by linarith
  have hv : 0 < (β - 1) * (1 - θ) / q := by positivity
  have hw : 0 < (1 - θ) / q := div_pos hu hq
  let A := 2 * C ^ (θ / q) * ENNReal.ofReal B ^ ((β - 1) * (1 - θ) / q) *
    S ^ ((1 - θ) / q)
  have hA : A ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.rpow_ne_top_of_nonneg (div_nonneg hθ hq.le) hC))
      (ENNReal.rpow_ne_top_of_nonneg hv.le ENNReal.ofReal_ne_top))
    (ENNReal.rpow_ne_top_of_nonneg hw.le hS)
  obtain ⟨D, _, hsum⟩ := exists_double_dyadic_constant hu hv
  have hfin : ENNReal.ofReal D * A ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA
  refine ⟨(ENNReal.ofReal D * A).toReal + 1, by positivity, fun V N hN ↦ ?_⟩
  have hcoeff : ENNReal.ofReal D * A ≤ ENNReal.ofReal ((ENNReal.ofReal D * A).toReal + 1) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc
    _ ≤ ∑' j : ℕ, ∑' l : ℕ, (A * V ^ (β * θ / q)) *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ^ (1 - θ) *
          ENNReal.ofReal ((1 / 2 : ℝ) ^ l) ^ ((β - 1) * (1 - θ) / q) := by
      apply ENNReal.tsum_le_tsum
      intro j
      apply ENNReal.tsum_le_tsum
      intro l
      have h := normalize_dyadic_block_bound (by positivity) hB.le hu.le hv.le (hN j l)
      convert h using 1
      dsimp [A]
      ring
    _ ≤ ENNReal.ofReal D * (A * V ^ (β * θ / q)) := hsum _
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_left hcoeff _

end NKBesicovitch
