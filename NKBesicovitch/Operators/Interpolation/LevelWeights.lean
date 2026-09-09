/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Geometric weights for maximal superlevels

The thresholds `c * b^j`, with `2b < 1` and `c = (1 - 2b)/2`, allocate
exactly half of the output height. Their moment cost is finite whenever
`b^(-P) * 2^(-p) < 1`.
-/

public section

open scoped ENNReal NNReal

namespace NKBesicovitch

theorem tsum_dyadic_level_allocation (b : ℝ≥0) (hb : 2 * b < 1) :
    (∑' j : ℕ, (2 : ℝ≥0∞) ^ j * (((1 - 2 * b) / 2 * b ^ j : ℝ≥0) : ℝ≥0∞)) =
      (2 : ℝ≥0∞)⁻¹ := by
  have hd : (1 : ℝ≥0∞) - 2 * (b : ℝ≥0∞) ≠ 0 := by
    apply ne_of_gt
    exact tsub_pos_iff_lt.mpr (by exact_mod_cast hb)
  have hd' : (1 : ℝ≥0∞) - 2 * (b : ℝ≥0∞) ≠ ∞ := by finiteness
  simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
    ENNReal.coe_sub, ENNReal.coe_one, ENNReal.coe_ofNat]
  have he (j : ℕ) : (2 : ℝ≥0∞) ^ j * (((1 - 2 * (b : ℝ≥0∞)) / 2) * (b : ℝ≥0∞) ^ j) =
      ((1 - 2 * (b : ℝ≥0∞)) / 2) * (2 * (b : ℝ≥0∞)) ^ j := by rw [mul_pow]; ac_rfl
  simp_rw [he]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv]
  calc
    _ = ((1 - 2 * (b : ℝ≥0∞)) * (1 - 2 * (b : ℝ≥0∞))⁻¹) * (2 : ℝ≥0∞)⁻¹ := by
      rw [mul_right_comm]
    _ = _ := by rw [ENNReal.mul_inv_cancel hd hd', one_mul]

private lemma rpow_pow_aux (x : ℝ≥0∞) (u : ℝ) (j : ℕ) :
    (x ^ j) ^ u = (x ^ u) ^ j := by
  rw [← ENNReal.rpow_natCast_mul, ← ENNReal.rpow_mul_natCast, mul_comm]

private lemma level_moment_weight_aux (b c : ℝ≥0) (P p : ℝ) (j : ℕ) :
    (((c * b ^ j : ℝ≥0) : ℝ≥0∞) ^ (-P)) * ENNReal.ofReal ((2 : ℝ) ^ j / 2) ^ (-p) =
      ((c : ℝ≥0∞) ^ (-P) * ((2 : ℝ≥0∞)⁻¹) ^ (-p)) *
        ((b : ℝ≥0∞) ^ (-P) * (2 : ℝ≥0∞) ^ (-p)) ^ j := by
  rw [ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    div_eq_mul_inv, ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top (by finiteness),
    ENNReal.mul_rpow_of_ne_top (by finiteness) (by norm_num)]
  rw [rpow_pow_aux, rpow_pow_aux, mul_pow]
  ac_rfl

theorem tsum_dyadic_level_moment_ne_top (b c : ℝ≥0) (hc : 0 < c) (P p : ℝ)
    (hr : (b : ℝ≥0∞) ^ (-P) * (2 : ℝ≥0∞) ^ (-p) < 1) :
    (∑' j : ℕ, (((c * b ^ j : ℝ≥0) : ℝ≥0∞) ^ (-P)) *
      ENNReal.ofReal ((2 : ℝ) ^ j / 2) ^ (-p)) ≠ ∞ := by
  simp_rw [level_moment_weight_aux, ENNReal.tsum_mul_left]
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_ne_zero (ENNReal.coe_ne_zero.mpr hc.ne') ENNReal.coe_ne_top
    · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  · exact (tsum_geometric_lt_top.mpr hr).ne

private lemma doubling_neg_rpow_aux {q : ℝ} (hq : 1 < q) :
    2 * (2 : ℝ≥0) ^ (-q) < 1 := by
  have he : (2 : ℝ≥0) ^ (1 - q) = 2 * (2 : ℝ≥0) ^ (-q) := by
    rw [sub_eq_add_neg, NNReal.rpow_add (by norm_num), NNReal.rpow_one]
  rw [← he]
  exact NNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hq)

private lemma dyadic_level_ratio_aux {P p q : ℝ} (hqp : q * P < p) :
    (((2 : ℝ≥0) ^ (-q) : ℝ≥0) : ℝ≥0∞) ^ (-P) * (2 : ℝ≥0∞) ^ (-p) < 1 := by
  rw [ENNReal.coe_rpow_of_ne_zero (by norm_num), ENNReal.coe_ofNat,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
  apply ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  nlinarith

/-- Positive geometric thresholds with finite moment cost exist when `1 < q` and `qP < p`. -/
theorem exists_dyadic_level_allocation {P p q : ℝ} (hq : 1 < q) (hqp : q * P < p) :
    ∃ a : ℕ → ℝ≥0, (∀ j, 0 < a j) ∧
      (∑' j : ℕ, (2 : ℝ≥0∞) ^ j * (a j : ℝ≥0∞)) = (2 : ℝ≥0∞)⁻¹ ∧
      (∑' j : ℕ, (a j : ℝ≥0∞) ^ (-P) * ENNReal.ofReal ((2 : ℝ) ^ j / 2) ^ (-p)) ≠ ∞ := by
  let b : ℝ≥0 := 2 ^ (-q)
  let c : ℝ≥0 := (1 - 2 * b) / 2
  have hb : 2 * b < 1 := doubling_neg_rpow_aux hq
  have hc : 0 < c := div_pos (tsub_pos_iff_lt.mpr hb) (by norm_num)
  refine ⟨fun j ↦ c * b ^ j, fun j ↦ mul_pos hc (pow_pos ?_ j),
    tsum_dyadic_level_allocation b hb, ?_⟩
  · dsimp [b]
    positivity
  · exact tsum_dyadic_level_moment_ne_top b c hc P p (dyadic_level_ratio_aux hqp)

end NKBesicovitch
