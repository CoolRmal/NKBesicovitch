/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Interpolation.InputDyadic

/-!
# Input superlevels relative to a positive threshold

At each output height, split off a constant half-height and majorize the
remaining input by doubling superlevels. This works pointwise even when the
input takes the value infinity and requires no measurability hypothesis.
-/

public section

open Set
open scoped ENNReal NNReal

namespace NKBesicovitch

variable {X : Type*}

theorem le_scaled_large_dyadic_sum (f : X → ℝ≥0∞) (x : X) {c : ℝ≥0∞}
    (hc : c ≠ 0) (hc' : c ≠ ∞) (hx : c ≤ f x) :
    f x ≤ ∑' j : ℕ, c * (2 : ℝ≥0∞) ^ (j + 1) *
      {y | c * (2 : ℝ≥0∞) ^ j ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  have hnorm : 1 ≤ f x / c := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc) (Or.inl hc'), one_mul]
    exact hx
  have h := mul_le_mul_right (le_large_dyadic_sum (fun y ↦ f y / c) x hnorm) c
  have he : c * (f x / c) = f x := by
    rw [div_eq_mul_inv, mul_comm c, mul_assoc, ENNReal.inv_mul_cancel hc hc', mul_one]
  rw [he, ← ENNReal.tsum_mul_left] at h
  simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.le_div_iff_mul_le (Or.inl hc) (Or.inl hc'), mul_comm _ c, mul_assoc] using h

/-- A half-threshold constant and doubling superlevels majorize every nonnegative input. -/
theorem le_half_add_dyadic_superlevels (f : X → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t) (x : X) :
    f x ≤ (t : ℝ≥0∞) / 2 + ∑' j : ℕ, (t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j *
      {y | (t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j / 2 ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  by_cases hx : f x ≤ (t : ℝ≥0∞) / 2
  · exact hx.trans le_self_add
  · have hc : (t : ℝ≥0∞) / 2 ≠ 0 :=
      (ENNReal.div_pos (ENNReal.coe_ne_zero.mpr ht.ne') (by norm_num)).ne'
    have hc' : (t : ℝ≥0∞) / 2 ≠ ∞ := by finiteness
    have h := le_scaled_large_dyadic_sum f x hc hc' (le_of_not_ge hx)
    have he (j : ℕ) : (t : ℝ≥0∞) / 2 * (2 : ℝ≥0∞) ^ (j + 1) = t * (2 : ℝ≥0∞) ^ j := by
      rw [pow_succ, mul_left_comm _ _ (2 : ℝ≥0∞),
        ENNReal.div_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num), mul_comm]
    have hs (j : ℕ) : (t : ℝ≥0∞) / 2 * (2 : ℝ≥0∞) ^ j = t * (2 : ℝ≥0∞) ^ j / 2 := by
      simp only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    simp only [he, hs] at h
    exact h.trans le_add_self

end NKBesicovitch
