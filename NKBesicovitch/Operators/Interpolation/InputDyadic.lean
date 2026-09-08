/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Interpolation.Dyadic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Two dyadic superlevel series for a nonnegative input

Halving scales cover values at most one. Doubling scales cover larger
values, including infinity. The latter case is handled by a divergent
geometric series, so pointwise finiteness of the input is not assumed.
-/

public section

open Set
open scoped ENNReal

namespace NKBesicovitch

variable {X : Type*}

theorem le_small_dyadic_sum (f : X → ℝ≥0∞) (x : X) (hx : f x ≤ 1) :
    f x ≤ ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
      {y | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  by_cases hz : f x = 0
  · rw [hz]
    exact zero_le
  obtain ⟨j, hj, hj'⟩ := exists_dyadic_scale_ennreal (pos_iff_ne_zero.mpr hz) zero_lt_one
    (by simpa only [ENNReal.ofReal_one] using hx)
  simp only [one_mul] at hj hj'
  have hm : x ∈ {y | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f y} := hj.le
  have hterm := ENNReal.le_tsum (f := fun j : ℕ ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
    {y | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) j
  rw [indicator_of_mem hm, mul_one] at hterm
  exact hj'.trans hterm

theorem le_large_dyadic_sum (f : X → ℝ≥0∞) (x : X) (hx : 1 ≤ f x) :
    f x ≤ ∑' j : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) *
      {y | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  by_cases htop : f x = ∞
  · have hm (j : ℕ) : x ∈ {y | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f y} := by simp [htop]
    simp_rw [indicator_of_mem (hm _), mul_one,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat]
    rw [ENNReal.tsum_geometric_add_one]
    rw [tsub_eq_zero_iff_le.mpr (by norm_num : (1 : ℝ≥0∞) ≤ 2), ENNReal.inv_zero]
    simp
  have hx' : 1 ≤ (f x).toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono htop hx
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near hx' (by norm_num : (1 : ℝ) < 2)
  have hm : x ∈ {y | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f y} := by
    change ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f x
    rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal hj
  have hu : f x ≤ ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) := by
    rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal hj'.le
  have hterm := ENNReal.le_tsum (f := fun j : ℕ ↦ ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) *
    {y | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) j
  rw [indicator_of_mem hm, mul_one] at hterm
  exact hu.trans hterm

theorem le_dyadic_superlevel_sums (f : X → ℝ≥0∞) (x : X) :
    f x ≤ (∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
      {y | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) +
        ∑' j : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) *
          {y | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  rcases le_total (f x) 1 with hsmall | hlarge
  · exact (le_small_dyadic_sum f x hsmall).trans (le_add_of_nonneg_right zero_le)
  · exact (le_large_dyadic_sum f x hlarge).trans (le_add_of_nonneg_left zero_le)

end NKBesicovitch
