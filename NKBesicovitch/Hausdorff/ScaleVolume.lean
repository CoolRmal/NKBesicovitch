/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Hausdorff.Covers
public import NKBesicovitch.Geometry.Plates
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Volume of a thickened group of comparable balls

At one scale, the sum of the covering radii to power `s` controls the
volume after thickening by that scale, with the factor `δ^(n-s)`.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Hausdorff

private theorem scale_power_le_aux (n : ℕ) {s : ℝ} (hs : 0 ≤ s)
    {δ r : ℝ≥0} (hδ : 0 < δ) (hr : δ / 2 ≤ r) :
    ((2 * δ : ℝ≥0) : ℝ≥0∞) ^ n ≤
      ((2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ s) * (δ : ℝ≥0∞) ^ ((n : ℝ) - s) *
        (r : ℝ≥0∞) ^ s := by
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have he : (δ : ℝ≥0∞) ^ n =
      (δ : ℝ≥0∞) ^ ((n : ℝ) - s) * (δ : ℝ≥0∞) ^ s := by
    rw [← ENNReal.rpow_add _ _ hδ0 ENNReal.coe_ne_top, sub_add_cancel, ENNReal.rpow_natCast]
  have hr' : (δ : ℝ≥0∞) ≤ 2 * (r : ℝ≥0∞) := by
    have h : δ ≤ 2 * r := by
      simpa only [mul_comm] using (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).mp hr
    exact_mod_cast h
  calc
    _ = (2 : ℝ≥0∞) ^ n * ((δ : ℝ≥0∞) ^ ((n : ℝ) - s) * (δ : ℝ≥0∞) ^ s) := by
      rw [ENNReal.coe_mul, ENNReal.coe_ofNat, mul_pow, he]
    _ ≤ (2 : ℝ≥0∞) ^ n * ((δ : ℝ≥0∞) ^ ((n : ℝ) - s) *
        (2 * (r : ℝ≥0∞)) ^ s) := by
      gcongr
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hs]; ac_rfl

theorem volume_thickening_ball_le_cost {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (x : EuclideanSpace ℝ (Fin n)) {δ r : ℝ≥0} (hδ : 0 < δ)
    (hr : δ / 2 ≤ r) (hrδ : r ≤ δ) :
    volume (thickening δ (ball x r)) ≤
      (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        ((2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ s)) *
          (δ : ℝ≥0∞) ^ ((n : ℝ) - s) * (r : ℝ≥0∞) ^ s := by
  have hsub : thickening (δ : ℝ) (ball x r) ⊆ ball x (2 * (δ : ℝ)) :=
    (thickening_ball x δ r).trans (ball_subset_ball (by
      have h : (r : ℝ) ≤ δ := hrδ
      linarith))
  apply (measure_mono hsub).trans
  rw [volume.addHaar_ball_of_pos x (by positivity : (0 : ℝ) < 2 * (δ : ℝ))]
  have h := mul_le_mul_left (scale_power_le_aux n hs hδ hr)
    (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))
  simp only [finrank_euclideanSpace, Fintype.card_fin,
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * (δ : ℝ)),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_coe_nnreal]
  simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat, mul_assoc, mul_comm, mul_left_comm] using h

theorem volume_thickening_ball_union_le_cost {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (r : ℕ → ℝ≥0) (I : Set ℕ)
    {δ : ℝ≥0} (hδ : 0 < δ) (hr : ∀ i ∈ I, δ / 2 ≤ r i ∧ r i ≤ δ) :
    volume (thickening δ (⋃ i ∈ I, ball (x i) (r i))) ≤
      (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        ((2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ s)) *
          (δ : ℝ≥0∞) ^ ((n : ℝ) - s) * (∑' i, (r i : ℝ≥0∞) ^ s) := by
  simp_rw [thickening_iUnion]
  apply (measure_iUnion_le _).trans
  calc
    _ ≤ ∑' i, (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        ((2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ s)) *
          (δ : ℝ≥0∞) ^ ((n : ℝ) - s) * (r i : ℝ≥0∞) ^ s := by
      apply ENNReal.tsum_le_tsum
      intro i
      by_cases hi : i ∈ I
      · simpa [hi] using
          volume_thickening_ball_le_cost hs (x i) hδ (hr i hi).1 (hr i hi).2
      · simp [hi]
    _ = _ := ENNReal.tsum_mul_left

end NKBesicovitch.Hausdorff
