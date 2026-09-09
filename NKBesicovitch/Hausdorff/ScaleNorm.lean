/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Hausdorff.ScaleVolume
public import NKBesicovitch.Induction.Globalization
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# A maximal norm bound for each covering scale

Combining the plate deficit with the volume of a thickened ball group
leaves the scale power `(n-s-α)/p`, which is positive below the proposed
Hausdorff-dimension threshold.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Hausdorff

private theorem scale_norm_factor_aux {n : ℕ} {s α p : ℝ} (hp : 0 < p)
    (C : ℝ≥0) (A t : ℝ≥0∞) {δ : ℝ≥0} (hδ : 0 < δ) :
    (C * δ ^ (-α / p) : ℝ≥0) * (A * (δ : ℝ≥0∞) ^ ((n : ℝ) - s) * t) ^ (1 / p) =
      ((C : ℝ≥0∞) * A ^ (1 / p)) * (δ : ℝ≥0∞) ^ (((n : ℝ) - s - α) / p) *
        t ^ (1 / p) := by
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδ.ne']
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le), ← ENNReal.rpow_mul]
  calc
    _ = ((C : ℝ≥0∞) * A ^ (1 / p)) *
        ((δ : ℝ≥0∞) ^ (-α / p) * (δ : ℝ≥0∞) ^ (((n : ℝ) - s) * (1 / p))) *
          t ^ (1 / p) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add _ _ hδ0 ENNReal.coe_ne_top]
      congr 2
      congr 1
      ring

/-- A plate deficit controls each group of comparable covering balls. -/
theorem exists_scale_norm_bound {n k : ℕ} {hkn : k ≤ n} {α p s : ℝ}
    (hp : 0 < p) (hs : 0 ≤ s) (h : Induction.HasPlateEstimate hkn α p) :
    ∃ B : ℝ≥0, ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)) (r : ℕ → ℝ≥0) (I : Set ℕ)
      (δ : ℝ≥0), 0 < δ → δ ≤ 1 → (∀ i ∈ I, δ / 2 ≤ r i ∧ r i ≤ δ) →
        eLpNorm (plateMaximal δ
          ((thickening δ (⋃ i ∈ I, ball (x i) (r i))).indicator (fun _ ↦ (1 : ℝ≥0∞))))
          (ENNReal.ofReal p) (Grassmannian.probability hkn) ≤
            (B : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (((n : ℝ) - s - α) / p) *
              (∑' i, (r i : ℝ≥0∞) ^ s) ^ (1 / p) := by
  obtain ⟨C, hC⟩ := h.global_bound hp
  let A : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
    ((2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ s)
  have hAf : A ≠ ∞ := by dsimp [A]; finiteness
  have hBf : (C : ℝ≥0∞) * A ^ (1 / p) ≠ ∞ := by finiteness
  refine ⟨((C : ℝ≥0∞) * A ^ (1 / p)).toNNReal, ?_⟩
  intro x r I δ hδ hδ1 hr
  let U := thickening (δ : ℝ) (⋃ i ∈ I, ball (x i) (r i))
  have hU : MeasurableSet U := isOpen_thickening.measurableSet
  have hnorm : eLpNorm (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) (ENNReal.ofReal p) volume =
      volume U ^ (1 / p) := by
    rw [eLpNorm_indicator_const hU (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top]
    simp only [enorm_eq_self, one_mul, ENNReal.toReal_ofReal hp.le]
  rw [ENNReal.coe_toNNReal hBf]
  calc
    _ ≤ (C * δ ^ (-α / p) : ℝ≥0) * volume U ^ (1 / p) := by
      simpa only [hnorm] using hC δ hδ hδ1
        (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) (measurable_const.indicator hU)
    _ ≤ (C * δ ^ (-α / p) : ℝ≥0) *
        (A * (δ : ℝ≥0∞) ^ ((n : ℝ) - s) * (∑' i, (r i : ℝ≥0∞) ^ s)) ^ (1 / p) :=
      mul_le_mul_right (ENNReal.rpow_le_rpow
        (volume_thickening_ball_union_le_cost hs x r I hδ hr) (one_div_nonneg.mpr hp.le)) _
    _ = _ := scale_norm_factor_aux hp C A _ hδ

end NKBesicovitch.Hausdorff
