/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.FiberBlocks
public import NKBesicovitch.Operators.Interpolation.Dyadic
public import NKBesicovitch.Operators.MixedNorm.Sums

/-!
# Decomposing a line family by parallel-fiber size

With one finite upper bound on the fiber measures, halving scales cover
every positive-measure fiber. A zero-measure fiber contributes zero almost
everywhere in the intercept variable. This gives a mixed-norm upper bound
by the countable sum of the comparable-fiber pieces.
-/

public section

open MeasureTheory Set NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {m : ℕ}

theorem indicator_le_tsum_fiberBlock_ae (F : Set (Line m)) {B : ℝ} (hB : 0 < B)
    (hupper : ∀ ξ, volume ((fun x ↦ (x, ξ)) ⁻¹' F) ≤ ENNReal.ofReal B)
    (ξ : EuclideanSpace ℝ (Fin m)) :
    ∀ᵐ x ∂volume, F.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x, ξ) ≤
      ∑' l : ℕ, (fiberBlock F (B * (1 / 2 : ℝ) ^ l)).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) (x, ξ) := by
  by_cases hzero : volume ((fun x ↦ (x, ξ)) ⁻¹' F) = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with x hx
    change (x, ξ) ∉ F at hx
    rw [indicator_of_notMem hx]
    exact zero_le
  · obtain ⟨l, hl, hl'⟩ := exists_dyadic_scale_ennreal (pos_iff_ne_zero.mpr hzero) hB (hupper ξ)
    apply ae_of_all
    intro x
    by_cases hx : (x, ξ) ∈ F
    · have hg : (x, ξ) ∈ fiberBlock F (B * (1 / 2 : ℝ) ^ l) := ⟨hx, hl, hl'⟩
      rw [indicator_of_mem hx]
      calc
        1 = (fiberBlock F (B * (1 / 2 : ℝ) ^ l)).indicator
            (fun _ ↦ (1 : ℝ≥0∞)) (x, ξ) := by rw [indicator_of_mem hg]
        _ ≤ _ := ENNReal.le_tsum l
    · rw [indicator_of_notMem hx]
      exact zero_le

theorem mixedNorm_indicator_le_tsum_fiberBlock {F : Set (Line m)} (hF : MeasurableSet F)
    {B : ℝ} (hB : 0 < B)
    (hupper : ∀ ξ, volume ((fun x ↦ (x, ξ)) ⁻¹' F) ≤ ENNReal.ofReal B)
    {q r : ℝ≥0∞} (hq : 1 ≤ q) (hr : 1 ≤ r) (hqfin : q ≠ ∞) (hrfin : r ≠ ∞) :
    mixedNorm (F.indicator (fun _ ↦ (1 : ℝ≥0∞))) q r volume volume ≤
      ∑' l : ℕ, mixedNorm ((fiberBlock F (B * (1 / 2 : ℝ) ^ l)).indicator
        (fun _ ↦ (1 : ℝ≥0∞))) q r volume volume := by
  calc
    _ ≤ mixedNorm (fun p ↦ ∑' l : ℕ, (fiberBlock F (B * (1 / 2 : ℝ) ^ l)).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) p) q r volume volume :=
      mixedNorm_mono_fiber_ae (ae_of_all _ (indicator_le_tsum_fiberBlock_ae F hB hupper))
    _ ≤ _ := mixedNorm_tsum_le
      (fun l ↦ measurable_const.indicator (measurableSet_fiberBlock hF _)) hq hr hqfin hrfin

end NKBesicovitch.XRay
