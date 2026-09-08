/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.Localization
public import NKBesicovitch.Operators.Interpolation.Dyadic
public import NKBesicovitch.Operators.MixedNorm.Sums

/-!
# Decomposing local X-ray values into halving superlevel sets

An indicator transform takes values in `[0,1]`. Superlevel sets at
thresholds `(1/2)^j / 2`, weighted by `(1/2)^j`, dominate it pointwise.
The countable mixed-norm triangle inequality then reduces its norm to
the weighted norms of these Borel superlevel sets.
-/

public section

open MeasureTheory Set NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {m : ℕ}

theorem indicator_localXRay_le_tsum_richLines
    {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)} (hE : MeasurableSet E)
    (Ξ : Set (EuclideanSpace ℝ (Fin m))) (g : Line m) :
    (Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1) g ≤
        ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
          (richLines E Ξ ((1 / 2 : ℝ) ^ j / 2)).indicator (fun _ ↦ (1 : ℝ≥0∞)) g := by
  by_cases hgξ : g ∈ Prod.snd ⁻¹' Ξ
  · rw [indicator_of_mem hgξ]
    by_cases hz : localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1 = 0
    · rw [hz]
      exact zero_le
    have hu : localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1 ≤ ENNReal.ofReal 1 := by
      rw [localXRay_indicator_eq_volume_lineTimes hE, ENNReal.ofReal_one]
      exact volume_lineTimes_le_one E g
    obtain ⟨j, hj, hj'⟩ := exists_dyadic_scale_ennreal (pos_iff_ne_zero.mpr hz) zero_lt_one hu
    simp only [one_mul] at hj hj'
    have hg : g ∈ richLines E Ξ ((1 / 2 : ℝ) ^ j / 2) := ⟨hgξ, hj.le⟩
    have hterm := ENNReal.le_tsum (f := fun j : ℕ ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
      (richLines E Ξ ((1 / 2 : ℝ) ^ j / 2)).indicator (fun _ ↦ (1 : ℝ≥0∞)) g) j
    rw [indicator_of_mem hg, mul_one] at hterm
    exact hj'.trans hterm
  · rw [indicator_of_notMem hgξ]
    exact zero_le

theorem mixedNorm_localXRay_le_tsum_richLines
    {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)} (hE : MeasurableSet E)
    {Ξ : Set (EuclideanSpace ℝ (Fin m))} (hΞ : MeasurableSet Ξ)
    {q r : ℝ≥0∞} (hq : 1 ≤ q) (hr : 1 ≤ r) (hqfin : q ≠ ∞) (hrfin : r ≠ ∞) :
    mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1))
        q r volume volume ≤ ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
          mixedNorm ((richLines E Ξ ((1 / 2 : ℝ) ^ j / 2)).indicator
            (fun _ ↦ (1 : ℝ≥0∞))) q r volume volume := by
  apply (mixedNorm_mono (indicator_localXRay_le_tsum_richLines hE Ξ)).trans
  apply (mixedNorm_tsum_le (fun j ↦ measurable_const.mul
    (measurable_const.indicator (measurableSet_richLines hE hΞ _))) hq hr hqfin hrfin).trans
  apply ENNReal.tsum_le_tsum
  intro j
  exact mixedNorm_const_mul_le (Real.toNNReal ((1 / 2 : ℝ) ^ j)) _

end NKBesicovitch.XRay
