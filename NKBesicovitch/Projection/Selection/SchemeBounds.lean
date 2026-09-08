/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.Scheme

/-!
# Applying a scheme with a lower bound on time-set measure

A positive lower bound on the time-set measure gives uniform bounds
on selection volume, parameter coordinates, and projection constants.
These forms apply to the outer and inner reservoirs at a corner node.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

theorem volume_lower_of_measure_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) {r : ℝ} (hr : 0 < r) (hmeasure : ENNReal.ofReal r ≤ volume I) :
    ENNReal.ofReal (S.lowerConstant * r ^ S.volumeExponent) ≤ volume (S.select I) := by
  have hIpos := (ENNReal.ofReal_pos.mpr hr).trans_le hmeasure
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hrI := (ENNReal.ofReal_le_iff_le_toReal hIfin).mp hmeasure
  apply le_trans _ (S.volume_lower I hI hIunit hIpos)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hr.le hrI _) S.lowerConstant_pos.le)

theorem coordinates_bound_of_measure_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) {r : ℝ} (hr : 0 < r) (hmeasure : ENNReal.ofReal r ≤ volume I)
    {σ : Fin D → ℝ} (hσ : σ ∈ S.select I) (j : Fin D) :
    |σ j| ≤ S.upperConstant * (r⁻¹) ^ S.boundExponent := by
  have hIpos := (ENNReal.ofReal_pos.mpr hr).trans_le hmeasure
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hrI := (ENNReal.ofReal_le_iff_le_toReal hIfin).mp hmeasure
  exact (S.coordinates_bound I hI hIunit hIpos σ hσ j).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (inv_anti₀ hr hrI) _)
      (zero_le_one.trans S.one_le_upperConstant))

theorem estimate_of_measure_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) {r : ℝ} (hr : 0 < r) (hmeasure : ENNReal.ofReal r ≤ volume I)
    {σ : Fin D → ℝ} (hσ : σ ∈ S.select I) {G : Set (Line m)} (hG : MeasurableSet G)
    (hGb : IsBounded G) :
    (volume G).toReal ≤ (S.upperConstant * (r⁻¹) ^ S.boundExponent) *
      (parallelMultiplicity G).toReal ^ (2 - β) *
      (sliceSize (Finset.univ.image (S.time σ)) G).toReal ^ β := by
  have hIpos := (ENNReal.ofReal_pos.mpr hr).trans_le hmeasure
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hrI := (ENNReal.ofReal_le_iff_le_toReal hIfin).mp hmeasure
  apply (S.estimate I hI hIunit hIpos σ hσ G hG hGb).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (inv_anti₀ hr hrI) _)
      (zero_le_one.trans S.one_le_upperConstant)) (Real.rpow_nonneg ENNReal.toReal_nonneg _))
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
