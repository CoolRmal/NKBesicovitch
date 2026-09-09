/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.PositiveMeasure.SmoothApproximation
public import NKBesicovitch.PositiveMeasure.FromMaximal
public import NKBesicovitch.Operators.DiskConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Positive measure from a Schwartz disk estimate

Smooth approximation from inside each open set and bounded convergence on
every disk give the required open-indicator estimate. Outer regularity then
gives a positive lower volume bound for every Besicovitch set.
-/

public section

open MeasureTheory Set Filter
open scoped SchwartzMap ENNReal NNReal Topology

namespace NKBesicovitch

private lemma eLpNorm_rpow_le_measure_aux {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {U : Set X} (hU : MeasurableSet U) {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ U.indicator (fun _ ↦ (1 : ℝ)) x)
    {p : ℝ≥0} (hp : 0 < p) : eLpNorm f p μ ^ (p : ℝ) ≤ μ U := by
  have hn : eLpNorm f p μ ≤ eLpNorm (U.indicator (fun _ ↦ (1 : ℝ))) p μ := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_of_nonneg (hf x).1,
      Real.norm_of_nonneg (indicator_nonneg (fun _ _ ↦ zero_le_one) x)]
    exact (hf x).2
  have h := ENNReal.rpow_le_rpow hn (show 0 ≤ (p : ℝ) from hp.le)
  simpa only [eLpNorm_indicator_const hU (ENNReal.coe_ne_zero.mpr hp.ne') ENNReal.coe_ne_top,
    enorm_one, one_mul, ENNReal.coe_toReal, one_div,
    ENNReal.rpow_inv_rpow (show (p : ℝ) ≠ 0 from (show 0 < (p : ℝ) from hp).ne')] using h

/-- A positive Schwartz disk bound implies the same powered bound for open indicators. -/
theorem lintegral_diskMaximal_indicator_rpow_le_of_schwartz_bound {n k : ℕ}
    (μ : Measure (Grassmannian n k)) {p : ℝ≥0} (hp : 0 < p) (C : ℝ≥0)
    (hbound : ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ), (∀ x, 0 ≤ f x) →
      eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (f x))) p μ ≤ C * eLpNorm f p volume)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) :
    (∫⁻ V, diskMaximal (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) V ^ (p : ℝ) ∂μ) ≤
      (C : ℝ≥0∞) ^ (p : ℝ) * volume U := by
  obtain ⟨f, hf, ht⟩ := exists_schwartz_tendsto_indicator hU
  apply lintegral_diskMaximal_rpow_le_of_tendsto μ
    (fun j ↦ ENNReal.continuous_ofReal.comp (f j).continuous)
    (fun j x ↦ (ENNReal.ofReal_le_ofReal ((hf j x).2.trans
      (indicator_le_self' (fun _ _ ↦ zero_le_one) x))).trans_eq ENNReal.ofReal_one)
    (fun x ↦ ?_) (show 0 < (p : ℝ) from hp) (fun j ↦ ?_)
  · have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (ht x)
    by_cases hx : x ∈ U
    · simpa only [Function.comp_def, indicator_of_mem hx, ENNReal.ofReal_one] using h
    · simpa only [Function.comp_def, indicator_of_notMem hx, ENNReal.ofReal_zero] using h
  · have h := ENNReal.rpow_le_rpow (hbound (f j) (fun x ↦ (hf j x).1))
      (show 0 ≤ (p : ℝ) from hp.le)
    rw [eLpNorm_nnreal_pow_eq_lintegral hp.ne',
      ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ (p : ℝ) from hp.le)] at h
    simp only [enorm_eq_self] at h
    exact h.trans (mul_le_mul_right (eLpNorm_rpow_le_measure_aux hU.measurableSet (hf j) hp) _)

/-- Any global positive Schwartz disk estimate forces positive measure for Besicovitch sets. -/
theorem volume_pos_of_schwartz_diskMaximal_bound {n k : ℕ}
    (μ : Measure (Grassmannian n k)) [IsProbabilityMeasure μ] {p : ℝ≥0} (hp : 0 < p) (C : ℝ≥0)
    (hbound : ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ), (∀ x, 0 ≤ f x) →
      eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (f x))) p μ ≤ C * eLpNorm f p volume)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : IsBesicovitch k E) : 0 < volume E := by
  have hC : 0 < (C + 1) ^ (p : ℝ) := NNReal.rpow_pos (by positivity)
  have h := le_volume_of_diskMaximal_bound μ (show 0 ≤ (p : ℝ) from hp.le) hC
    (fun U hU ↦ ?_) hE
  · exact (ENNReal.div_pos one_ne_zero ENNReal.coe_ne_top).trans_le h
  · have hb := lintegral_diskMaximal_indicator_rpow_le_of_schwartz_bound μ hp C hbound hU
    apply hb.trans
    rw [ENNReal.coe_rpow_of_nonneg _ (show 0 ≤ (p : ℝ) from hp.le)]
    have hc : (C : ℝ≥0∞) ≤ ((C + 1 : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.coe_le_coe.mpr (le_add_of_nonneg_right zero_le_one)
    exact mul_le_mul_left (ENNReal.rpow_le_rpow hc (show 0 ≤ (p : ℝ) from hp.le)) _

end NKBesicovitch
