/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Disks
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Positive measure from an open-set maximal bound

Outer regularity makes the argument apply even to sets that are not measurable.
Only open indicators enter the assumed analytic estimate. The direction measure
is a probability measure; later constructions provide the invariant one.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NKBesicovitch

/-- A uniform disk maximal estimate for open indicators gives a quantitative volume lower bound. -/
theorem le_volume_of_diskMaximal_bound {n k : ℕ} (μ : Measure (Grassmannian n k))
    [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 ≤ p) {C : ℝ≥0} (hC : 0 < C)
    (hmax : ∀ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U →
      (∫⁻ V, diskMaximal (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) V ^ p ∂μ) ≤ C * volume U)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : IsBesicovitch k E) : (1 : ℝ≥0∞) / C ≤ volume E := by
  rw [E.measure_eq_iInf_isOpen volume]
  refine le_iInf fun U ↦ le_iInf fun hEU ↦ le_iInf fun hU ↦ ?_
  have hB : IsBesicovitch k U := by
    intro V hV
    obtain ⟨a, ha⟩ := hE V hV
    exact ⟨a, fun v hv hn ↦ hEU (ha v hv hn)⟩
  have hlow : (1 : ℝ≥0∞) ≤
      ∫⁻ V, diskMaximal (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) V ^ p ∂μ := by
    calc
      (1 : ℝ≥0∞) = ∫⁻ _ : Grassmannian n k, (1 : ℝ≥0∞) ∂μ := by simp
      _ ≤ _ := lintegral_mono fun V ↦ by
        simpa using ENNReal.rpow_le_rpow (one_le_diskMaximal_indicator hB V) hp
  exact (ENNReal.div_le_iff' (by exact_mod_cast hC.ne') ENNReal.coe_ne_top).2
    (hlow.trans (hmax U hU))

end NKBesicovitch
