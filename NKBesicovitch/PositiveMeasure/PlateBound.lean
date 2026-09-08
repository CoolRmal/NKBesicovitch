/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.PositiveMeasure.Delta
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.Positivity

/-!
# Positive measure from uniform delta maximal estimates

Fatou's lemma permits a different small-scale threshold for every direction.
The scale loss in the assumed bound is zero. A positive power loss in delta
would not give the asserted positive-volume conclusion by this argument.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace NKBesicovitch

/-- Uniform plate maximal estimates on open indicators imply a quantitative volume lower bound. -/
theorem le_volume_of_plateMaximal_bound {n k : ℕ} (μ : Measure (Grassmannian n k))
    [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 ≤ p) {C : ℝ≥0} (hC : 0 < C)
    (hmeas : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ U : Set (Space n), IsOpen U →
      AEMeasurable (plateMaximal δ (U.indicator (fun _ ↦ (1 : ℝ≥0∞)))) μ)
    (hmax : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ U : Set (Space n), IsOpen U →
      (∫⁻ V, plateMaximal δ (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) V ^ p ∂μ) ≤ C * volume U)
    {E : Set (Space n)} (hE : IsBesicovitch k E) : (1 : ℝ≥0∞) / C ≤ volume E := by
  rw [E.measure_eq_iInf_isOpen volume]
  refine le_iInf fun U ↦ le_iInf fun hEU ↦ le_iInf fun hU ↦ ?_
  have hB : IsBesicovitch k U := by
    intro V hV
    obtain ⟨a, ha⟩ := hE V hV
    exact ⟨a, fun v hv hn ↦ hEU (ha v hv hn)⟩
  let δ (j : ℕ) : ℝ := 1 / (j + 1)
  have hδ (j : ℕ) : δ j ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · dsimp [δ]
      positivity
    · exact (div_le_iff₀ (by positivity : (0 : ℝ) < j + 1)).2 (by simp)
  let F (j : ℕ) (V : Grassmannian n k) :=
    plateMaximal (δ j) (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) V ^ p
  have hF (j : ℕ) : AEMeasurable (F j) μ :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hmeas _ (hδ j) U hU)
  have hlim (V : Grassmannian n k) : 1 ≤ liminf (fun j ↦ F j V) atTop := by
    obtain ⟨δ₀, hδ₀, hs⟩ := exists_scale_one_le_plateMaximal hU hB V
    have hsmall : ∀ᶠ j in atTop, δ j < δ₀ :=
      tendsto_one_div_add_atTop_nhds_zero_nat (Iio_mem_nhds hδ₀)
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hsmall] with j hj
    simpa [F] using ENNReal.rpow_le_rpow (hs _ ⟨(hδ j).1, hj.le⟩) hp
  have hlow : (1 : ℝ≥0∞) ≤ C * volume U := calc
    (1 : ℝ≥0∞) = ∫⁻ _ : Grassmannian n k, (1 : ℝ≥0∞) ∂μ := by simp
    _ ≤ ∫⁻ V, liminf (fun j ↦ F j V) atTop ∂μ := lintegral_mono hlim
    _ ≤ liminf (fun j ↦ ∫⁻ V, F j V ∂μ) atTop := lintegral_liminf_le' hF
    _ ≤ C * volume U := by
      simpa [F] using liminf_le_liminf (f := atTop)
        (Eventually.of_forall (fun j ↦ hmax _ (hδ j) U hU))
  exact (ENNReal.div_le_iff' (by exact_mod_cast hC.ne') ENNReal.coe_ne_top).2 hlow

end NKBesicovitch
