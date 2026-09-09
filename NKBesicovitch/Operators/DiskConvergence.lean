/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.DiskMeasurability
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Passing disk estimates to bounded pointwise limits

Dominated convergence applies on each individual disk. Taking the supremum
over centers gives a lower bound by the liminf of the maxima; Fatou's lemma
then passes a uniform integral estimate to the limiting function.
-/

public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NKBesicovitch

variable {n k : ℕ} {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
  {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

/-- Uniformly bounded pointwise convergence implies convergence of each disk average. -/
theorem tendsto_diskAverage_of_bounded (hf : ∀ j, Measurable (f j))
    (hb : ∀ j x, f j x ≤ 1) (hg : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 (g x)))
    (V : Grassmannian n k) (a : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun j ↦ diskAverage (f j) V a) atTop (𝓝 (diskAverage g V a)) := by
  have h := tendsto_lintegral_of_dominated_convergence
    (μ := volume.restrict (closedBall (0 : V.val) 1)) (fun _ ↦ (1 : ℝ≥0∞))
    (fun j ↦ (hf j).comp (continuous_const.add continuous_subtype_val).measurable)
    (fun j ↦ ae_of_all _ fun w ↦ hb j (a + w))
    (by simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ]
      using (measure_closedBall_lt_top (x := (0 : V.val)) (r := 1)).ne)
    (ae_of_all _ fun w ↦ hg (a + w))
  exact (ENNReal.continuous_div_const _
    (measure_closedBall_pos volume _ zero_lt_one).ne').continuousAt.tendsto.comp h

theorem diskMaximal_rpow_le_liminf_of_tendsto (hf : ∀ j, Measurable (f j))
    (hb : ∀ j x, f j x ≤ 1) (hg : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 (g x)))
    {p : ℝ} (hp : 0 < p) (V : Grassmannian n k) :
    diskMaximal g V ^ p ≤ liminf (fun j ↦ diskMaximal (f j) V ^ p) atTop := by
  rw [← ENNReal.le_rpow_inv_iff hp]
  apply iSup_le
  intro a
  rw [ENNReal.le_rpow_inv_iff hp]
  have ht := (ENNReal.continuous_rpow_const (y := p)).continuousAt.tendsto.comp
    (tendsto_diskAverage_of_bounded hf hb hg V a)
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun j ↦
    ENNReal.rpow_le_rpow (le_iSup (fun a ↦ diskAverage (f j) V a) a) hp.le)

/-- A uniform integral bound for continuous inputs passes to their bounded pointwise limit. -/
theorem lintegral_diskMaximal_rpow_le_of_tendsto (μ : Measure (Grassmannian n k))
    (hf : ∀ j, Continuous (f j)) (hb : ∀ j x, f j x ≤ 1)
    (hg : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 (g x)))
    {p : ℝ} (hp : 0 < p) {B : ℝ≥0∞}
    (hbound : ∀ j, (∫⁻ V, diskMaximal (f j) V ^ p ∂μ) ≤ B) :
    (∫⁻ V, diskMaximal g V ^ p ∂μ) ≤ B := by
  apply (lintegral_mono fun V ↦ diskMaximal_rpow_le_liminf_of_tendsto
    (fun j ↦ (hf j).measurable) hb hg hp V).trans
  apply (lintegral_liminf_le fun j ↦ ENNReal.continuous_rpow_const.measurable.comp
    (lowerSemicontinuous_diskMaximal (hf j).lowerSemicontinuous).measurable).trans
  simpa only [Function.comp_def, liminf_const] using
    liminf_le_liminf (f := atTop) (Eventually.of_forall hbound)

end NKBesicovitch
