/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lower semicontinuity under nonnegative integration

Fatou's lemma applies to the neighborhood filter in a first-countable space.
This will give measurability of maximal averages on open indicators.
-/

public section

open MeasureTheory
open scoped ENNReal Topology

namespace NKBesicovitch

theorem lowerSemicontinuous_lintegral {X Y : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [MeasurableSpace Y] {μ : Measure Y} {f : X → Y → ℝ≥0∞}
    (hm : ∀ x, AEMeasurable (f x) μ) (hl : ∀ y, LowerSemicontinuous (fun x ↦ f x y)) :
    LowerSemicontinuous (fun x ↦ ∫⁻ y, f x y ∂μ) := by
  refine lowerSemicontinuous_iff_le_liminf.mpr fun x ↦ ?_
  exact (lintegral_mono fun y ↦ (hl y).le_liminf x).trans (lintegral_liminf_le' hm)

end NKBesicovitch
