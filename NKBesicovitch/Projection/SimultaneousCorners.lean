/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerRefinement

/-!
# Simultaneous outer-density refinement of corners

Impose the prescribed lower bound at every selected outer height. The total
lost mass is bounded by the sum of the individual outer-data bounds.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι : Type*}

/-- Corners satisfying all the outer-density thresholds in the original family. -/
noncomputable def denseCorners (a b c κ : ℝ) (u : ι → ℝ) (I : Finset ι)
    (D : Set (CornerCoordinates m)) (τ : ℝ≥0∞) : Set (CornerCoordinates m) :=
  D ∩ ⋂ i ∈ I, {p | τ ≤ cornerOuterDensity a b c κ (u i) D (cornerOuterData a b c κ (u i) p)}

theorem denseCorners_subset (a b c κ : ℝ) (u : ι → ℝ) (I : Finset ι)
    (D : Set (CornerCoordinates m)) (τ : ℝ≥0∞) : denseCorners a b c κ u I D τ ⊆ D :=
  inter_subset_left

theorem le_cornerOuterDensity_of_mem_denseCorners {a b c κ : ℝ} {u : ι → ℝ} {I : Finset ι}
    {D : Set (CornerCoordinates m)} {τ : ℝ≥0∞} {p : CornerCoordinates m}
    (hp : p ∈ denseCorners a b c κ u I D τ) {i : ι} (hi : i ∈ I) :
    τ ≤ cornerOuterDensity a b c κ (u i) D (cornerOuterData a b c κ (u i) p) :=
  mem_iInter.mp (mem_iInter.mp hp.2 i) hi

theorem measurableSet_denseCorners (a b c κ : ℝ) (u : ι → ℝ) (I : Finset ι)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D) (τ : ℝ≥0∞) :
    MeasurableSet (denseCorners a b c κ u I D τ) :=
  hD.inter (I.measurableSet_biInter fun i _ ↦ measurableSet_le measurable_const
    ((measurable_cornerOuterDensity a b c κ (u i) hD).comp
      (continuous_cornerOuterData a b c κ (u i)).measurable))

theorem sdiff_denseCorners_subset (a b c κ : ℝ) (u : ι → ℝ) (I : Finset ι)
    (D : Set (CornerCoordinates m)) (τ : ℝ≥0∞) :
    D \ denseCorners a b c κ u I D τ ⊆
      ⋃ i ∈ I, D ∩
        {p | cornerOuterDensity a b c κ (u i) D (cornerOuterData a b c κ (u i) p) < τ} := by
  intro p hp
  by_contra h
  apply hp.2
  refine ⟨hp.1, mem_iInter.mpr fun i ↦ mem_iInter.mpr fun hi ↦ ?_⟩
  change τ ≤ cornerOuterDensity a b c κ (u i) D (cornerOuterData a b c κ (u i) p)
  exact le_of_not_gt fun hlt ↦ h (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hp.1, hlt⟩⟩)

theorem volume_sdiff_denseCorners_le {a b c κ : ℝ} (hab : a ≠ b)
    (u : ι → ℝ) (I : Finset ι) (hua : ∀ i ∈ I, u i ≠ a)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D) (τ : ℝ≥0∞) (S : ι → Set (Line m))
    (hS : ∀ i ∈ I, cornerOuterData a b c κ (u i) '' D ⊆ S i) :
    volume (D \ denseCorners a b c κ u I D τ) ≤ ∑ i ∈ I, τ * volume (S i) := by
  calc
    _ ≤ volume (⋃ i ∈ I, D ∩
        {p | cornerOuterDensity a b c κ (u i) D (cornerOuterData a b c κ (u i) p) < τ}) :=
      measure_mono (sdiff_denseCorners_subset a b c κ u I D τ)
    _ ≤ ∑ i ∈ I, volume (D ∩
        {p | cornerOuterDensity a b c κ (u i) D (cornerOuterData a b c κ (u i) p) < τ}) :=
      measure_biUnion_finset_le I _
    _ ≤ _ := Finset.sum_le_sum fun i hi ↦
      volume_low_cornerOuterDensity_le hab (hua i hi) hD (hS i hi) τ

theorem half_volume_le_volume_denseCorners {a b c κ : ℝ} (hab : a ≠ b)
    (u : ι → ℝ) (I : Finset ι) (hua : ∀ i ∈ I, u i ≠ a)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    (τ : ℝ≥0∞) (S : ι → Set (Line m))
    (hS : ∀ i ∈ I, cornerOuterData a b c κ (u i) '' D ⊆ S i)
    (hbudget : ∑ i ∈ I, τ * volume (S i) ≤ volume D / 2) :
    volume D / 2 ≤ volume (denseCorners a b c κ u I D τ) := by
  have h := measure_le_inter_add_sdiff volume D (denseCorners a b c κ u I D τ)
  rw [inter_eq_right.mpr (denseCorners_subset a b c κ u I D τ)] at h
  have hloss := (volume_sdiff_denseCorners_le hab u I hua hD τ S hS).trans hbudget
  apply ENNReal.le_of_add_le_add_right (ne_top_of_le_ne_top hfin ENNReal.half_le_self)
  rw [ENNReal.add_halves]
  exact h.trans (add_le_add le_rfl hloss)

end NKBesicovitch.Projection
