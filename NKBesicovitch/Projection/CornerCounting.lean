/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.InnerCorners

/-!
# Retaining corners through parent and inner pair restrictions

The retained parent mass is multiplied by the last-companion mass. Removing
bad inner pairs costs at most their pair mass times the first-companion mass.
These exact counts give the half-mass budget in the corner pruning step.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem parentCorners_sdiff_inner_preimage_subset {a b : ℝ}
    {G₀ A B : Set (Line m)} {U W : Set (PairCoordinates m)}
    (hU : U ⊆ companionPairs a G₀ A) :
    parentCorners a b U B \ cornerInner b ⁻¹' W ⊆
      innerCorners a b A (companionPairs b G₀ B \ W) := by
  intro p hp
  have h := hU hp.1.1
  refine ⟨h.2, ⟨⟨?_, hp.1.2⟩, hp.2⟩⟩
  simpa only [first_cornerInner, first_cornerParent] using h.1

theorem volume_parentCorners_sdiff_inner_preimage_le (a b : ℝ)
    {G₀ A B : Set (Line m)} (hG₀ : MeasurableSet G₀) (hA : MeasurableSet A)
    (hB : MeasurableSet B) {U W : Set (PairCoordinates m)}
    (hU : U ⊆ companionPairs a G₀ A) (hW : MeasurableSet W) (ηₐ : ℝ≥0∞)
    (hηₐ : ∀ g ∈ G₀, sliceMultiplicity a A (atHeight a g) = ηₐ) :
    volume (parentCorners a b U B \ cornerInner b ⁻¹' W) ≤
      volume (companionPairs b G₀ B \ W) * ηₐ := by
  calc
    _ ≤ volume (innerCorners a b A (companionPairs b G₀ B \ W)) :=
      measure_mono (parentCorners_sdiff_inner_preimage_subset hU)
    _ = _ := volume_innerCorners_of_constant_mass a b hA
      ((measurableSet_companionPairs b hG₀ hB).diff hW) ηₐ
        (fun p hp ↦ hηₐ _ hp.1.1)

/-- The retained corner mass plus the cost of bad inner pairs covers the parent lift. -/
theorem parent_mass_le_retained_corner_mass_add (a b : ℝ)
    {G₀ A B : Set (Line m)} (hG₀ : MeasurableSet G₀) (hA : MeasurableSet A)
    (hB : MeasurableSet B) {U W : Set (PairCoordinates m)} (hU : MeasurableSet U)
    (hUP : U ⊆ companionPairs a G₀ A) (hW : MeasurableSet W) (ηₐ ηᵦ : ℝ≥0∞)
    (hηₐ : ∀ g ∈ G₀, sliceMultiplicity a A (atHeight a g) = ηₐ)
    (hηᵦ : ∀ g ∈ G₀, sliceMultiplicity b B (atHeight b g) = ηᵦ) :
    volume U * ηᵦ ≤ volume (parentCorners a b U B ∩ cornerInner b ⁻¹' W) +
      volume (companionPairs b G₀ B \ W) * ηₐ := by
  rw [← volume_parentCorners_of_constant_mass a b hU hB ηᵦ
    (fun p hp ↦ hηᵦ _ (hUP hp).1)]
  exact (measure_le_inter_add_sdiff volume (parentCorners a b U B) (cornerInner b ⁻¹' W)).trans
    (add_le_add le_rfl
      (volume_parentCorners_sdiff_inner_preimage_le a b hG₀ hA hB hUP hW ηₐ hηₐ))

/-- A small enough inner-pair deletion preserves half the initial lifted parent mass. -/
theorem half_parent_mass_le_retained_corner_mass (a b : ℝ)
    {G₀ A B : Set (Line m)} (hG₀ : MeasurableSet G₀) (hA : MeasurableSet A)
    (hB : MeasurableSet B) {U W : Set (PairCoordinates m)} (hU : MeasurableSet U)
    (hUP : U ⊆ companionPairs a G₀ A) (hW : MeasurableSet W) (ηₐ ηᵦ : ℝ≥0∞)
    (hηₐ : ∀ g ∈ G₀, sliceMultiplicity a A (atHeight a g) = ηₐ)
    (hηᵦ : ∀ g ∈ G₀, sliceMultiplicity b B (atHeight b g) = ηᵦ)
    (hfin : volume U * ηᵦ ≠ ∞)
    (hbudget : volume (companionPairs b G₀ B \ W) * ηₐ ≤ (volume U * ηᵦ) / 2) :
    (volume U * ηᵦ) / 2 ≤ volume (parentCorners a b U B ∩ cornerInner b ⁻¹' W) := by
  apply ENNReal.le_of_add_le_add_right (ne_top_of_le_ne_top hfin ENNReal.half_le_self)
  rw [ENNReal.add_halves]
  exact (parent_mass_le_retained_corner_mass_add a b hG₀ hA hB hU hUP hW ηₐ ηᵦ hηₐ hηᵦ).trans
    (add_le_add le_rfl hbudget)

end NKBesicovitch.Projection
