/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Companions
public import NKBesicovitch.Projection.SliceRefinement

/-!
# Balanced pairs of center lines and companions

Pairs use a center line from the refined family and a companion from the
original fiber. Prescribing the companion mass makes the pair mass exactly
the center-family volume times that prescribed mass.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Incident pairs with a center in `G₀` and a companion in `C`. -/
def companionPairs (a : ℝ) (G₀ C : Set (Line m)) : Set (PairCoordinates m) :=
  {p | lineAt a p.1 p.2.1 ∈ G₀ ∧ lineAt a p.1 p.2.2 ∈ C}

theorem measurableSet_companionPairs (a : ℝ) {G₀ C : Set (Line m)}
    (hG₀ : MeasurableSet G₀) (hC : MeasurableSet C) :
    MeasurableSet (companionPairs a G₀ C) :=
  (hG₀.preimage (by unfold lineAt; fun_prop)).inter
    (hC.preimage (by unfold lineAt; fun_prop))

theorem companionPairs_subset_pairFamily (a : ℝ) {G₀ C G : Set (Line m)}
    (hG₀ : G₀ ⊆ G) (hC : C ⊆ G) : companionPairs a G₀ C ⊆ pairFamily a G :=
  fun _ hp ↦ ⟨hG₀ hp.1, hC hp.2⟩

theorem volume_companionPairs (a : ℝ) {G₀ C : Set (Line m)}
    (hG₀ : MeasurableSet G₀) (hC : MeasurableSet C) :
    volume (companionPairs a G₀ C) =
      ∫⁻ y, sliceMultiplicity a G₀ y * sliceMultiplicity a C y := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_companionPairs a hG₀ hC)]
  apply lintegral_congr
  intro y
  change volume ((lineAt a y ⁻¹' G₀) ×ˢ (lineAt a y ⁻¹' C)) = _
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  rfl

/-- Balanced companion pairs have an exact intrinsic mass. -/
theorem volume_companionPairs_of_constant_mass (a : ℝ) {G₀ C : Set (Line m)}
    (hG₀ : MeasurableSet G₀) (hC : MeasurableSet C) (η : ℝ≥0∞)
    (hη : ∀ y ∈ atHeight a '' G₀, sliceMultiplicity a C y = η) :
    volume (companionPairs a G₀ C) = volume G₀ * η := by
  rw [volume_companionPairs a hG₀ hC]
  calc
    _ = ∫⁻ y, sliceMultiplicity a G₀ y * η := by
      apply lintegral_congr
      intro y
      by_cases hy : sliceMultiplicity a G₀ y = 0
      · simp [hy]
      · rw [hη y (support_sliceMultiplicity_subset a G₀ hy)]
    _ = (∫⁻ y, sliceMultiplicity a G₀ y) * η :=
      lintegral_mul_const η (measurable_sliceMultiplicity a hG₀)
    _ = _ := by rw [lintegral_sliceMultiplicity a hG₀]

/-- All the selected heights admit companions with the same exact pair mass. -/
theorem exists_balanced_pairs [Nonempty (Fin m)] (Γ : Finset ℝ) {G : Set (Line m)}
    (hG : MeasurableSet G) (hGb : IsBounded G) (η N : ℝ≥0∞)
    (hN : ∀ a ∈ Γ, volume (atHeight a '' G) ≤ N)
    (hbudget : Γ.card * η * N ≤ volume G / 2) :
    ∃ G₀ : Set (Line m), MeasurableSet G₀ ∧ G₀ ⊆ G ∧ volume G / 2 ≤ volume G₀ ∧
      ∀ a ∈ Γ, ∃ C : Set (Line m), MeasurableSet C ∧ C ⊆ G ∧
        (∀ g ∈ G₀, sliceMultiplicity a C (atHeight a g) = η) ∧
        volume (companionPairs a G₀ C) = volume G₀ * η := by
  let G₀ := denseLines id Γ G η
  have hG₀ : MeasurableSet G₀ := measurableSet_denseLines id Γ hG η
  refine ⟨G₀, hG₀, denseLines_subset id Γ G η,
    half_volume_le_volume_denseLines id Γ hG hGb.measure_lt_top.ne η N hN hbudget,
    fun a ha ↦ ?_⟩
  obtain ⟨C, hC, hCG, hCη⟩ := exists_companions a hG hGb η
  have he : ∀ y ∈ atHeight a '' G₀, sliceMultiplicity a C y = η := by
    rintro y ⟨g, hg, rfl⟩
    exact hCη _ (le_sliceMultiplicity_of_mem_denseLines hg ha)
  exact ⟨C, hC, hCG, fun g hg ↦ he _ ⟨g, hg, rfl⟩,
    volume_companionPairs_of_constant_mass a hG₀ hC η he⟩

end NKBesicovitch.Projection
