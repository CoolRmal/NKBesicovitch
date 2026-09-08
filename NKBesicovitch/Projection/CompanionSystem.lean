/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.BalancedStopping

/-!
# A common system of balanced companions

The finite-tree argument uses the same companion family whenever a height
occurs again. This record stores that simultaneous choice, its Borel and
containment properties, and the exact common slice mass.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- A half-mass center family and companions of equal slice mass at all selected heights. -/
structure CompanionSystem (G : Set (Line m)) (Γ : Finset ℝ) where
  centers : Set (Line m)
  companion : ℝ → Set (Line m)
  η : ℝ≥0∞
  centers_measurable : MeasurableSet centers
  centers_subset : centers ⊆ G
  centers_half : volume G / 2 ≤ volume centers
  η_pos : 0 < η
  η_ne_top : η ≠ ∞
  companion_measurable : ∀ t ∈ Γ, MeasurableSet (companion t)
  companion_subset : ∀ t ∈ Γ, companion t ⊆ G
  slice_eq : ∀ t ∈ Γ, ∀ g ∈ centers, sliceMultiplicity t (companion t) (atHeight t g) = η

theorem exists_companionSystem [Nonempty (Fin m)] (Γ : Finset ℝ) (hΓ : Γ.Nonempty)
    {G : Set (Line m)} (hG : MeasurableSet G) (hGb : IsBounded G) (hGpos : 0 < volume G)
    {N : ℝ} (hN : 0 < N) (hπ : ∀ t ∈ Γ, volume (atHeight t '' G) ≤ ENNReal.ofReal N) :
    ∃ S : CompanionSystem G Γ,
      S.η.toReal = (volume G).toReal / (2 * Γ.card * N) ∧
      (1 / (4 * Γ.card)) * (volume G).toReal ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤
        (volume S.centers * S.η).toReal ∧
      (volume S.centers * S.η).toReal ≤
        (1 / (2 * Γ.card)) * (volume G).toReal ^ (2 : ℝ) * N ^ (-1 : ℝ) := by
  classical
  obtain ⟨η, hη, hηfin, hηreal, G₀, hG₀, hG₀G, hhalf, hlower, hupper, hcomp⟩ :=
    exists_balanced_stopping_data Γ hΓ hG hGb hGpos hN hπ
  let C (t : ℝ) := if h : t ∈ Γ then (hcomp t h).choose else ∅
  have hC (t : ℝ) (ht : t ∈ Γ) : MeasurableSet (C t) ∧ C t ⊆ G ∧
      (∀ g ∈ G₀, sliceMultiplicity t (C t) (atHeight t g) = η) := by
    simpa only [C, dite_eq_left ht] using
      ⟨(hcomp t ht).choose_spec.1, (hcomp t ht).choose_spec.2.1,
        (hcomp t ht).choose_spec.2.2.1⟩
  exact ⟨⟨G₀, C, η, hG₀, hG₀G, hhalf, hη, hηfin,
    fun t ht ↦ (hC t ht).1, fun t ht ↦ (hC t ht).2.1, fun t ht ↦ (hC t ht).2.2⟩,
    hηreal, hlower, hupper⟩

end NKBesicovitch.Projection
