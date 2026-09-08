/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.SimultaneousRefinement
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Concentrated pair images and their refinement cost

A lower density bound on a pair family controls the outer measure of its
double-projection image. Subsequent low-density deletion can use this smaller
image in place of the product of the original line projections.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι : Type*}

theorem support_pairDensity_subset_image {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    (W : Set (PairCoordinates m)) :
    Function.support (pairDensity a s t W) ⊆ pairProjections a s t '' W := by
  intro yz hyz
  by_contra h
  have hz (w : EuclideanSpace ℝ (Fin m)) : pairFromData a s t (w, yz) ∉ W := by
    intro hw
    exact h ⟨_, hw, pairProjections_pairFromData hs ht (w, yz)⟩
  exact hyz (by simp [pairDensity, Set.indicator_of_notMem, hz])

theorem mul_volume_pairProjections_image_le {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    {W E : Set (PairCoordinates m)} (hW : MeasurableSet W) (ℓ : ℝ≥0∞)
    (hℓ : ∀ p ∈ E, ℓ ≤ pairDensity a s t W (pairProjections a s t p)) :
    ℓ * volume (pairProjections a s t '' E) ≤ volume W := by
  have hsub : pairProjections a s t '' E ⊆ {yz | ℓ ≤ pairDensity a s t W yz} := by
    rintro yz ⟨p, hp, rfl⟩
    exact hℓ p hp
  calc
    _ ≤ ℓ * volume {yz | ℓ ≤ pairDensity a s t W yz} :=
      mul_le_mul le_rfl (measure_mono hsub) bot_le bot_le
    _ ≤ ∫⁻ yz, pairDensity a s t W yz :=
      mul_meas_ge_le_lintegral (measurable_pairDensity a s t hW) ℓ
    _ = _ := lintegral_pairDensity hs ht hW

theorem volume_low_pairDensity_le_of_image_subset {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) {S : Set (Line m)}
    (hS : pairProjections a s t '' W ⊆ S) (ℓ : ℝ≥0∞) :
    volume (W ∩ {p | pairDensity a s t W (pairProjections a s t p) < ℓ}) ≤ ℓ * volume S := by
  change volume (W ∩ pairProjections a s t ⁻¹' {yz | pairDensity a s t W yz < ℓ}) ≤ _
  rw [← setLIntegral_pairDensity hs ht hW
    (measurableSet_lt (measurable_pairDensity a s t hW) measurable_const)]
  exact setLIntegral_lt_le_mul_measure (measurable_pairDensity a s t hW)
    ((support_pairDensity_subset_image hs ht W).trans hS) ℓ

theorem volume_sdiff_densePairs_le_of_image_subset (a : ℝ) (s t : ι → ℝ) (I : Finset ι)
    (hs : ∀ i ∈ I, s i ≠ a) (ht : ∀ i ∈ I, t i ≠ a)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (S : ι → Set (Line m)) (hS : ∀ i ∈ I, pairProjections a (s i) (t i) '' W ⊆ S i)
    (ℓ : ℝ≥0∞) :
    volume (W \ densePairs a s t I W ℓ) ≤ ∑ i ∈ I, ℓ * volume (S i) := by
  calc
    _ ≤ volume (⋃ i ∈ I, W ∩
        {p | pairDensity a (s i) (t i) W (pairProjections a (s i) (t i) p) < ℓ}) :=
      measure_mono (sdiff_densePairs_subset a s t I W ℓ)
    _ ≤ ∑ i ∈ I, volume (W ∩
        {p | pairDensity a (s i) (t i) W (pairProjections a (s i) (t i) p) < ℓ}) :=
      measure_biUnion_finset_le I _
    _ ≤ _ := Finset.sum_le_sum fun i hi ↦
      volume_low_pairDensity_le_of_image_subset (hs i hi) (ht i hi) hW (hS i hi) ℓ

theorem volume_sdiff_densePairs_le_of_image_bound (a : ℝ) (s t : ι → ℝ) (I : Finset ι)
    (hs : ∀ i ∈ I, s i ≠ a) (ht : ∀ i ∈ I, t i ≠ a)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) (ℓ P : ℝ≥0∞)
    (hP : ∀ i ∈ I, volume (pairProjections a (s i) (t i) '' W) ≤ P) :
    volume (W \ densePairs a s t I W ℓ) ≤ I.card * ℓ * P := by
  refine (volume_sdiff_densePairs_le_of_image_subset a s t I hs ht hW
    (fun i ↦ pairProjections a (s i) (t i) '' W) (fun _ _ ↦ Subset.rfl) ℓ).trans ?_
  calc
    _ ≤ ∑ _i ∈ I, ℓ * P := Finset.sum_le_sum fun i hi ↦
      mul_le_mul le_rfl (hP i hi) bot_le bot_le
    _ = _ := by simp [nsmul_eq_mul, mul_assoc]

end NKBesicovitch.Projection
