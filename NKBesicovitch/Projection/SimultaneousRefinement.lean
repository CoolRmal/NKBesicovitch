/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PairRefinement

/-!
# Simultaneous pair-density refinement

Impose density lower bounds at finitely many pairs of heights. Subadditivity
controls the total discarded mass by the sum of the individual losses.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι : Type*}

/-- Pairs satisfying every selected density threshold, measured in the original family. -/
noncomputable def densePairs (a : ℝ) (s t : ι → ℝ) (I : Finset ι)
    (W : Set (PairCoordinates m)) (ℓ : ℝ≥0∞) : Set (PairCoordinates m) :=
  W ∩ ⋂ i ∈ I, {p | ℓ ≤ pairDensity a (s i) (t i) W (pairProjections a (s i) (t i) p)}

theorem densePairs_subset (a : ℝ) (s t : ι → ℝ) (I : Finset ι)
    (W : Set (PairCoordinates m)) (ℓ : ℝ≥0∞) : densePairs a s t I W ℓ ⊆ W :=
  inter_subset_left

theorem le_pairDensity_of_mem_densePairs {a : ℝ} {s t : ι → ℝ} {I : Finset ι}
    {W : Set (PairCoordinates m)} {ℓ : ℝ≥0∞} {p : PairCoordinates m}
    (hp : p ∈ densePairs a s t I W ℓ) {i : ι} (hi : i ∈ I) :
    ℓ ≤ pairDensity a (s i) (t i) W (pairProjections a (s i) (t i) p) :=
  mem_iInter.mp (mem_iInter.mp hp.2 i) hi

theorem measurableSet_densePairs (a : ℝ) (s t : ι → ℝ) (I : Finset ι)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) (ℓ : ℝ≥0∞) :
    MeasurableSet (densePairs a s t I W ℓ) := by
  exact hW.inter (I.measurableSet_biInter fun i _ ↦
    measurableSet_le measurable_const ((measurable_pairDensity a (s i) (t i) hW).comp
      (continuous_pairProjections a (s i) (t i)).measurable))

theorem sdiff_densePairs_subset (a : ℝ) (s t : ι → ℝ) (I : Finset ι)
    (W : Set (PairCoordinates m)) (ℓ : ℝ≥0∞) :
    W \ densePairs a s t I W ℓ ⊆
      ⋃ i ∈ I, W ∩ {p | pairDensity a (s i) (t i) W (pairProjections a (s i) (t i) p) < ℓ} := by
  intro p hp
  by_contra h
  apply hp.2
  refine ⟨hp.1, mem_iInter.mpr fun i ↦ mem_iInter.mpr fun hi ↦ ?_⟩
  change ℓ ≤ pairDensity a (s i) (t i) W (pairProjections a (s i) (t i) p)
  exact le_of_not_gt fun hlt ↦
    h (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hp.1, hlt⟩⟩)

theorem volume_sdiff_densePairs_le (a : ℝ) (s t : ι → ℝ) (I : Finset ι)
    (hs : ∀ i ∈ I, s i ≠ a) (ht : ∀ i ∈ I, t i ≠ a)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (hWG : W ⊆ pairFamily a G) (ℓ : ℝ≥0∞) :
    volume (W \ densePairs a s t I W ℓ) ≤
      ∑ i ∈ I, ℓ * (volume (atHeight (s i) '' G) * volume (atHeight (t i) '' G)) := by
  calc
    _ ≤ volume (⋃ i ∈ I, W ∩
        {p | pairDensity a (s i) (t i) W (pairProjections a (s i) (t i) p) < ℓ}) :=
      measure_mono (sdiff_densePairs_subset a s t I W ℓ)
    _ ≤ ∑ i ∈ I, volume (W ∩
        {p | pairDensity a (s i) (t i) W (pairProjections a (s i) (t i) p) < ℓ}) :=
      measure_biUnion_finset_le I _
    _ ≤ _ := Finset.sum_le_sum fun i hi ↦ volume_low_pairDensity_le (hs i hi) (ht i hi) hW hWG ℓ

theorem volume_sdiff_densePairs_le_card (a : ℝ) (s t : ι → ℝ) (I : Finset ι)
    (hs : ∀ i ∈ I, s i ≠ a) (ht : ∀ i ∈ I, t i ≠ a)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (hWG : W ⊆ pairFamily a G) (ℓ N : ℝ≥0∞)
    (hsN : ∀ i ∈ I, volume (atHeight (s i) '' G) ≤ N)
    (htN : ∀ i ∈ I, volume (atHeight (t i) '' G) ≤ N) :
    volume (W \ densePairs a s t I W ℓ) ≤ I.card * ℓ * N ^ 2 := by
  refine (volume_sdiff_densePairs_le a s t I hs ht hW hWG ℓ).trans ?_
  calc
    _ ≤ ∑ i ∈ I, ℓ * N ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [pow_two]
      exact mul_le_mul le_rfl (mul_le_mul (hsN i hi) (htN i hi) bot_le bot_le) bot_le bot_le
    _ = _ := by simp [nsmul_eq_mul, mul_assoc]

theorem volume_le_volume_densePairs_add (a : ℝ) (s t : ι → ℝ) (I : Finset ι)
    (hs : ∀ i ∈ I, s i ≠ a) (ht : ∀ i ∈ I, t i ≠ a)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (hWG : W ⊆ pairFamily a G) (ℓ N : ℝ≥0∞)
    (hsN : ∀ i ∈ I, volume (atHeight (s i) '' G) ≤ N)
    (htN : ∀ i ∈ I, volume (atHeight (t i) '' G) ≤ N) :
    volume W ≤ volume (densePairs a s t I W ℓ) + I.card * ℓ * N ^ 2 := by
  have h := measure_le_inter_add_sdiff volume W (densePairs a s t I W ℓ)
  rw [inter_eq_right.mpr (densePairs_subset a s t I W ℓ)] at h
  exact h.trans (add_le_add le_rfl
    (volume_sdiff_densePairs_le_card a s t I hs ht hW hWG ℓ N hsN htN))

theorem half_volume_le_volume_densePairs (a : ℝ) (s t : ι → ℝ) (I : Finset ι)
    (hs : ∀ i ∈ I, s i ≠ a) (ht : ∀ i ∈ I, t i ≠ a)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (hWG : W ⊆ pairFamily a G) (hfin : volume W ≠ ∞) (ℓ N : ℝ≥0∞)
    (hsN : ∀ i ∈ I, volume (atHeight (s i) '' G) ≤ N)
    (htN : ∀ i ∈ I, volume (atHeight (t i) '' G) ≤ N)
    (hbudget : I.card * ℓ * N ^ 2 ≤ volume W / 2) :
    volume W / 2 ≤ volume (densePairs a s t I W ℓ) := by
  have h := volume_le_volume_densePairs_add a s t I hs ht hW hWG ℓ N hsN htN
  apply ENNReal.le_of_add_le_add_right (ne_top_of_le_ne_top hfin ENNReal.half_le_self)
  rw [ENNReal.add_halves]
  exact h.trans (add_le_add le_rfl hbudget)

end NKBesicovitch.Projection
