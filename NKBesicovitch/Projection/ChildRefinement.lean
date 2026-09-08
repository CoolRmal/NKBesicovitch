/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.ProjectionImage
public import NKBesicovitch.Projection.SimultaneousCodePruning

/-!
# The common child family and its two refinements

Intersect the concentrated subsets for every child projection, impose all
double-projection density lower bounds, then retain comparable density for
each selected code. The total loss is explicit at each stage.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι κ : Type*}

theorem exists_common_concentrated_pairs (a : ℝ) (s t : ι → ℝ) (I : Finset ι)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) (δ P : ℝ≥0∞)
    (hchild : ∀ i ∈ I, ∃ E : Set (PairCoordinates m), MeasurableSet E ∧ E ⊆ W ∧
      volume (W \ E) ≤ δ ∧ volume (pairProjections a (s i) (t i) '' E) ≤ P) :
    ∃ E : Set (PairCoordinates m), MeasurableSet E ∧ E ⊆ W ∧
      volume (W \ E) ≤ I.card * δ ∧
      ∀ i ∈ I, volume (pairProjections a (s i) (t i) '' E) ≤ P := by
  classical
  let E (i : ι) := if hi : i ∈ I then Classical.choose (hchild i hi) else W
  have hE (i : ι) (hi : i ∈ I) : MeasurableSet (E i) ∧ E i ⊆ W ∧
      volume (W \ E i) ≤ δ ∧ volume (pairProjections a (s i) (t i) '' E i) ≤ P := by
    simpa only [E, dite_eq_left hi] using Classical.choose_spec (hchild i hi)
  let E₁ := W ∩ ⋂ i ∈ I, E i
  have hsub (i : ι) (hi : i ∈ I) : E₁ ⊆ E i := fun _ hp ↦
    mem_iInter.mp (mem_iInter.mp hp.2 i) hi
  refine ⟨E₁, hW.inter (I.measurableSet_biInter fun i hi ↦ (hE i hi).1),
    inter_subset_left, ?_, fun i hi ↦ (measure_mono (image_mono (hsub i hi))).trans (hE i hi).2.2.2⟩
  have hcover : W \ E₁ ⊆ ⋃ i ∈ I, W \ E i := by
    intro p hp
    by_contra h
    apply hp.2
    refine ⟨hp.1, mem_iInter.mpr fun i ↦ mem_iInter.mpr fun hi ↦ ?_⟩
    by_contra hn
    exact h (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hp.1, hn⟩⟩)
  calc
    _ ≤ volume (⋃ i ∈ I, W \ E i) := measure_mono hcover
    _ ≤ ∑ i ∈ I, volume (W \ E i) := measure_biUnion_finset_le I _
    _ ≤ ∑ _i ∈ I, δ := Finset.sum_le_sum fun i hi ↦ (hE i hi).2.2.1
    _ = _ := by simp [nsmul_eq_mul]

theorem volume_sdiff_le_add_sdiff (W E F : Set (PairCoordinates m)) :
    volume (W \ F) ≤ volume (W \ E) + volume (E \ F) := by
  have hsub : W \ F ⊆ (W \ E) ∪ (E \ F) := by
    intro p hp
    by_cases hE : p ∈ E
    · exact Or.inr ⟨hE, hp.2⟩
    · exact Or.inl ⟨hp.1, hE⟩
  exact (measure_mono hsub).trans (measure_union_le _ _)

/-- The three child families, with one total deletion budget and all density bounds. -/
theorem exists_refined_child_pairs {a b : ℝ} (hab : a ≠ b)
    (s t : ι → ℝ) (I : Finset ι) (c : κ → ℝ) (K : Finset κ)
    (hs : ∀ i ∈ I, s i ≠ a) (ht : ∀ i ∈ I, t i ≠ a)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) (δ P ℓ : ℝ≥0∞)
    (hchild : ∀ i ∈ I, ∃ E : Set (PairCoordinates m), MeasurableSet E ∧ E ⊆ W ∧
      volume (W \ E) ≤ δ ∧ volume (pairProjections a (s i) (t i) '' E) ≤ P) :
    ∃ E₁ E₂ E₃ : Set (PairCoordinates m),
      MeasurableSet E₁ ∧ MeasurableSet E₂ ∧ MeasurableSet E₃ ∧
      E₁ ⊆ W ∧ E₂ ⊆ E₁ ∧ E₃ ⊆ E₂ ∧
      volume (W \ E₃) ≤ (1 + 2 * K.card) * (I.card * δ + I.card * ℓ * P) ∧
      (∀ i ∈ I, ∀ p ∈ E₂, ℓ ≤ pairDensity a (s i) (t i) E₁
        (pairProjections a (s i) (t i) p)) ∧
      ∀ k ∈ K, ∀ p ∈ E₃, 0 < codeDensity a b (c k) W (pairCode a b (c k) p) ∧
        codeDensity a b (c k) W (pairCode a b (c k) p) ≤
          2 * codeDensity a b (c k) E₂ (pairCode a b (c k) p) := by
  obtain ⟨E₁, hE₁, hE₁W, hloss₁, hP⟩ :=
    exists_common_concentrated_pairs a s t I hW δ P hchild
  let E₂ := densePairs a s t I E₁ ℓ
  let E₃ := retainedCodePairs a b c K W E₂
  have hE₂ : MeasurableSet E₂ := measurableSet_densePairs a s t I hE₁ ℓ
  have hE₂E₁ : E₂ ⊆ E₁ := densePairs_subset a s t I E₁ ℓ
  have hE₃ : MeasurableSet E₃ := measurableSet_retainedCodePairs a b c K hW hE₂
  have hE₃E₂ : E₃ ⊆ E₂ := retainedCodePairs_subset a b c K W E₂
  have hloss₂ : volume (W \ E₂) ≤ I.card * δ + I.card * ℓ * P :=
    (volume_sdiff_le_add_sdiff W E₁ E₂).trans (add_le_add hloss₁
      (volume_sdiff_densePairs_le_of_image_bound a s t I hs ht hE₁ ℓ P hP))
  refine ⟨E₁, E₂, E₃, hE₁, hE₂, hE₃, hE₁W, hE₂E₁, hE₃E₂, ?_,
    fun _ hi _ hp ↦ le_pairDensity_of_mem_densePairs hp hi,
    fun _ hk _ hp ↦ codeDensity_bounds_of_mem_retainedCodePairs hp hk⟩
  exact (volume_sdiff_retainedCodePairs_le hab c K hW hE₂ (hE₂E₁.trans hE₁W)).trans
    (mul_le_mul le_rfl hloss₂ bot_le bot_le)

end NKBesicovitch.Projection
