/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.ProjectionImage

/-!
# The uniform and concentrated alternatives for incident pairs

Either a specified amount of pair mass has low double-projection density,
or deleting that sublevel set leaves a small double-projection image.
The root alternative follows when the threshold exceeds the uniform
pointwise density bound supplied by one original line projection.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Pairs on which their original double-projection density is below `Q`. -/
noncomputable def lowPairs (a s t : ℝ) (W : Set (PairCoordinates m))
    (Q : ℝ≥0∞) : Set (PairCoordinates m) :=
  W ∩ {p | pairDensity a s t W (pairProjections a s t p) < Q}

theorem lowPairs_subset (a s t : ℝ) (W : Set (PairCoordinates m)) (Q : ℝ≥0∞) :
    lowPairs a s t W Q ⊆ W := inter_subset_left

theorem measurableSet_lowPairs (a s t : ℝ) {W : Set (PairCoordinates m)}
    (hW : MeasurableSet W) (Q : ℝ≥0∞) : MeasurableSet (lowPairs a s t W Q) :=
  hW.inter (measurableSet_lt
    ((measurable_pairDensity a s t hW).comp (continuous_pairProjections a s t).measurable)
    measurable_const)

theorem sdiff_sdiff_lowPairs (a s t : ℝ) (W : Set (PairCoordinates m)) (Q : ℝ≥0∞) :
    W \ (W \ lowPairs a s t W Q) = lowPairs a s t W Q := by
  ext p
  constructor
  · intro hp
    by_contra hn
    exact hp.2 ⟨hp.1, hn⟩
  · intro hp
    exact ⟨hp.1, fun h ↦ h.2 hp⟩

theorem le_pairDensity_of_mem_sdiff_lowPairs {a s t : ℝ}
    {W : Set (PairCoordinates m)} {Q : ℝ≥0∞} {p : PairCoordinates m}
    (hp : p ∈ W \ lowPairs a s t W Q) :
    Q ≤ pairDensity a s t W (pairProjections a s t p) :=
  le_of_not_gt fun h ↦ hp.2 ⟨hp.1, h⟩

/-- Failure of the low-density mass condition gives a concentrated subset. -/
theorem exists_concentrated_pairs {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) {Q δ P : ℝ≥0∞}
    (hQ : 0 < Q) (hQfin : Q ≠ ∞) (hmass : volume W ≤ Q * P)
    (hlow : volume (lowPairs a s t W Q) < δ) :
    ∃ E : Set (PairCoordinates m), MeasurableSet E ∧ E ⊆ W ∧
      volume (W \ E) ≤ δ ∧ volume (pairProjections a s t '' E) ≤ P := by
  refine ⟨W \ lowPairs a s t W Q, hW.diff (measurableSet_lowPairs a s t hW Q),
    sdiff_subset, ?_, ?_⟩
  · simpa only [sdiff_sdiff_lowPairs] using hlow.le
  · apply (ENNReal.mul_le_mul_iff_right hQ.ne' hQfin).mp
    exact (mul_volume_pairProjections_image_le hs ht hW Q
      (fun _ hp ↦ le_pairDensity_of_mem_sdiff_lowPairs hp)).trans hmass

theorem lowPairs_eq_of_density_bound (a s t : ℝ) {W : Set (PairCoordinates m)}
    {Q : ℝ≥0∞} (hQ : ∀ p ∈ W, pairDensity a s t W (pairProjections a s t p) < Q) :
    lowPairs a s t W Q = W :=
  Subset.antisymm (lowPairs_subset a s t W Q) (fun p hp ↦ ⟨hp, hQ p hp⟩)

/-- A threshold above the one-projection density bound makes every pair low-density. -/
theorem lowPairs_eq_of_projection_bound (a s t : ℝ) {G : Set (Line m)}
    {W : Set (PairCoordinates m)} (hWG : W ⊆ pairFamily a G) {Q : ℝ≥0∞}
    (hQ : pairJacobian m a s t * volume (atHeight a '' G) < Q) :
    lowPairs a s t W Q = W :=
  lowPairs_eq_of_density_bound a s t (fun p _ ↦
    (pairDensity_le_projection a s t hWG (pairProjections a s t p)).trans_lt hQ)

end NKBesicovitch.Projection
