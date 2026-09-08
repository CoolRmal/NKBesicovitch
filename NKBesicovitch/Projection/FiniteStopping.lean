/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Concentration
public import Mathlib.Data.Finset.Max

/-!
# A deepest uniform node and concentrated children

Nodes are labels in a finite family, so repeated numerical heights remain
distinct nodes. The deepest node satisfying the low-density mass condition
has no such node at a later nonterminal level. Terminal nodes use their
original projection-image bound and discard no mass.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι : Type*}

theorem exists_deepest_uniform_node (I : Finset ι) (level : ι → ℕ) (J : ℕ)
    (a s t : ι → ℝ) (W : ι → Set (PairCoordinates m)) (Q δ : ℕ → ℝ≥0∞)
    (hroot : ∃ v ∈ I, level v < J ∧
      δ (level v) ≤ volume (lowPairs (a v) (s v) (t v) (W v) (Q (level v)))) :
    ∃ v ∈ I, level v < J ∧
      δ (level v) ≤ volume (lowPairs (a v) (s v) (t v) (W v) (Q (level v))) ∧
      ∀ w ∈ I, level v < level w → level w < J →
        volume (lowPairs (a w) (s w) (t w) (W w) (Q (level w))) < δ (level w) := by
  classical
  let U := I.filter fun v ↦ level v < J ∧
    δ (level v) ≤ volume (lowPairs (a v) (s v) (t v) (W v) (Q (level v)))
  have hU : U.Nonempty := by
    obtain ⟨v, hv, hlevel, hmass⟩ := hroot
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hlevel, hmass⟩⟩
  obtain ⟨v, hv, hmax⟩ := U.exists_max_image level hU
  have hv' := Finset.mem_filter.mp hv
  refine ⟨v, hv'.1, hv'.2.1, hv'.2.2, fun w hw hvw hwJ ↦ ?_⟩
  apply lt_of_not_ge
  intro hmass
  exact (not_le_of_gt hvw) (hmax w (Finset.mem_filter.mpr ⟨hw, hwJ, hmass⟩))

/-- Choose a low-density parent whose next-level nodes all admit concentrated subsets. -/
theorem exists_uniform_node_concentrated_children (I : Finset ι) (level : ι → ℕ) (J : ℕ)
    (a s t : ι → ℝ) (W : ι → Set (PairCoordinates m)) (Q δ P : ℕ → ℝ≥0∞)
    (hW : ∀ v ∈ I, MeasurableSet (W v))
    (hs : ∀ v ∈ I, s v ≠ a v) (ht : ∀ v ∈ I, t v ≠ a v)
    (hQ : ∀ v ∈ I, level v < J → 0 < Q (level v))
    (hQfin : ∀ v ∈ I, level v < J → Q (level v) ≠ ∞)
    (hmass : ∀ v ∈ I, level v < J → volume (W v) ≤ Q (level v) * P (level v))
    (hleaf : ∀ v ∈ I, J ≤ level v → volume (pairProjections (a v) (s v) (t v) '' W v) ≤
      P (level v))
    (hroot : ∃ v ∈ I, level v < J ∧
      δ (level v) ≤ volume (lowPairs (a v) (s v) (t v) (W v) (Q (level v)))) :
    ∃ v ∈ I, level v < J ∧
      δ (level v) ≤ volume (lowPairs (a v) (s v) (t v) (W v) (Q (level v))) ∧
      ∀ w ∈ I, level w = level v + 1 →
        ∃ E : Set (PairCoordinates m), MeasurableSet E ∧ E ⊆ W w ∧
          volume (W w \ E) ≤ δ (level w) ∧
          volume (pairProjections (a w) (s w) (t w) '' E) ≤ P (level w) := by
  obtain ⟨v, hv, hvJ, hparent, hdeep⟩ :=
    exists_deepest_uniform_node I level J a s t W Q δ hroot
  refine ⟨v, hv, hvJ, hparent, fun w hw hlevel ↦ ?_⟩
  by_cases hwJ : level w < J
  · apply exists_concentrated_pairs (hs w hw) (ht w hw) (hW w hw)
      (hQ w hw hwJ) (hQfin w hw hwJ) (hmass w hw hwJ)
    exact hdeep w hw (by rw [hlevel]; exact Nat.lt_succ_self _) hwJ
  · exact ⟨W w, hW w hw, Subset.rfl, by simp, hleaf w hw (le_of_not_gt hwJ)⟩

end NKBesicovitch.Projection
