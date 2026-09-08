/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.TreeUniformBound
public import NKBesicovitch.Projection.TreeThreshold

/-!
# The normalized bound from an admissible finite corner tree

Fix the tree before the line family. Balanced companions, the root and
terminal estimates, and finite stopping then supply all geometric inputs
to the corner bound. Constants are uniform across the finitely many nodes.
The theorem here treats line mass at least one and projection size above
the fixed threshold; the remaining bounded cases use the two-slice seed.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerTree

variable {m J : ℕ} {β : ℝ}

theorem exists_large_normalized_bound [Nonempty (Fin m)] (T : CornerTree m β J)
    (hJ : 0 < J) (hβ : 1 < β) (hβ2 : β ≤ 2) :
    let q := β / (β - 1)
    ∃ C N₀ : ℝ, 0 < C ∧ 1 ≤ N₀ ∧
      ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
      (parallelMultiplicity G).toReal ≤ 1 → 1 ≤ (volume G).toReal →
      ∀ N : ℝ, N₀ ≤ N → (∀ t ∈ T.times, volume (atHeight t '' G) ≤ ENNReal.ofReal N) →
      (volume G).toReal ≤ C *
        N ^ ((2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) /
          (q + 2 * q ^ 2 - 2)) := by
  classical
  let r := (T.times.card : ℝ)
  have hr : 0 < r := Nat.cast_pos.mpr T.times_nonempty.card_pos
  have hc₀ : 0 < 1 / (4 * r) := by positivity
  have hc₁ : (0 : ℝ) < 1 / 2 := by norm_num
  have hd : 0 < 1 / (2 * r) := by positivity
  let ι := {v : T.Node // T.level v < J}
  choose B _ hB using fun v : ι ↦
    (T.pattern v.val v.property).exists_stopping_node_constant hβ hβ2 hc₀ hc₁ hd
  obtain ⟨D, hD⟩ := (Set.finite_range B).bddAbove
  obtain ⟨N₀, hN₀, hthreshold⟩ := T.exists_stopping_threshold hJ hc₀
  have hbound (v : T.Node) (hv : T.level v < J) :
      (T.pattern v hv).StoppingNodeBound (1 / (4 * r)) (1 / 2) (1 / (2 * r)) (max 1 D) :=
    (hB (⟨v, hv⟩ : ι)).mono
      ((hD (Set.mem_range_self (⟨v, hv⟩ : ι))).trans (le_max_right _ _))
  refine ⟨max 1 D, N₀, zero_lt_one.trans_le (le_max_left _ _), hN₀,
    fun G hG hGb hM hL N hN hπ ↦ ?_⟩
  obtain ⟨hroot, hprune⟩ := hthreshold N hN
  exact T.large_normalized_bound_of_stoppingNodeBounds hJ le_rfl hbound
    hG hGb hM hL (hN₀.trans hN) hπ hroot hprune

end NKBesicovitch.Projection.CornerTree
