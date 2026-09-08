/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerTree
public import NKBesicovitch.Projection.StoppingBoundary

/-!
# One projection-size threshold for a finite corner tree

The root density condition and every internal child-deletion budget hold
above one fixed finite threshold. This threshold is chosen before the
line family and depends only on the tree and balanced-mass coefficient.
-/

public section

namespace NKBesicovitch.Projection.CornerTree

variable {m J : ℕ} {β : ℝ}

theorem exists_stopping_threshold (T : CornerTree m β J) (hJ : 0 < J)
    {c : ℝ} (hc : 0 < c) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N, N₀ ≤ N →
      (pairJacobian m (T.a T.root) (T.b T.root) (T.c T.root)).toReal < c * N ^ (96 : ℝ) ∧
      ∀ (v : T.Node) (hv : T.level v < J),
        4 * (1 + 2 * ((T.pattern v hv).outer.card : ℝ)) * (T.pattern v hv).children.card ≤
          N ^ (1 / (J : ℝ) ^ 2) := by
  classical
  obtain ⟨R, _, hR⟩ := exists_root_threshold hc
    (pairJacobian m (T.a T.root) (T.b T.root) (T.c T.root)).toReal
  let ι := {v : T.Node // T.level v < J}
  choose B _ hB using fun v : ι ↦ exists_child_pruning_threshold
    ((T.pattern v.val v.property).children.card : ℝ)
    ((T.pattern v.val v.property).outer.card : ℝ) hJ
  obtain ⟨D, hD⟩ := (Set.finite_range B).bddAbove
  refine ⟨max 1 (max R D), le_max_left _ _, fun N hN ↦ ⟨?_, fun v hv ↦ ?_⟩⟩
  · exact hR N ((le_max_left R D).trans ((le_max_right _ _).trans hN))
  · exact hB (⟨v, hv⟩ : ι) N ((hD (Set.mem_range_self (⟨v, hv⟩ : ι))).trans
      ((le_max_right R D).trans ((le_max_right _ _).trans hN)))

end NKBesicovitch.Projection.CornerTree
