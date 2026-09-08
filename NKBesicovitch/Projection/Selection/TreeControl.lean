/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.TreeRealization
public import NKBesicovitch.Projection.Selection.NodeControl

/-!
# Uniformly controlled analytic trees from selected parameters

The realization keeps the common separation, input estimate, and label
count bounds at every internal node. The finite-tree stopping argument
can therefore use the same quantitative data throughout the tree.
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

theorem exists_controlled_cornerTree_of_mem_treeParameters {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) (J : ℕ) {q : (ℝ × ℝ) × ℝ}
    (hq : q ∈ separatedTriples I ((volume I).toReal / 100))
    {σ : TreeCoordinate D L J → ℝ} (hσ : σ ∈ S.treeParameters I J q) :
    ∃ T : CornerTree m β J,
      T.a T.root = q.1.1 ∧ T.b T.root = q.1.2 ∧ T.c T.root = q.2 ∧
        T.times ⊆ S.treeTimes J q σ ∧ ∀ v h,
          (T.pattern v h).IsControlled ((volume I).toReal / 100)
            (S.upperConstant * (100 / (volume I).toReal) ^ (8 * S.boundExponent)) L :=
  S.exists_cornerTree_of_mem_treeParameters_of_pattern_property hI hIunit hIpos
    (fun P ↦ P.IsControlled ((volume I).toReal / 100)
      (S.upperConstant * (100 / (volume I).toReal) ^ (8 * S.boundExponent)) L)
    (fun _ hq _ hp ↦ S.nodePattern_isControlled hI hIunit hIpos hq hp) J hq hσ

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
