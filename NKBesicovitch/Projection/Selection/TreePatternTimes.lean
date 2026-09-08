/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.TreeTimes

/-!
# The selected root pattern uses only labeled tree heights

Representative labels recover each numerical child. Its inner and dual
heights are the second and third entries of the corresponding child root,
so both occur among the recursive measurable output labels.
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

theorem nodePattern_times_subset_treeTimes {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) (J : ℕ) {q : (ℝ × ℝ) × ℝ}
    (hq : q ∈ separatedTriples I ((volume I).toReal / 100))
    {σ : TreeCoordinate D L (J + 1) → ℝ}
    (hσ : σ ∈ S.treeParameters I (J + 1) q) :
    (S.nodePattern hI hIunit hIpos hq hσ.1).times ⊆ S.treeTimes (J + 1) q σ := by
  have hchild (u : (S.nodePattern hI hIunit hIpos hq hσ.1).children) (i : Fin 3) :
      ![q.1.2, u.val.2,
        dualTime q.1.2 q.1.1
          (cornerInnerCoefficient q.1.1 q.2 (TreeCoordinate.splitEquiv D L J σ).1.1 u.val.1)
          u.val.2] i ∈ S.treeTimes (J + 1) q σ := by
    let ij := S.nodeChildLabels (TreeCoordinate.splitEquiv D L J σ).1 u.val
    have h := S.child_treeTimes_subset J q σ ij (S.base_mem_treeTimes J _ _ i)
    have he := S.nodeChildTriple_nodeChildLabels hI hIunit hIpos hq hσ.1 u.property
    simpa only [ij, he] using h
  apply CornerPattern.times_subset (I := ↑(S.treeTimes (J + 1) q σ))
  · exact S.base_mem_treeTimes (J + 1) q σ 0
  · exact S.base_mem_treeTimes (J + 1) q σ 1
  · exact S.base_mem_treeTimes (J + 1) q σ 2
  · intro u hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    exact S.mem_treeTimes.mpr ⟨Sum.inl (Sum.inr i), rfl⟩
  · intro u hu t ht
    exact hchild ⟨(u, t), CornerPattern.mem_children.mpr ⟨hu, ht⟩⟩ 1
  · intro u hu t ht
    exact hchild ⟨(u, t), CornerPattern.mem_children.mpr ⟨hu, ht⟩⟩ 2

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
