/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.TreePatternTimes
public import NKBesicovitch.Projection.TreeConstruction

/-!
# Realizing selected coordinates as analytic corner trees

Every selected parameter gives an admissible finite corner tree with the
prescribed root triple. The tree uses only the measurable labeled output
heights. At duplicate numerical outer heights, representative labels
choose the corresponding child subtree.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

/-- Realization of every selected parameter with no extra projection heights. -/
theorem exists_cornerTree_of_mem_treeParameters {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) (J : ℕ) {q : (ℝ × ℝ) × ℝ}
    (hq : q ∈ separatedTriples I ((volume I).toReal / 100))
    {σ : TreeCoordinate D L J → ℝ} (hσ : σ ∈ S.treeParameters I J q) :
    ∃ T : CornerTree m β J,
      T.a T.root = q.1.1 ∧ T.b T.root = q.1.2 ∧ T.c T.root = q.2 ∧
        T.times ⊆ S.treeTimes J q σ := by
  classical
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hr : 0 < (volume I).toReal / 100 := by positivity
  induction J generalizing q with
  | zero =>
    have hb := mem_separatedTriples.mp hq
    refine ⟨CornerTree.leaf (dist_pos.mp (hr.trans_le hb.2.2.2.1)).symm
      (dist_pos.mp (hr.trans_le hb.2.2.2.2.1)).symm
      (dist_pos.mp (hr.trans_le hb.2.2.2.2.2)).symm, rfl, rfl, rfl, ?_⟩
    apply CornerTree.times_subset (I := ↑(S.treeTimes 0 q σ))
    · exact fun _ ↦ S.base_mem_treeTimes 0 q σ 0
    · exact fun _ ↦ S.base_mem_treeTimes 0 q σ 1
    · exact fun _ ↦ S.base_mem_treeTimes 0 q σ 2
    · exact fun _ h ↦ (Nat.not_lt_zero _ h).elim
  | succ J ih =>
    let P := S.nodePattern hI hIunit hIpos hq hσ.1
    have hchild (u : P.children) : ∃ T : CornerTree m β J,
        T.a T.root = P.b ∧ T.b T.root = u.val.2 ∧
          T.c T.root = dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u.val.1) u.val.2 ∧
            T.times ⊆ S.treeTimes (J + 1) q σ := by
      let ij := S.nodeChildLabels (TreeCoordinate.splitEquiv D L J σ).1 u.val
      have hg := S.cornerNodeParameters_child_triple hI hIunit hIpos hr
        (mem_separatedTriples.mp hq).2.1 hσ.1 ij.1 ij.2
      obtain ⟨T, ha, hb, hc, ht⟩ := ih
        (q := S.nodeChildTriple q.1.1 q.1.2 q.2 (TreeCoordinate.splitEquiv D L J σ).1 ij)
        hg (hσ.2 ij)
      have he := S.nodeChildTriple_nodeChildLabels hI hIunit hIpos hq hσ.1 u.property
      refine ⟨T, ha, ?_, ?_, ht.trans (S.child_treeTimes_subset J q σ ij)⟩
      · simpa only [ij, he] using hb
      · change T.c T.root = dualTime q.1.2 q.1.1
          (cornerInnerCoefficient q.1.1 q.2 (TreeCoordinate.splitEquiv D L J σ).1.1 u.val.1) u.val.2
        simpa only [ij, he] using hc
    choose B hBa hBb hBc hBt using hchild
    refine ⟨CornerTree.graft P B hBa hBb hBc, rfl, rfl, rfl, ?_⟩
    exact CornerTree.graft_times_subset P B hBa hBb hBc
      (S.nodePattern_times_subset_treeTimes hI hIunit hIpos J hq hσ) hBt

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
