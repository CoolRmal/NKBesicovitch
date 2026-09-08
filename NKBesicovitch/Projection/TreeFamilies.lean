/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.TreeStopping
public import NKBesicovitch.Projection.CompanionSystem

/-!
# The parent and child families selected by tree stopping

Balanced companions at equal heights are shared throughout the tree.
Consequently each numerical child family is the inner companion-pair
family required by its parent's corner pattern. The selected parent and
children satisfy the hypotheses of the stopping-node estimate.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerTree

variable {m J : ℕ} {β : ℝ}

theorem exists_stopping_families (T : CornerTree m β J) (hJ : 0 < J)
    {G : Set (Line m)} (S : CompanionSystem G T.times)
    {V : ℝ≥0∞} (hVpos : 0 < V) (hVfin : V ≠ ∞) (hVeq : volume S.centers * S.η = V)
    {c L N : ℝ} (hc : 0 ≤ c) (hL : 1 ≤ L) (hN : 1 ≤ N)
    (hV : c * L ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤ V.toReal)
    (hπ : ∀ t ∈ T.times, volume (atHeight t '' G) ≤ ENNReal.ofReal N)
    (hlarge : (pairJacobian m (T.a T.root) (T.b T.root) (T.c T.root)).toReal <
      c * N ^ (96 : ℝ)) :
    ∃ (v : T.Node) (hv : T.level v < J),
      let P := T.pattern v hv
      ∃ U : Set (PairCoordinates m), MeasurableSet U ∧
        U ⊆ companionPairs P.a S.centers (S.companion P.a) ∧
        V * ENNReal.ofReal (N ^ (-stoppingAlpha J (T.level v))) ≤ volume U ∧
        (∀ p ∈ U, pairDensity P.a P.b P.c (companionPairs P.a S.centers (S.companion P.a))
          (pairProjections P.a P.b P.c p) ≤
            V * ENNReal.ofReal (N ^ (-2 + stoppingRho J (T.level v)))) ∧
        ∀ u ∈ P.children, ∃ E : Set (PairCoordinates m), MeasurableSet E ∧
          E ⊆ companionPairs P.b S.centers (S.companion P.b) ∧
          volume (companionPairs P.b S.centers (S.companion P.b) \ E) ≤
            V * ENNReal.ofReal (N ^ (-stoppingAlpha J (T.level v + 1))) ∧
          volume (pairProjections P.b u.2
            (dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u.1) u.2) '' E) ≤
              ENNReal.ofReal (N ^ (2 - stoppingRho J (T.level v + 1))) := by
  let W (v : T.Node) := companionPairs (T.a v) S.centers (S.companion (T.a v))
  have hW (v : T.Node) : MeasurableSet (W v) := measurableSet_companionPairs _
    S.centers_measurable (S.companion_measurable _ (T.a_mem_times v))
  have hWG (v : T.Node) : W v ⊆ pairFamily (T.a v) G :=
    companionPairs_subset_pairFamily _ S.centers_subset (S.companion_subset _ (T.a_mem_times v))
  have hmass (v : T.Node) : volume (W v) = V := by
    change volume (companionPairs (T.a v) S.centers (S.companion (T.a v))) = V
    rw [volume_companionPairs_of_constant_mass _ S.centers_measurable
      (S.companion_measurable _ (T.a_mem_times v)) S.η]
    · exact hVeq
    · rintro _ ⟨g, hg, rfl⟩
      exact S.slice_eq _ (T.a_mem_times v) g hg
  obtain ⟨v, hv, hparent, hchildren⟩ :=
    T.exists_stopping_node hJ W hW hWG hVpos hVfin hmass hc hL hN hV hπ hlarge
  refine ⟨v, hv, ?_⟩
  simp only [T.pattern_a, T.pattern_b, T.pattern_c]
  refine ⟨lowPairs (T.a v) (T.b v) (T.c v) (W v)
    (V * ENNReal.ofReal (N ^ (-2 + stoppingRho J (T.level v)))),
    measurableSet_lowPairs _ _ _ (hW v) _, lowPairs_subset _ _ _ _ _,
    hparent, fun _ hp ↦ hp.2.le, fun u hu ↦ ?_⟩
  have h := hchildren (T.child v hv ⟨u, hu⟩) (T.child_level v hv ⟨u, hu⟩)
  simpa only [W, T.child_a, T.child_b, T.child_c, T.child_level] using h

end NKBesicovitch.Projection.CornerTree
