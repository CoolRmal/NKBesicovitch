/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerTree
public import NKBesicovitch.Projection.FiniteStopping
public import NKBesicovitch.Projection.StoppingBoundary

/-!
# Selecting a stopping node in an admissible corner tree

Equal positive pair masses and bounds on all tree projections supply the
root and terminal hypotheses of finite stopping. For sufficiently large
projection size, a nonterminal node has enough low-density parent mass,
and every next-level family admits a concentrated subset.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerTree

variable {m J : ℕ} {β : ℝ}

theorem exists_stopping_node (T : CornerTree m β J) (hJ : 0 < J)
    {G : Set (Line m)} (W : T.Node → Set (PairCoordinates m))
    (hW : ∀ v, MeasurableSet (W v)) (hWG : ∀ v, W v ⊆ pairFamily (T.a v) G)
    {V : ℝ≥0∞} (hVpos : 0 < V) (hVfin : V ≠ ∞) (hmass : ∀ v, volume (W v) = V)
    {c L N : ℝ} (hc : 0 ≤ c) (hL : 1 ≤ L) (hN : 1 ≤ N)
    (hV : c * L ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤ V.toReal)
    (hπ : ∀ t ∈ T.times, volume (atHeight t '' G) ≤ ENNReal.ofReal N)
    (hlarge : (pairJacobian m (T.a T.root) (T.b T.root) (T.c T.root)).toReal <
      c * N ^ (96 : ℝ)) :
    ∃ v : T.Node, T.level v < J ∧
      V * ENNReal.ofReal (N ^ (-stoppingAlpha J (T.level v))) ≤
        volume (lowPairs (T.a v) (T.b v) (T.c v) (W v)
          (V * ENNReal.ofReal (N ^ (-2 + stoppingRho J (T.level v))))) ∧
      ∀ w : T.Node, T.level w = T.level v + 1 →
        ∃ E : Set (PairCoordinates m), MeasurableSet E ∧ E ⊆ W w ∧
          volume (W w \ E) ≤ V * ENNReal.ofReal (N ^ (-stoppingAlpha J (T.level w))) ∧
          volume (pairProjections (T.a w) (T.b w) (T.c w) '' E) ≤
            ENNReal.ofReal (N ^ (2 - stoppingRho J (T.level w))) := by
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  have hroot := root_lowPairs_eq hc hL hN (hWG T.root) hVfin hV
    (hπ _ (T.a_mem_times T.root)) hlarge J
  have hquota : V * ENNReal.ofReal (N ^ (-stoppingAlpha J 0)) ≤ V := by
    calc
      _ ≤ V * 1 := mul_le_mul le_rfl (by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one_of_one_le_of_nonpos hN
          (neg_nonpos.mpr (stoppingAlpha_pos hJ 0).le))) bot_le bot_le
      _ = _ := mul_one V
  have hterminal (v : T.Node) (hv : J ≤ T.level v) :
      volume (pairProjections (T.a v) (T.b v) (T.c v) '' W v) ≤
        ENNReal.ofReal (N ^ (2 - stoppingRho J (T.level v))) := by
    have he : T.level v = J := (T.level_le v).antisymm hv
    simpa only [he, stoppingRho_self hJ, sub_zero] using volume_pairProjections_le_square
      hNpos.le (hWG v) (hπ _ (T.b_mem_times v)) (hπ _ (T.c_mem_times v))
  obtain ⟨v, _, hv, hparent, hchildren⟩ := exists_uniform_node_concentrated_children
    Finset.univ T.level J T.a T.b T.c W
    (fun i ↦ V * ENNReal.ofReal (N ^ (-2 + stoppingRho J i)))
    (fun i ↦ V * ENNReal.ofReal (N ^ (-stoppingAlpha J i)))
    (fun i ↦ ENNReal.ofReal (N ^ (2 - stoppingRho J i)))
    (fun v _ ↦ hW v) (fun v _ ↦ T.b_ne_a v) (fun v _ ↦ T.c_ne_a v)
    (fun v _ _ ↦ ENNReal.mul_pos hVpos.ne'
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hNpos _)).ne')
    (fun _ _ _ ↦ by finiteness)
    (fun v _ _ ↦ by rw [hmass, stopping_density_mul_image_ennreal V hNpos])
    (fun v _ ↦ hterminal v) ⟨T.root, Finset.mem_univ _, by simpa only [T.root_level] using hJ,
      by simpa only [T.root_level, hroot, hmass] using hquota⟩
  exact ⟨v, hv, hparent, fun w ↦ hchildren w (Finset.mem_univ _)⟩

end NKBesicovitch.Projection.CornerTree
