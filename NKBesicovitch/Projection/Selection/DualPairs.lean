/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.SeparatedTimes
public import Mathlib.Tactic.FinCases

/-!
# Separated time pairs for the dual-code reservoir

Both times stay away from the two base heights and from each other by
`|I|/100`. These five separations still leave at least `|I|²/2` of pair
measure. This is the geometric domain of the change of variables from
the second time to the dual-code scalar.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Time pairs with the five separations required by the dual-code change of variables. -/
noncomputable def dualPairParameters (I : Set ℝ) (a b : ℝ) : Set (ℝ × ℝ) :=
  separatedPairs (separatedTimes I ![a, b] Finset.univ ((volume I).toReal / 100))
    ((volume I).toReal / 100)

theorem measurableSet_dualPairParameters {I : Set ℝ} (hI : MeasurableSet I) (a b : ℝ) :
    MeasurableSet (dualPairParameters I a b) :=
  measurableSet_separatedPairs (measurableSet_separatedTimes hI _ _ _) _

theorem measurableSet_dualPairParameters_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    MeasurableSet {p : X × (ℝ × ℝ) |
      p.2 ∈ dualPairParameters {t | (p.1, t) ∈ I} (a p.1) (b p.1)} := by
  have hr := (measurable_measure_prodMk_left (ν := volume) hI).ennreal_toReal.div_const 100
  have hbase (i : Fin 2) : Measurable (fun x ↦ ![a x, b x] i) := by
    fin_cases i
    · exact ha
    · exact hb
  exact measurableSet_separatedPairs_family
    (measurableSet_separatedTimes_family hI Finset.univ (fun i _ ↦ hbase i) hr) hr

theorem dualPairParameters_spec {I : Set ℝ} {a b : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ dualPairParameters I a b) :
    p.1 ∈ I ∧ p.2 ∈ I ∧
      (volume I).toReal / 100 ≤ dist p.1 a ∧ (volume I).toReal / 100 ≤ dist p.1 b ∧
      (volume I).toReal / 100 ≤ dist p.2 a ∧ (volume I).toReal / 100 ≤ dist p.2 b ∧
      (volume I).toReal / 100 ≤ dist p.1 p.2 := by
  have hs := mem_separatedTimes.mp hp.1.1
  have ht := mem_separatedTimes.mp hp.1.2
  exact ⟨hs.1, ht.1, hs.2 0 (Finset.mem_univ _), hs.2 1 (Finset.mem_univ _),
    ht.2 0 (Finset.mem_univ _), ht.2 1 (Finset.mem_univ _), hp.2⟩

theorem dualPairParameters_ne {I : Set ℝ} (hIpos : 0 < volume I) (hIfin : volume I ≠ ∞)
    {a b : ℝ} {p : ℝ × ℝ} (hp : p ∈ dualPairParameters I a b) :
    p.1 ≠ a ∧ p.1 ≠ b ∧ p.2 ≠ a ∧ p.2 ≠ b ∧ p.1 ≠ p.2 := by
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hr : 0 < (volume I).toReal / 100 := by positivity
  obtain ⟨_, _, hta, htb, hua, hub, htu⟩ := dualPairParameters_spec hp
  exact ⟨dist_pos.mp (hr.trans_le hta), dist_pos.mp (hr.trans_le htb),
    dist_pos.mp (hr.trans_le hua), dist_pos.mp (hr.trans_le hub), dist_pos.mp (hr.trans_le htu)⟩

theorem half_square_le_volume_dualPairParameters {I : Set ℝ} (hI : MeasurableSet I)
    (hIfin : volume I ≠ ∞) (a b : ℝ) :
    ENNReal.ofReal ((volume I).toReal ^ 2 / 2) ≤ volume (dualPairParameters I a b) := by
  let A := separatedTimes I ![a, b] Finset.univ ((volume I).toReal / 100)
  have hA : MeasurableSet A := measurableSet_separatedTimes hI _ _ _
  have hAfin : volume A ≠ ∞ := ne_top_of_le_ne_top hIfin (measure_mono inter_subset_left)
  have hL : 0 ≤ (volume I).toReal := ENNReal.toReal_nonneg
  have hLA : 0 ≤ (volume A).toReal := ENNReal.toReal_nonneg
  have hretained : (volume I).toReal - 4 * ((volume I).toReal / 100) ≤ (volume A).toReal := by
    have h := volume_separatedTimes_lower I ![a, b] Finset.univ
      (by positivity : 0 ≤ (volume I).toReal / 100)
    norm_num only [Finset.card_univ, Fintype.card_fin] at h
    change (volume I).toReal - 2 * ((volume I).toReal / 100) * 2 ≤ (volume A).toReal at h
    linarith
  have hlow₁ : 3 / 4 * (volume I).toReal ≤ (volume A).toReal := by linarith
  have hlow₂ : 3 / 4 * (volume I).toReal ≤
      (volume A).toReal - 2 * ((volume I).toReal / 100) := by linarith
  have hnonneg : 0 ≤ (volume A).toReal - 2 * ((volume I).toReal / 100) := by linarith
  refine le_trans ?_ (volume_separatedPairs_lower hA (by positivity))
  conv_rhs => arg 2; rw [← ENNReal.ofReal_toReal hAfin]
  rw [← ENNReal.ofReal_mul hnonneg]
  apply ENNReal.ofReal_le_ofReal
  have hprod := mul_le_mul hlow₂ hlow₁ (by positivity) hnonneg
  nlinarith [sq_nonneg (volume I).toReal]

end NKBesicovitch.Projection.Selection
