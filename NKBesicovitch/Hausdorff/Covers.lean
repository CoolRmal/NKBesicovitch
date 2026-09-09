/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.NormNum

/-!
# Small ball covers of Hausdorff-null sets

The defining diameter covers can be enlarged to open balls with positive
radii and arbitrarily small total cost. This also handles singleton and
empty members of a cover without discarding any points.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology

namespace NKBesicovitch.Hausdorff

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exists_diameter_cover_of_measure_zero {s : ℝ} {E : Set X}
    (hE : μH[s] E = 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t : ℕ → Set X, E ⊆ ⋃ i, t i ∧ (∀ i, ediam (t i) ≤ 1 / 2) ∧
      (∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ s) < ε := by
  have h : (⨅ (t : ℕ → Set X) (_ : E ⊆ ⋃ i, t i)
      (_ : ∀ i, ediam (t i) ≤ (1 / 2 : ℝ≥0∞)),
        ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ s) < ε := by
    apply lt_of_le_of_lt _ hε
    rw [← hE, hausdorffMeasure_apply]
    exact le_iSup₂_of_le (1 / 2) (by norm_num) le_rfl
  obtain ⟨t, ht, hd, hc⟩ := (by simpa only [iInf_lt_iff] using h)
  exact ⟨t, ht, hd, hc⟩

private theorem exists_larger_radius_aux {s : ℝ} (hs : 0 < s) {d : ℝ≥0} (hd : d < 1)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ≥0, d < r ∧ r < 1 ∧ (r : ℝ≥0∞) ^ s < (d : ℝ≥0∞) ^ s + ε := by
  have hcost : ∀ᶠ r : ℝ≥0 in 𝓝 d,
      (r : ℝ≥0∞) ^ s < (d : ℝ≥0∞) ^ s + ε :=
    ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_coe).tendsto d).eventually
      (gt_mem_nhds (ENNReal.lt_add_right
        (ENNReal.rpow_ne_top_of_nonneg hs.le ENNReal.coe_ne_top) hε.ne'))
  obtain ⟨r, hc, hr, hr1⟩ :=
    ((hcost.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hd)).exists
  exact ⟨r, hr, hr1, hc⟩

theorem exists_ball_cover_of_measure_zero [Nonempty X] {s : ℝ} (hs : 0 < s)
    {E : Set X} (hE : μH[s] E = 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (x : ℕ → X) (r : ℕ → ℝ≥0), (∀ i, 0 < r i ∧ r i < 1) ∧
      E ⊆ ⋃ i, ball (x i) (r i) ∧ (∑' i, (r i : ℝ≥0∞) ^ s) < ε := by
  classical
  obtain ⟨t, ht, hd, hc⟩ := exists_diameter_cover_of_measure_zero hE
    (ENNReal.half_pos hε.ne')
  obtain ⟨η, hη, hηsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.half_pos hε.ne').ne' ℕ
  have hdtop (i) : ediam (t i) ≠ ∞ := ne_top_of_le_ne_top (by norm_num) (hd i)
  have hdi (i) : (ediam (t i)).toNNReal < 1 := by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal (hdtop i), ENNReal.coe_one]
    exact (hd i).trans_lt (by norm_num)
  choose r hr hr1 hrc using fun i ↦ exists_larger_radius_aux hs (hdi i)
    (ENNReal.coe_pos.mpr (hη i))
  have hcover (i) : ∃ x : X, t i ⊆ ball x (r i) := by
    by_cases hne : (t i).Nonempty
    · obtain ⟨x, hx⟩ := hne
      refine ⟨x, fun y hy ↦ ?_⟩
      have h := (edist_le_ediam_of_mem hy hx).trans_lt
        (by simpa only [ENNReal.coe_toNNReal (hdtop i)] using ENNReal.coe_lt_coe.mpr (hr i))
      rw [edist_nndist] at h
      exact_mod_cast (ENNReal.coe_lt_coe.mp h : nndist y x < r i)
    · exact ⟨Classical.arbitrary X, (not_nonempty_iff_eq_empty.mp hne) ▸ empty_subset _⟩
  choose x hx using hcover
  refine ⟨x, r, fun i ↦ ⟨zero_le.trans_lt (hr i), hr1 i⟩,
    ht.trans (iUnion_mono hx), ?_⟩
  have he (i) : ((ediam (t i)).toNNReal : ℝ≥0∞) ^ s =
      ⨆ _ : (t i).Nonempty, ediam (t i) ^ s := by
    rw [ENNReal.coe_toNNReal (hdtop i)]
    by_cases hne : (t i).Nonempty
    · simp only [iSup_pos hne]
    · simp [not_nonempty_iff_eq_empty.mp hne, ENNReal.zero_rpow_of_pos hs]
  calc
    _ ≤ ∑' i, (((ediam (t i)).toNNReal : ℝ≥0∞) ^ s + η i) :=
      ENNReal.tsum_le_tsum fun i ↦ (hrc i).le
    _ = (∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ s) + ∑' i, (η i : ℝ≥0∞) := by
      simp_rw [ENNReal.tsum_add, he]
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hc hηsum
    _ = ε := ENNReal.add_halves ε

end NKBesicovitch.Hausdorff
