/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Hausdorff.DyadicCover

/-!
# Hausdorff dimension from a plate maximal estimate

The covering-cost lower bound rules out zero `s`-dimensional Hausdorff
measure for every positive `s < n-α`. The resulting dimension theorem
applies to arbitrary sets, with no measurability or boundedness assumption.
-/

public section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology

namespace NKBesicovitch.Hausdorff

private theorem exists_small_cost_aux (C : ℝ≥0) {q : ℝ} (hq : 0 < q) :
    ∃ ε : ℝ≥0, 0 < ε ∧ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ q < 1 := by
  have hc : Continuous (fun ε : ℝ≥0 ↦ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ q) :=
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
      (ENNReal.continuous_rpow_const.comp ENNReal.continuous_coe)
  have he : (C : ℝ≥0∞) * ((0 : ℝ≥0) : ℝ≥0∞) ^ q < 1 := by
    simp [ENNReal.zero_rpow_of_pos hq]
  have h := (hc.tendsto 0).eventually (gt_mem_nhds he)
  obtain ⟨ε, hε, hε0, -⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from zero_lt_one))).exists
  exact ⟨ε, hε0, hε⟩

/-- Hausdorff measure cannot vanish below the dimension supplied by a plate estimate. -/
theorem hausdorffMeasure_ne_zero_of_plateEstimate {n k : ℕ} {hkn : k ≤ n} {α p s : ℝ}
    (hp : 1 ≤ p) (hs : 0 < s) (hgap : s < (n : ℝ) - α)
    (h : Induction.HasPlateEstimate hkn α p) {E : Set (EuclideanSpace ℝ (Fin n))}
    (hB : IsBesicovitch k E) : μH[s] E ≠ 0 := by
  intro hzero
  obtain ⟨C, hC⟩ := exists_ball_cover_cost_bound hp hs.le hgap h
  obtain ⟨ε, hε, hεcost⟩ := exists_small_cost_aux C
    (one_div_pos.mpr (zero_lt_one.trans_le hp))
  obtain ⟨x, r, hr, hcover, hcost⟩ := exists_ball_cover_of_measure_zero hs hzero
    (ENNReal.coe_pos.mpr hε)
  have hbound := hC hB x r (fun i ↦ ⟨(hr i).1, (hr i).2.le⟩) hcover
  have hsmall : (C : ℝ≥0∞) * (∑' i, (r i : ℝ≥0∞) ^ s) ^ (1 / p) ≤
      (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (1 / p) :=
    mul_le_mul_right (ENNReal.rpow_le_rpow hcost.le
      (one_div_nonneg.mpr (zero_le_one.trans hp))) _
  exact (hbound.trans hsmall).not_gt hεcost

end NKBesicovitch.Hausdorff

namespace NKBesicovitch.Induction

/-- A plate maximal estimate with deficit `α` gives Hausdorff dimension at least `n-α`. -/
theorem HasPlateEstimate.le_dimH {n k : ℕ} {hkn : k ≤ n} {α p : ℝ} (hp : 1 ≤ p)
    (h : HasPlateEstimate hkn α p) {E : Set (EuclideanSpace ℝ (Fin n))}
    (hB : IsBesicovitch k E) : ENNReal.ofReal ((n : ℝ) - α) ≤ dimH E := by
  by_contra! hlt
  obtain ⟨s, hs, hsn⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hs0 : 0 < (s : ℝ) := by
    exact_mod_cast (ENNReal.coe_pos.mp (bot_le.trans_lt hs))
  exact Hausdorff.hausdorffMeasure_ne_zero_of_plateEstimate hp hs0
    (ENNReal.coe_lt_ofReal.mp hsn) h hB (hausdorffMeasure_of_dimH_lt hs)

end NKBesicovitch.Induction
