/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.CornerRelation

/-!
# Measure of the compatible outer time-scalar relation

For each separated outer time, converting the inner scalar reservoir
to outer scalars multiplies its measure by at least `|I|/100`.
At least `|I|/2` of outer times remain, and the inner scalar reservoir
has measure at least `δ|I|²/400`. Thus the compatible relation has
measure at least `δ|I|⁴/80000`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

theorem volume_cornerTimeRelation {I : Set ℝ} (hI : MeasurableSet I) (a b c δ : ℝ) :
    volume (cornerTimeRelation I a b c δ) =
      ∫⁻ u in separatedTimes I ![a, c] Finset.univ ((volume I).toReal / 100),
        volume ((fun κ ↦ cornerInnerCoefficient a c κ u) ⁻¹' dualReservoir I b a δ) := by
  let A := separatedTimes I ![a, c] Finset.univ ((volume I).toReal / 100)
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_cornerTimeRelation hI a b c δ)]
  have he : (fun u ↦ volume (Prod.mk u ⁻¹' cornerTimeRelation I a b c δ)) =
      A.indicator (fun u ↦
        volume ((fun κ ↦ cornerInnerCoefficient a c κ u) ⁻¹' dualReservoir I b a δ)) := by
    funext u
    by_cases hu : u ∈ A
    · rw [Set.indicator_of_mem hu, cornerTimeRelation_section hu]
    · rw [Set.indicator_of_notMem hu]
      have hz : Prod.mk u ⁻¹' cornerTimeRelation I a b c δ = ∅ := by
        ext κ
        simp only [cornerTimeRelation, mem_preimage, mem_ofPred_eq, show u ∉
          separatedTimes I ![a, c] Finset.univ ((volume I).toReal / 100) from hu,
          false_and, mem_empty_iff_false]
      rw [hz, measure_empty]
  rw [he, lintegral_indicator (measurableSet_separatedTimes hI _ _ _)]

theorem volume_corner_scalar_preimage_lower {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a c u : ℝ} (ha : a ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hu : u ∈ separatedTimes I ![a, c] Finset.univ ((volume I).toReal / 100)) (S : Set ℝ) :
    ENNReal.ofReal ((volume I).toReal / 100) * volume S ≤
      volume ((fun κ ↦ cornerInnerCoefficient a c κ u) ⁻¹' S) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hr : 0 < (volume I).toReal / 100 := by positivity
  obtain ⟨huI, hu⟩ := mem_separatedTimes.mp hu
  have hua : (volume I).toReal / 100 ≤ dist u a := hu 0 (Finset.mem_univ _)
  have huc : (volume I).toReal / 100 ≤ dist u c := hu 1 (Finset.mem_univ _)
  rw [volume_preimage_cornerInnerCoefficient
    (dist_pos.mp (hr.trans_le hua)) (dist_pos.mp (hr.trans_le huc))]
  exact mul_le_mul
    (ENNReal.ofReal_le_ofReal (corner_scalar_ratio_bounds ha hc (hIunit huI) hr hua huc).1)
    le_rfl zero_le zero_le

theorem volume_cornerTimeRelation_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    ENNReal.ofReal (δ * (volume I).toReal ^ 4 / 80000) ≤
      volume (cornerTimeRelation I a b c δ) := by
  have hP := volume_dualReservoir_lower hI hIunit hIpos hb ha hδ
    (by simpa only [dist_comm] using hab)
  have hA := half_volume_le_separatedTimes_pair (I := I) a c
  have hmass : ENNReal.ofReal ((volume I).toReal / 100) * volume (dualReservoir I b a δ) *
      volume (separatedTimes I ![a, c] Finset.univ ((volume I).toReal / 100)) ≤
        volume (cornerTimeRelation I a b c δ) := by
    rw [volume_cornerTimeRelation hI, ← setLIntegral_const]
    exact setLIntegral_mono' (measurableSet_separatedTimes hI _ _ _) fun u hu ↦
      volume_corner_scalar_preimage_lower hIunit hIpos ha hc hu _
  refine le_trans ?_ hmass
  calc
    _ = ENNReal.ofReal ((volume I).toReal / 100) *
        ENNReal.ofReal (δ * (volume I).toReal ^ 2 / 400) *
        ENNReal.ofReal ((volume I).toReal / 2) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul le_rfl hP zero_le zero_le) hA zero_le zero_le

end NKBesicovitch.Projection.Selection
