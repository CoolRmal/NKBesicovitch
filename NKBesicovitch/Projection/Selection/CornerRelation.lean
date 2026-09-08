/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.CornerScalar

/-!
# Outer times compatible with one corner scalar

The relation consists of separated outer times and scalars whose derived
inner coefficient belongs to the dual reservoir for the base pair `(b,a)`.
It is jointly Borel, and every admissible outer scalar has polynomial
upper and lower bounds in terms of the input time-set measure.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Compatible pairs of an outer time and a common corner scalar. -/
noncomputable def cornerTimeRelation (I : Set ℝ) (a b c δ : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ separatedTimes I ![a, c] Finset.univ ((volume I).toReal / 100) ∧
    cornerInnerCoefficient a c p.2 p.1 ∈ dualReservoir I b a δ}

theorem measurableSet_cornerTimeRelation {I : Set ℝ} (hI : MeasurableSet I) (a b c δ : ℝ) :
    MeasurableSet (cornerTimeRelation I a b c δ) :=
  ((measurableSet_separatedTimes hI _ _ _).preimage measurable_fst).inter
    ((measurableSet_dualReservoir hI b a δ).preimage
      (measurable_cornerInnerCoefficient measurable_const measurable_const
        measurable_snd measurable_fst))

theorem measurableSet_cornerTimeRelation_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b c δ : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hδ : Measurable δ) :
    MeasurableSet {p : X × (ℝ × ℝ) | p.2 ∈ cornerTimeRelation {t | (p.1, t) ∈ I}
      (a p.1) (b p.1) (c p.1) (δ p.1)} := by
  have hr := (measurable_measure_prodMk_left (ν := volume) hI).ennreal_toReal.div_const 100
  have hbase (i : Fin 2) : Measurable (fun x ↦ ![a x, c x] i) := by
    fin_cases i
    · exact ha
    · exact hc
  exact ((measurableSet_separatedTimes_family hI Finset.univ (fun i _ ↦ hbase i) hr).preimage
    (f := fun p : X × (ℝ × ℝ) ↦ (p.1, p.2.1))
    (measurable_fst.prodMk measurable_snd.fst)).inter
      ((measurableSet_dualReservoir_family hI hb ha hδ).preimage
        (f := fun p : X × (ℝ × ℝ) ↦
          (p.1, cornerInnerCoefficient (a p.1) (c p.1) p.2.2 p.2.1))
        (measurable_fst.prodMk (measurable_cornerInnerCoefficient (ha.comp measurable_fst)
          (hc.comp measurable_fst) measurable_snd.snd measurable_snd.fst)))

theorem cornerTimeRelation_spec {I : Set ℝ} {a b c δ : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ cornerTimeRelation I a b c δ) :
    p.1 ∈ I ∧ (volume I).toReal / 100 ≤ dist p.1 a ∧
      (volume I).toReal / 100 ≤ dist p.1 c ∧
      cornerInnerCoefficient a c p.2 p.1 ∈ dualReservoir I b a δ := by
  have hu := mem_separatedTimes.mp hp.1
  exact ⟨hu.1, hu.2 0 (Finset.mem_univ _), hu.2 1 (Finset.mem_univ _), hp.2⟩

theorem cornerTimeRelation_section {I : Set ℝ} {a b c δ u : ℝ}
    (hu : u ∈ separatedTimes I ![a, c] Finset.univ ((volume I).toReal / 100)) :
    Prod.mk u ⁻¹' cornerTimeRelation I a b c δ =
      (fun κ ↦ cornerInnerCoefficient a c κ u) ⁻¹' dualReservoir I b a δ := by
  ext κ
  simp only [cornerTimeRelation, mem_preimage, mem_ofPred_eq, hu, true_and]

theorem cornerTimeRelation_scalar_bounds {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b c δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hc : c ∈ Icc 0 1) (hδ : 0 < δ) (hab : δ ≤ dist a b) {p : ℝ × ℝ}
    (hp : p ∈ cornerTimeRelation I a b c δ) :
    p.2 ≠ 0 ∧ δ * ((volume I).toReal / 100) ^ 2 ≤ |p.2| ∧
      |p.2| ≤ (100 / (volume I).toReal) ^ 3 := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hr : 0 < (volume I).toReal / 100 := by positivity
  obtain ⟨hu, hua, huc, hs⟩ := cornerTimeRelation_spec hp
  have hsbound := dualReservoir_scalar_bounds hIunit hIpos hb ha hδ
    (by simpa only [dist_comm] using hab) hs
  have hratio := corner_scalar_ratio_bounds ha hc (hIunit hu) hr hua huc
  have he : |p.2| = |cornerInnerCoefficient a c p.2 p.1| * |(p.1 - a) / (p.1 - c)| := by
    conv_lhs => rw [← cornerInnerCoefficient_swap
      (dist_pos.mp (hr.trans_le hua)) (dist_pos.mp (hr.trans_le huc)) p.2]
    simp only [cornerInnerCoefficient, abs_div, abs_mul, mul_div_assoc]
  refine ⟨?_, ?_, ?_⟩
  · intro hκ
    apply hsbound.1
    simp [cornerInnerCoefficient, hκ]
  · rw [he]
    simpa only [pow_two, mul_assoc] using mul_le_mul hsbound.2.1 hratio.1 hr.le (abs_nonneg _)
  · rw [he]
    simpa only [inv_div, pow_succ] using
      mul_le_mul hsbound.2.2 hratio.2 (abs_nonneg _) (by positivity)

end NKBesicovitch.Projection.Selection
