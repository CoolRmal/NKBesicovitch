/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.DualRelation
public import NKBesicovitch.Projection.Selection.SeparatedTriples

/-!
# Admissible times for each dual scalar

The time fiber of the dual relation is a Borel subset of the input time
set. Its measure varies measurably, including in measurable families of
time sets and base heights. Integrating these fiber measures recovers
the measure of the relation by Tonelli's theorem.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Times whose dual partner satisfies all five separation conditions. -/
noncomputable def dualTimes (I : Set ℝ) (a b c : ℝ) : Set ℝ :=
  {t | (t, c) ∈ dualTimeRelation I a b}

theorem dualTimes_spec {I : Set ℝ} {a b c t : ℝ} (ht : t ∈ dualTimes I a b c) :
    c ≠ 0 ∧ t ∈ I ∧ dualTime a b c t ∈ I ∧
      (volume I).toReal / 100 ≤ dist t a ∧ (volume I).toReal / 100 ≤ dist t b ∧
      (volume I).toReal / 100 ≤ dist (dualTime a b c t) a ∧
      (volume I).toReal / 100 ≤ dist (dualTime a b c t) b ∧
      (volume I).toReal / 100 ≤ dist t (dualTime a b c t) :=
  ⟨ht.1, dualPairParameters_spec ht.2⟩

theorem dualTimes_subset (I : Set ℝ) (a b c : ℝ) : dualTimes I a b c ⊆ I :=
  fun _ ht ↦ (dualPairParameters_spec ht.2).1

/-- The base, inner time, and its dual form an admissible triple for the next corner node. -/
theorem dualTimes_mem_separatedTriples {I : Set ℝ} {a b c t : ℝ} (ha : a ∈ I)
    (ht : t ∈ dualTimes I a b c) :
    ((a, t), dualTime a b c t) ∈ separatedTriples I ((volume I).toReal / 100) := by
  obtain ⟨_, htI, hdualI, hta, _, hdual_a, _, htdual⟩ := dualTimes_spec ht
  exact mem_separatedTriples.mpr ⟨ha, htI, hdualI,
    by simpa only [dist_comm] using hta, by simpa only [dist_comm] using hdual_a, htdual⟩

theorem measurableSet_dualTimes {I : Set ℝ} (hI : MeasurableSet I) (a b c : ℝ) :
    MeasurableSet (dualTimes I a b c) :=
  (measurableSet_dualTimeRelation hI a b).preimage (by fun_prop)

theorem measurable_volume_dualTimes {I : Set ℝ} (hI : MeasurableSet I) (a b : ℝ) :
    Measurable (fun c ↦ volume (dualTimes I a b c)) :=
  measurable_measure_prodMk_right (measurableSet_dualTimeRelation hI a b)

theorem measurableSet_dualTimes_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    MeasurableSet {p : (X × ℝ) × ℝ |
      p.2 ∈ dualTimes {t | (p.1.1, t) ∈ I} (a p.1.1) (b p.1.1) p.1.2} := by
  change MeasurableSet ((fun p : (X × ℝ) × ℝ ↦ (p.1.1, (p.2, p.1.2))) ⁻¹'
    {q : X × (ℝ × ℝ) | q.2 ∈ dualTimeRelation {t | (q.1, t) ∈ I} (a q.1) (b q.1)})
  exact (measurableSet_dualTimeRelation_family hI ha hb).preimage
    (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))

theorem measurable_volume_dualTimes_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p : X × ℝ ↦
      volume (dualTimes {t | (p.1, t) ∈ I} (a p.1) (b p.1) p.2)) :=
  measurable_measure_prodMk_left (measurableSet_dualTimes_family hI ha hb)

theorem lintegral_volume_dualTimes {I : Set ℝ} (hI : MeasurableSet I) (a b : ℝ) :
    ∫⁻ c, volume (dualTimes I a b c) = volume (dualTimeRelation I a b) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_dualTimeRelation hI a b)]
  rfl

theorem support_volume_dualTimes_subset {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    Function.support (fun c ↦ volume (dualTimes I a b c)) ⊆
      Icc (-((100 / (volume I).toReal) ^ 2)) ((100 / (volume I).toReal) ^ 2) := by
  intro c hc
  obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero hc
  exact (dualTimeRelation_subset hIunit hIpos ha hb hδ hab ht).2

end NKBesicovitch.Projection.Selection
