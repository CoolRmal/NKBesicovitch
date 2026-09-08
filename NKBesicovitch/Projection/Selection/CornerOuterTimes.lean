/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.CornerRelationMass

/-!
# Outer time fibers for a common corner scalar

Every time in an outer fiber is separated from the two required base
heights and gives an inner coefficient in the dual reservoir. The outer
fibers and their measures are jointly measurable, and Tonelli identifies
their total mass with the compatible time-scalar relation.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Separated outer times compatible with the fixed corner scalar. -/
noncomputable def cornerOuterTimes (I : Set ℝ) (a b c δ κ : ℝ) : Set ℝ :=
  {u | (u, κ) ∈ cornerTimeRelation I a b c δ}

theorem cornerOuterTimes_spec {I : Set ℝ} {a b c δ κ u : ℝ}
    (hu : u ∈ cornerOuterTimes I a b c δ κ) :
    u ∈ I ∧ (volume I).toReal / 100 ≤ dist u a ∧ (volume I).toReal / 100 ≤ dist u c ∧
      cornerInnerCoefficient a c κ u ∈ dualReservoir I b a δ :=
  cornerTimeRelation_spec hu

theorem cornerOuterTimes_subset (I : Set ℝ) (a b c δ κ : ℝ) :
    cornerOuterTimes I a b c δ κ ⊆ I := fun _ hu ↦ (cornerOuterTimes_spec hu).1

theorem measurableSet_cornerOuterTimes {I : Set ℝ} (hI : MeasurableSet I) (a b c δ κ : ℝ) :
    MeasurableSet (cornerOuterTimes I a b c δ κ) :=
  (measurableSet_cornerTimeRelation hI a b c δ).preimage
    (f := fun u : ℝ ↦ (u, κ)) (by fun_prop)

theorem measurable_volume_cornerOuterTimes {I : Set ℝ} (hI : MeasurableSet I) (a b c δ : ℝ) :
    Measurable (fun κ ↦ volume (cornerOuterTimes I a b c δ κ)) :=
  measurable_measure_prodMk_right (measurableSet_cornerTimeRelation hI a b c δ)

theorem measurableSet_cornerOuterTimes_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b c δ : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hδ : Measurable δ) :
    MeasurableSet {p : (X × ℝ) × ℝ | p.2 ∈ cornerOuterTimes {t | (p.1.1, t) ∈ I}
      (a p.1.1) (b p.1.1) (c p.1.1) (δ p.1.1) p.1.2} :=
  (measurableSet_cornerTimeRelation_family hI ha hb hc hδ).preimage
    (f := fun p : (X × ℝ) × ℝ ↦ (p.1.1, (p.2, p.1.2)))
    (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))

theorem measurable_volume_cornerOuterTimes_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b c δ : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hδ : Measurable δ) :
    Measurable (fun p : X × ℝ ↦ volume (cornerOuterTimes {t | (p.1, t) ∈ I}
      (a p.1) (b p.1) (c p.1) (δ p.1) p.2)) :=
  measurable_measure_prodMk_left (measurableSet_cornerOuterTimes_family hI ha hb hc hδ)

theorem lintegral_volume_cornerOuterTimes {I : Set ℝ} (hI : MeasurableSet I) (a b c δ : ℝ) :
    ∫⁻ κ, volume (cornerOuterTimes I a b c δ κ) = volume (cornerTimeRelation I a b c δ) := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply_symm (measurableSet_cornerTimeRelation hI a b c δ)]
  rfl

theorem support_volume_cornerOuterTimes_subset {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b c δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hc : c ∈ Icc 0 1) (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    Function.support (fun κ ↦ volume (cornerOuterTimes I a b c δ κ)) ⊆
      Icc (-((100 / (volume I).toReal) ^ 3)) ((100 / (volume I).toReal) ^ 3) := by
  intro κ hκ
  obtain ⟨u, hu⟩ := nonempty_of_measure_ne_zero hκ
  exact abs_le.mp (cornerTimeRelation_scalar_bounds hIunit hIpos ha hb hc hδ hab hu).2.2

end NKBesicovitch.Projection.Selection
