/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.Scheme
public import NKBesicovitch.Projection.Selection.CornerReservoir

/-!
# Parameter selection at one corner node

A node parameter consists of one common scalar, one outer scheme parameter,
and one inner scheme parameter for every outer label. The outer scheme lies
in the compatible outer-time set, while each inner scheme lies in the dual
time reservoir determined by its outer label. Every membership condition is
jointly Borel, including when the original time set and base heights vary.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

namespace SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

/-- Parameters for one corner node, with one inner copy for each outer time label. -/
noncomputable def cornerNodeParameters (I : Set ℝ) (a b c δ : ℝ) :
    Set (ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))) :=
  {p | p.1 ∈ cornerReservoir I a b c δ ∧ p.2.1 ∈ S.select (cornerOuterTimes I a b c δ p.1) ∧
    ∀ i, p.2.2 i ∈ S.select (dualTimes I b a (cornerInnerCoefficient a c p.1 (S.time p.2.1 i)))}

theorem measurableSet_node_inner_times_family {X : Type} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b c : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (i : Fin L) :
    MeasurableSet {p : ((X × ℝ) × (Fin D → ℝ)) × ℝ |
      p.2 ∈ dualTimes {t | (p.1.1.1, t) ∈ I} (b p.1.1.1) (a p.1.1.1)
        (cornerInnerCoefficient (a p.1.1.1) (c p.1.1.1) p.1.1.2 (S.time p.1.2 i))} := by
  have htime : Measurable (fun q : (X × ℝ) × (Fin D → ℝ) ↦ S.time q.2 i) :=
    (S.measurable_time i).comp measurable_snd
  have hcoef : Measurable (fun q : (X × ℝ) × (Fin D → ℝ) ↦
      cornerInnerCoefficient (a q.1.1) (c q.1.1) q.1.2 (S.time q.2 i)) :=
    measurable_cornerInnerCoefficient (ha.comp measurable_fst.fst)
      (hc.comp measurable_fst.fst) measurable_fst.snd htime
  exact (measurableSet_dualTimes_family hI hb ha).preimage
    (f := fun p : ((X × ℝ) × (Fin D → ℝ)) × ℝ ↦
      ((p.1.1.1, cornerInnerCoefficient (a p.1.1.1) (c p.1.1.1) p.1.1.2
        (S.time p.1.2 i)), p.2))
    ((measurable_fst.fst.fst.prodMk (hcoef.comp measurable_fst)).prodMk measurable_snd)

theorem measurableSet_cornerNodeParameters_family {X : Type} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b c δ : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hδ : Measurable δ) :
    MeasurableSet {p : X × (ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))) |
      p.2 ∈ S.cornerNodeParameters {t | (p.1, t) ∈ I} (a p.1) (b p.1) (c p.1) (δ p.1)} := by
  have houter := S.measurable_select
    (fun q : X × ℝ ↦ cornerOuterTimes {t | (q.1, t) ∈ I} (a q.1) (b q.1) (c q.1) (δ q.1) q.2)
    (measurableSet_cornerOuterTimes_family hI ha hb hc hδ)
  have hinner (i : Fin L) := S.measurable_select
    (fun q : (X × ℝ) × (Fin D → ℝ) ↦ dualTimes {t | (q.1.1, t) ∈ I} (b q.1.1) (a q.1.1)
      (cornerInnerCoefficient (a q.1.1) (c q.1.1) q.1.2 (S.time q.2 i)))
    (S.measurableSet_node_inner_times_family hI ha hb hc i)
  apply MeasurableSet.inter
    ((measurableSet_cornerReservoir_family hI ha hb hc hδ).preimage
      (f := fun p : X × (ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))) ↦ (p.1, p.2.1))
      (measurable_fst.prodMk measurable_snd.fst))
  apply MeasurableSet.inter
    (houter.preimage
      (f := fun p : X × (ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))) ↦ ((p.1, p.2.1), p.2.2.1))
      ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd.fst))
  change MeasurableSet {p : X × (ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))) |
    ∀ i, p.2.2.2 i ∈ S.select (dualTimes {t | (p.1, t) ∈ I} (b p.1) (a p.1)
      (cornerInnerCoefficient (a p.1) (c p.1) p.2.1 (S.time p.2.2.1 i)))}
  have h := MeasurableSet.iInter fun i ↦ (hinner i).preimage
    (f := fun p : X × (ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))) ↦
      (((p.1, p.2.1), p.2.2.1), p.2.2.2 i))
    (((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd.fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd.snd.snd))
  simpa only [preimage_ofPred_eq, ← ofPred_forall] using h

theorem measurableSet_cornerNodeParameters {I : Set ℝ} (hI : MeasurableSet I) (a b c δ : ℝ) :
    MeasurableSet (S.cornerNodeParameters I a b c δ) := by
  have h := S.measurableSet_cornerNodeParameters_family
    (X := Unit) (I := {p : Unit × ℝ | p.2 ∈ I}) (hI.preimage measurable_snd)
    (a := fun _ ↦ a) (b := fun _ ↦ b) (c := fun _ ↦ c) (δ := fun _ ↦ δ)
    measurable_const measurable_const measurable_const measurable_const
  exact h.preimage (f := fun p ↦ ((), p)) (by fun_prop)

end SelectableProjectionScheme

end NKBesicovitch.Projection.Selection
