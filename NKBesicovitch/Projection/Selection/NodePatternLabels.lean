/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.NodePattern

/-!
# Matching analytic children with labeled child triples

Every child of the selected analytic pattern comes from an outer and an
inner label. Its numerical triple agrees with the measurable labeled
child-triple map. All heights of the analytic pattern belong to the
original time set.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

/-- The base triple of the child carrying the specified outer and inner labels. -/
noncomputable def nodeChildTriple (a b c : ℝ)
    (p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))) (ij : Fin L × Fin L) : (ℝ × ℝ) × ℝ :=
  ((b, S.time (p.2.2 ij.1) ij.2),
    dualTime b a (cornerInnerCoefficient a c p.1 (S.time p.2.1 ij.1)) (S.time (p.2.2 ij.1) ij.2))

theorem measurable_nodeChildTriple {X : Type*} [MeasurableSpace X] {a b c : X → ℝ}
    {p : X → ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hp : Measurable p)
    (ij : Fin L × Fin L) :
    Measurable (fun x ↦ S.nodeChildTriple (a x) (b x) (c x) (p x) ij) := by
  have hu := (S.measurable_time ij.1).comp hp.snd.fst
  have ht := (S.measurable_time ij.2).comp ((measurable_pi_apply ij.1).comp hp.snd.snd)
  exact (hb.prodMk ht).prodMk
    (measurable_dualTime hb ha (measurable_cornerInnerCoefficient ha hc hp.fst hu) ht)

/-- Representative labels for a numerical child pair. -/
noncomputable def nodeChildLabels
    (p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))) (q : ℝ × ℝ) : Fin L × Fin L :=
  (S.labelIndex p.2.1 q.1, S.labelIndex (p.2.2 (S.labelIndex p.2.1 q.1)) q.2)

theorem nodeChildLabels_spec {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b c : ℝ}
    (hbase : ((a, b), c) ∈ separatedTriples I ((volume I).toReal / 100))
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c ((volume I).toReal / 100)) {q : ℝ × ℝ}
    (hq : q ∈ (S.nodePattern hI hIunit hIpos hbase hp).children) :
    S.time p.2.1 (S.nodeChildLabels p q).1 = q.1 ∧
      S.time (p.2.2 (S.nodeChildLabels p q).1) (S.nodeChildLabels p q).2 = q.2 := by
  obtain ⟨hu, ht⟩ := CornerPattern.mem_children.mp hq
  exact ⟨S.time_labelIndex hu, S.time_labelIndex ht⟩

theorem nodeChildTriple_nodeChildLabels {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c : ℝ}
    (hbase : ((a, b), c) ∈ separatedTriples I ((volume I).toReal / 100))
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c ((volume I).toReal / 100)) {q : ℝ × ℝ}
    (hq : q ∈ (S.nodePattern hI hIunit hIpos hbase hp).children) :
    S.nodeChildTriple a b c p (S.nodeChildLabels p q) =
      ((b, q.2), dualTime b a (cornerInnerCoefficient a c p.1 q.1) q.2) := by
  obtain ⟨hu, ht⟩ := S.nodeChildLabels_spec hI hIunit hIpos hbase hp hq
  simp only [nodeChildTriple, hu, ht]

theorem nodePattern_times_subset {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b c : ℝ}
    (hbase : ((a, b), c) ∈ separatedTriples I ((volume I).toReal / 100))
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c ((volume I).toReal / 100)) :
    ∀ t ∈ (S.nodePattern hI hIunit hIpos hbase hp).times, t ∈ I := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hr : 0 < (volume I).toReal / 100 := by positivity
  obtain ⟨ha, hb, hc, _, _, _⟩ := mem_separatedTriples.mp hbase
  apply CornerPattern.times_subset _ ha hb hc
  · intro u hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    exact (cornerOuterTimes_spec
      (S.cornerNodeParameters_outer_time_mem hI hIunit hIpos hr hp i)).1
  · intro u hu t ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    exact (dualTimes_spec (S.cornerNodeParameters_inner_time_mem hI hIunit hIpos hr hp _ j)).2.1
  · intro u hu t ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    have h := S.cornerNodeParameters_inner_time_mem hI hIunit hIpos hr hp (S.labelIndex p.2.1 u) j
    rw [S.time_labelIndex hu] at h
    exact (dualTimes_spec h).2.2.1

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
