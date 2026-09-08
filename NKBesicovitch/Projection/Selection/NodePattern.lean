/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.NodeBounds
public import NKBesicovitch.Projection.CornerPattern

/-!
# An admissible corner pattern from selected labels

Choose one representative label for each numerical outer time. Its inner
scheme supplies the inner height set of the analytic corner pattern.
Every child of that pattern is represented by an outer and inner label.
The representative choice is used only for this finite analytic pattern;
the parameter selections and labeled time maps keep their Borel definitions.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

/-- A representative label for a numerical height, with a default for heights outside the image. -/
noncomputable def labelIndex (σ : Fin D → ℝ) (t : ℝ) : Fin L :=
  if h : ∃ i, S.time σ i = t then h.choose else ⟨0, S.label_pos⟩

theorem time_labelIndex {σ : Fin D → ℝ} {t : ℝ}
    (ht : t ∈ Finset.univ.image (S.time σ)) : S.time σ (S.labelIndex σ t) = t := by
  have h : ∃ i, S.time σ i = t := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
    exact ⟨i, hi⟩
  simp only [labelIndex, dite_eq_left h]
  exact h.choose_spec

theorem node_outer_ne {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b c δ : ℝ} (hδ : 0 < δ)
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c δ) {u : ℝ}
    (hu : u ∈ Finset.univ.image (S.time p.2.1)) : u ≠ a ∧ u ≠ c := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hr : 0 < (volume I).toReal / 100 := by positivity
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
  have ht := cornerOuterTimes_spec (S.cornerNodeParameters_outer_time_mem hI hIunit hIpos hδ hp i)
  exact ⟨dist_pos.mp (hr.trans_le ht.2.1), dist_pos.mp (hr.trans_le ht.2.2.1)⟩

theorem node_inner_ne {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b c δ : ℝ} (hδ : 0 < δ)
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c δ) {u t : ℝ}
    (hu : u ∈ Finset.univ.image (S.time p.2.1))
    (ht : t ∈ Finset.univ.image (S.time (p.2.2 (S.labelIndex p.2.1 u)))) :
    t ≠ b ∧ t ≠ a ∧ dualTime b a (cornerInnerCoefficient a c p.1 u) t ≠ t := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
  have h := S.cornerNodeParameters_inner_time_mem hI hIunit hIpos hδ hp (S.labelIndex p.2.1 u) j
  rw [S.time_labelIndex hu] at h
  have hne := dualPairParameters_ne hIpos hIfin h.2
  exact ⟨hne.1, hne.2.1, hne.2.2.2.2.symm⟩

theorem node_outer_hasProjectionEstimate {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ} (hδ : 0 < δ)
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c δ) :
    HasProjectionEstimate m β (Finset.univ.image (S.time p.2.1)) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hC := zero_lt_one.trans_le S.one_le_upperConstant
  exact ⟨S.upperConstant * ((δ * (volume I).toReal ^ 7 / 320000000000)⁻¹) ^ S.boundExponent,
    by positivity, fun G hG hGb ↦
      S.cornerNodeParameters_outer_estimate hI hIunit hIpos hδ hp hG hGb⟩

theorem node_inner_hasProjectionEstimate {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ} (hδ : 0 < δ)
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c δ) (i : Fin L) :
    HasProjectionEstimate m β (Finset.univ.image (S.time (p.2.2 i))) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hC := zero_lt_one.trans_le S.one_le_upperConstant
  exact ⟨S.upperConstant * ((δ * (volume I).toReal ^ 5 / 8000000)⁻¹) ^ S.boundExponent,
    by positivity, fun G hG hGb ↦
      S.cornerNodeParameters_inner_estimate hI hIunit hIpos hδ hp i hG hGb⟩

/-- The analytic corner pattern carried by a selected node parameter. -/
noncomputable def nodePattern {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b c : ℝ}
    (hbase : ((a, b), c) ∈ separatedTriples I ((volume I).toReal / 100))
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c ((volume I).toReal / 100)) : CornerPattern m β := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hr : 0 < (volume I).toReal / 100 := by positivity
  have hbase' := mem_separatedTriples.mp hbase
  exact {
    a := a, b := b, c := c, κ := p.1
    a_ne_b := dist_pos.mp (hr.trans_le hbase'.2.2.2.1)
    c_ne_a := (dist_pos.mp (hr.trans_le hbase'.2.2.2.2.1)).symm
    c_ne_b := (dist_pos.mp (hr.trans_le hbase'.2.2.2.2.2)).symm
    κ_ne_zero := (cornerReservoir_scalar_bounds hIunit hIpos
      (hIunit hbase'.1) (hIunit hbase'.2.1) (hIunit hbase'.2.2.1)
      hr hbase'.2.2.2.1 hp.1).1
    outer := Finset.univ.image (S.time p.2.1)
    outer_nonempty := S.times_nonempty _
    inner := fun u ↦ Finset.univ.image (S.time (p.2.2 (S.labelIndex p.2.1 u)))
    inner_nonempty := fun _ _ ↦ S.times_nonempty _
    outer_ne_a := fun _ hu ↦ (S.node_outer_ne hI hIunit hIpos hr hp hu).1
    outer_ne_c := fun _ hu ↦ (S.node_outer_ne hI hIunit hIpos hr hp hu).2
    inner_ne_b := fun _ hu _ ht ↦ (S.node_inner_ne hI hIunit hIpos hr hp hu ht).1
    inner_ne_a := fun _ hu _ ht ↦ (S.node_inner_ne hI hIunit hIpos hr hp hu ht).2.1
    dual_ne_inner := fun _ hu _ ht ↦ (S.node_inner_ne hI hIunit hIpos hr hp hu ht).2.2
    outer_estimate := S.node_outer_hasProjectionEstimate hI hIunit hIpos hr hp
    inner_estimate := fun u _ ↦ S.node_inner_hasProjectionEstimate hI hIunit hIpos hr hp
      (S.labelIndex p.2.1 u)
  }

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
