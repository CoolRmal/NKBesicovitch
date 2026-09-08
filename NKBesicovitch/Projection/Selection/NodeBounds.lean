/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.NodeGeometry
public import NKBesicovitch.Projection.Selection.SchemeBounds

/-!
# Uniform input bounds at a selected corner node

The outer and inner time reservoirs have fixed polynomial measure lower
bounds. Substituting them into the input scheme gives uniform bounds on
all scheme coordinates and on both kinds of input projection constants.
These estimates are independent of the selected scalar and label values.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

theorem cornerNodeParameters_outer_coordinates_bound {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ} (hδ : 0 < δ)
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c δ) (j : Fin D) :
    |p.2.1 j| ≤ S.upperConstant *
      ((δ * (volume I).toReal ^ 7 / 320000000000)⁻¹) ^ S.boundExponent := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  exact S.coordinates_bound_of_measure_lower (measurableSet_cornerOuterTimes hI _ _ _ _ _)
    ((cornerOuterTimes_subset I _ _ _ _ _).trans hIunit) (by positivity) hp.1 hp.2.1 j

theorem cornerNodeParameters_inner_coordinates_bound {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ} (hδ : 0 < δ)
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c δ) (i : Fin L) (j : Fin D) :
    |p.2.2 i j| ≤ S.upperConstant *
      ((δ * (volume I).toReal ^ 5 / 8000000)⁻¹) ^ S.boundExponent := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hu := S.cornerNodeParameters_outer_time_mem hI hIunit hIpos hδ hp i
  exact S.coordinates_bound_of_measure_lower (measurableSet_dualTimes hI _ _ _)
    ((dualTimes_subset I _ _ _).trans hIunit) (by positivity)
    (cornerOuterTimes_spec hu).2.2.2 (hp.2.2 i) j

theorem cornerNodeParameters_outer_estimate {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ} (hδ : 0 < δ)
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c δ) {G : Set (Line m)}
    (hG : MeasurableSet G) (hGb : IsBounded G) :
    (volume G).toReal ≤
      (S.upperConstant * ((δ * (volume I).toReal ^ 7 / 320000000000)⁻¹) ^ S.boundExponent) *
      (parallelMultiplicity G).toReal ^ (2 - β) *
      (sliceSize (Finset.univ.image (S.time p.2.1)) G).toReal ^ β := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  exact S.estimate_of_measure_lower (measurableSet_cornerOuterTimes hI _ _ _ _ _)
    ((cornerOuterTimes_subset I _ _ _ _ _).trans hIunit) (by positivity) hp.1 hp.2.1 hG hGb

theorem cornerNodeParameters_inner_estimate {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ} (hδ : 0 < δ)
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c δ) (i : Fin L) {G : Set (Line m)}
    (hG : MeasurableSet G) (hGb : IsBounded G) :
    (volume G).toReal ≤
      (S.upperConstant * ((δ * (volume I).toReal ^ 5 / 8000000)⁻¹) ^ S.boundExponent) *
      (parallelMultiplicity G).toReal ^ (2 - β) *
      (sliceSize (Finset.univ.image (S.time (p.2.2 i))) G).toReal ^ β := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hu := S.cornerNodeParameters_outer_time_mem hI hIunit hIpos hδ hp i
  exact S.estimate_of_measure_lower (measurableSet_dualTimes hI _ _ _)
    ((dualTimes_subset I _ _ _).trans hIunit) (by positivity)
    (cornerOuterTimes_spec hu).2.2.2 (hp.2.2 i) hG hGb

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
