/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Good times with uniformly small spatial slices

Removing times whose spatial slice is larger than `2|E|/r` costs at most
`r/2` of time measure. Thus a line with indicator transform at least `r`
retains at least `r/2` good times. The retained time sets vary jointly
measurably with the line, and every retained projection lies in a spatial
slice of the prescribed size.
-/

@[expose] public section

open MeasureTheory Set NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {m : ℕ}

/-- Line-intersection times at which the entire spatial slice has controlled volume. -/
noncomputable def goodTimes (E : Set (EuclideanSpace ℝ (Fin m) × ℝ)) (N : ℝ≥0∞)
    (g : Line m) : Set ℝ :=
  lineTimes E g ∩ {t | volume ((fun x ↦ (x, t)) ⁻¹' E) ≤ N}

theorem measurableSet_goodTimes_family {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) (N : ℝ≥0∞) :
    MeasurableSet {p : Line m × ℝ | p.2 ∈ goodTimes E N p.1} := by
  have hm : Measurable (fun p : Line m × ℝ ↦ volume ((fun x ↦ (x, p.2)) ⁻¹' E)) :=
    (measurable_measure_prodMk_right hE).comp measurable_snd
  simpa only [goodTimes, mem_inter_iff, mem_ofPred_eq, ofPred_and] using
    (measurableSet_lineTimes_family hE).inter (measurableSet_le hm measurable_const)

theorem measurableSet_goodTimes {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) (N : ℝ≥0∞) (g : Line m) : MeasurableSet (goodTimes E N g) :=
  (measurableSet_goodTimes_family hE N).preimage (f := fun t ↦ (g, t)) (by fun_prop)

theorem goodTimes_subset_unit (E : Set (EuclideanSpace ℝ (Fin m) × ℝ)) (N : ℝ≥0∞)
    (g : Line m) : goodTimes E N g ⊆ Icc 0 1 :=
  inter_subset_left.trans inter_subset_left

theorem goodTimes_spec {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)} {N : ℝ≥0∞}
    {g : Line m} {t : ℝ} (ht : t ∈ goodTimes E N g) :
    (atHeight t g, t) ∈ E ∧ volume ((fun x ↦ (x, t)) ⁻¹' E) ≤ N :=
  ⟨ht.1.2, ht.2⟩

theorem volume_large_slices_le {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) {N : ℝ≥0∞} (hN : N ≠ 0) (hNfin : N ≠ ∞) :
    volume {t : ℝ | N < volume ((fun x ↦ (x, t)) ⁻¹' E)} ≤ volume E / N := by
  have hm : Measurable (fun t : ℝ ↦ volume ((fun x ↦ (x, t)) ⁻¹' E)) :=
    measurable_measure_prodMk_right hE
  have h := meas_ge_le_lintegral_div (μ := volume) hm.aemeasurable hN hNfin
  have hmass : (∫⁻ t, volume ((fun x ↦ (x, t)) ⁻¹' E)) = volume E := by
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hE]
  rw [hmass] at h
  apply le_trans _ h
  apply measure_mono
  intro t ht
  exact mem_ofPred_eq.mpr (mem_ofPred_eq.mp ht).le

theorem localXRay_indicator_le_goodTimes_add_largeSlices
    {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)} (hE : MeasurableSet E) (N : ℝ≥0∞) (g : Line m) :
    localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1 ≤
      volume (goodTimes E N g) + volume {t : ℝ | N < volume ((fun x ↦ (x, t)) ⁻¹' E)} := by
  rw [localXRay_indicator_eq_volume_lineTimes hE]
  have hsubset : lineTimes E g ⊆ goodTimes E N g ∪
      {t | N < volume ((fun x ↦ (x, t)) ⁻¹' E)} := by
    intro t ht
    by_cases h : volume ((fun x ↦ (x, t)) ⁻¹' E) ≤ N
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr (lt_of_not_ge h)
  exact (measure_mono hsubset).trans (measure_union_le _ _)

theorem localXRay_indicator_le_goodTimes_add {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) {N : ℝ≥0∞} (hN : N ≠ 0) (hNfin : N ≠ ∞) (g : Line m) :
    localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1 ≤
      volume (goodTimes E N g) + volume E / N :=
  (localXRay_indicator_le_goodTimes_add_largeSlices hE N g).trans
    (add_le_add_right (volume_large_slices_le hE hN hNfin) _)

private theorem half_le_volume_goodTimes_of_pos {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) (hEpos : 0 < volume E) (hEfin : volume E ≠ ∞)
    {r : ℝ} (hr : 0 < r) {g : Line m}
    (hg : ENNReal.ofReal r ≤ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1) :
    ENNReal.ofReal (r / 2) ≤
      volume (goodTimes E (ENNReal.ofReal (2 * (volume E).toReal / r)) g) := by
  have hEreal := ENNReal.toReal_pos hEpos.ne' hEfin
  have hN : 0 < 2 * (volume E).toReal / r := by positivity
  have h := hg.trans (localXRay_indicator_le_goodTimes_add hE
    (ENNReal.ofReal_pos.mpr hN).ne' ENNReal.ofReal_ne_top g)
  have hratio : volume E / ENNReal.ofReal (2 * (volume E).toReal / r) = ENNReal.ofReal (r / 2) := by
    conv_lhs => arg 1; rw [← ENNReal.ofReal_toReal hEfin]
    rw [← ENNReal.ofReal_div_of_pos hN]
    congr 1
    field_simp
  rw [hratio] at h
  have hrhalf : ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) = ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top (hrhalf.trans_le h)

theorem volume_goodTimes_of_volume_zero {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) (hzero : volume E = 0) (g : Line m) :
    volume (goodTimes E 0 g) = volume (lineTimes E g) := by
  have hm : Measurable (fun t : ℝ ↦ volume ((fun x ↦ (x, t)) ⁻¹' E)) :=
    measurable_measure_prodMk_right hE
  have hmass : (∫⁻ t, volume ((fun x ↦ (x, t)) ⁻¹' E)) = 0 := by
    rw [← Measure.prod_apply_symm hE, ← Measure.volume_eq_prod, hzero]
  have hae := (lintegral_eq_zero_iff hm).mp hmass
  apply measure_congr
  filter_upwards [hae] with t ht
  change (t ∈ goodTimes E 0 g) = (t ∈ lineTimes E g)
  simp only [goodTimes, mem_inter_iff, mem_ofPred_eq, ht, Pi.zero_apply, le_refl, and_true]

/-- Every rich line retains half its time measure, also for ambient sets of volume zero. -/
theorem half_le_volume_goodTimes {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) (hEfin : volume E ≠ ∞) {r : ℝ} (hr : 0 < r) {g : Line m}
    (hg : ENNReal.ofReal r ≤ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1) :
    ENNReal.ofReal (r / 2) ≤
      volume (goodTimes E (ENNReal.ofReal (2 * (volume E).toReal / r)) g) := by
  by_cases hzero : volume E = 0
  · simp only [hzero, ENNReal.toReal_zero, mul_zero, zero_div, ENNReal.ofReal_zero]
    rw [volume_goodTimes_of_volume_zero hE hzero,
      ← localXRay_indicator_eq_volume_lineTimes hE]
    exact (ENNReal.ofReal_le_ofReal (by linarith : r / 2 ≤ r)).trans hg
  · exact half_le_volume_goodTimes_of_pos hE (pos_iff_ne_zero.mpr hzero) hEfin hr hg

end NKBesicovitch.XRay
