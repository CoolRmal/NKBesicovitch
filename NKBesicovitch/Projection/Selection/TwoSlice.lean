/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.SeparatedPairs
public import NKBesicovitch.Projection.Estimates

/-!
# Quantitative selection of the two-slice seed

Select pairs in `I²` separated by at least `|I|/100`. Their parameter measure
is at least `|I|²/2`, and each pair has two-slice estimate constant at most
`(100/|I|)^m`. For a time set inside `[0,1]`, all parameters remain in the
unit square. The same explicit selection is jointly Borel for measurable
families of time sets.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Parameters for the two-slice seed, with separation set by the time-set measure. -/
noncomputable def twoSliceParameters (I : Set ℝ) : Set (ℝ × ℝ) :=
  separatedPairs I ((volume I).toReal / 100)

theorem measurableSet_twoSliceParameters_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) :
    MeasurableSet {p : X × (ℝ × ℝ) | p.2 ∈ twoSliceParameters {t | (p.1, t) ∈ I}} :=
  measurableSet_separatedPairs_family hI
    ((measurable_measure_prodMk_left (ν := volume) hI).ennreal_toReal.div_const 100)

theorem twoSliceParameters_ne {I : Set ℝ} (hIpos : 0 < volume I) (hIfin : volume I ≠ ∞)
    {p : ℝ × ℝ} (hp : p ∈ twoSliceParameters I) : p.1 ≠ p.2 := by
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hsep : (volume I).toReal / 100 ≤ dist p.1 p.2 := hp.2
  intro he
  rw [he, dist_self] at hsep
  linarith

theorem volume_le_of_mem_twoSliceParameters {m : ℕ} {I : Set ℝ}
    (hIpos : 0 < volume I) (hIfin : volume I ≠ ∞) {p : ℝ × ℝ}
    (hp : p ∈ twoSliceParameters I) {G : Set (Line m)} (hGb : IsBounded G) :
    (volume G).toReal ≤ (100 / (volume I).toReal) ^ m *
      (sliceSize {p.1, p.2} G).toReal ^ 2 := by
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hsep : (volume I).toReal / 100 ≤ |p.2 - p.1| := by
    simpa only [mem_ofPred_eq, Real.dist_eq, abs_sub_comm] using hp.2
  have hinv := inv_anti₀ (by positivity : 0 < (volume I).toReal / 100) hsep
  have hcoef : |((p.2 - p.1) ^ m)⁻¹| ≤ (100 / (volume I).toReal) ^ m := by
    simpa only [abs_inv, abs_pow, inv_pow, inv_div] using
      pow_le_pow_left₀ (inv_nonneg.mpr (abs_nonneg (p.2 - p.1))) hinv m
  have hfin : ENNReal.ofReal |((p.2 - p.1) ^ m)⁻¹| *
      (volume (atHeight p.1 '' G) * volume (atHeight p.2 '' G)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
      (volume_projection_ne_top _ hGb) (volume_projection_ne_top _ hGb))
  have h := ENNReal.toReal_mono hfin (volume_le_two_slice (twoSliceParameters_ne hIpos hIfin hp) G)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at h
  have hprod := mul_le_mul
    (projection_toReal_le_sliceSize (show p.1 ∈ ({p.1, p.2} : Finset ℝ) by simp) hGb)
    (projection_toReal_le_sliceSize (show p.2 ∈ ({p.1, p.2} : Finset ℝ) by simp) hGb)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  simpa only [pow_two] using h.trans
    (mul_le_mul hcoef hprod (by positivity) (by positivity))

/-- The selectable two-slice seed, with an explicit parameter-volume and estimate constant. -/
theorem twoSliceParameters_spec {m : ℕ} {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) :
    MeasurableSet (twoSliceParameters I) ∧
      twoSliceParameters I ⊆ I ×ˢ I ∧
      twoSliceParameters I ⊆ (Icc 0 1) ×ˢ (Icc 0 1) ∧
      ENNReal.ofReal ((volume I).toReal ^ 2 / 2) ≤ volume (twoSliceParameters I) ∧
      ∀ p ∈ twoSliceParameters I, p.1 ≠ p.2 ∧
        ∀ G : Set (Line m), IsBounded G →
          (volume G).toReal ≤ (100 / (volume I).toReal) ^ m *
            (sliceSize {p.1, p.2} G).toReal ^ 2 := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  refine ⟨measurableSet_separatedPairs hI _, inter_subset_left,
    inter_subset_left.trans (Set.prod_mono hIunit hIunit),
    half_square_le_volume_separatedPairs hI hIfin, fun p hp ↦ ?_⟩
  exact ⟨twoSliceParameters_ne hIpos hIfin hp, fun _ hGb ↦ volume_le_of_mem_twoSliceParameters
    hIpos hIfin hp hGb⟩

end NKBesicovitch.Projection.Selection
