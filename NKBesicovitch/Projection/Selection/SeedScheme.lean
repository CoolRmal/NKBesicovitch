/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.Scheme
public import NKBesicovitch.Projection.Selection.TwoSlice
public import Mathlib.Tactic.FinCases

/-!
# The two-slice seed as a selectable projection scheme

Use two real coordinates as the two labeled heights. The selection-volume
exponent is two, with lower constant `1/2`. In positive slope dimension
`m`, the coordinate and estimate bounds use exponent `m` and upper
constant `100^m`. All finite-coordinate statements use the canonical
product Lebesgue measure.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

private theorem coordinate_mem_aux {I : Set ℝ} {σ : Fin 2 → ℝ}
    (hσ : MeasurableEquiv.finTwoArrow σ ∈ twoSliceParameters I) (i : Fin 2) : σ i ∈ I := by
  fin_cases i
  · exact hσ.1.1
  · exact hσ.1.2

private theorem one_le_seed_bound_aux {m : ℕ} {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) : 1 ≤ (100 : ℝ) ^ m * ((volume I).toReal⁻¹) ^ m := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hLle : (volume I).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono (by simp) (measure_mono (μ := volume) hIunit)
    simpa only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one] using h
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ ((one_le_inv₀ hL).mpr hLle))

/-- The quantitative exponent-two scheme on two coordinates and two time labels. -/
noncomputable def twoSliceScheme (m : ℕ) [Nonempty (Fin m)] :
    SelectableProjectionScheme m 2 2 2 where
  label_pos := by norm_num
  time σ := σ
  measurable_time i := measurable_pi_apply i
  select I := MeasurableEquiv.finTwoArrow ⁻¹' twoSliceParameters I
  measurable_select := by
    intro X _ I hI
    exact (measurableSet_twoSliceParameters_family hI).preimage
      (f := fun p : X × (Fin 2 → ℝ) ↦ (p.1, MeasurableEquiv.finTwoArrow p.2))
      (measurable_fst.prodMk (MeasurableEquiv.finTwoArrow.measurable.comp measurable_snd))
  volumeExponent := 2
  volumeExponent_pos := by norm_num
  boundExponent := m
  boundExponent_pos := Fin.pos_iff_nonempty.mpr inferInstance
  lowerConstant := 1 / 2
  lowerConstant_pos := by norm_num
  upperConstant := 100 ^ m
  one_le_upperConstant := one_le_pow₀ (by norm_num)
  volume_lower := by
    intro I hI hIunit _
    have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
    rw [(volume_preserving_finTwoArrow ℝ).measure_preimage_equiv (twoSliceParameters I)]
    simpa only [twoSliceParameters, div_eq_mul_inv, one_mul, mul_comm] using
      half_square_le_volume_separatedPairs hI hIfin
  coordinates_bound := by
    intro I _ hIunit hIpos σ hσ i
    have hi := hIunit (coordinate_mem_aux hσ i)
    have hiabs : |σ i| ≤ 1 := by simpa only [abs_of_nonneg hi.1] using hi.2
    exact hiabs.trans (one_le_seed_bound_aux hIunit hIpos)
  time_mem := by
    intro I _ _ _ σ hσ i
    exact coordinate_mem_aux hσ i
  estimate := by
    intro I _ hIunit hIpos σ hσ G _ hGb
    have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
    have ht : Finset.univ.image σ = {σ 0, σ 1} := by
      ext t
      simp [Fin.exists_fin_two, eq_comm]
    have h := volume_le_of_mem_twoSliceParameters hIpos hIfin hσ hGb
    simpa only [ht, MeasurableEquiv.finTwoArrow_apply, sub_self, Real.rpow_zero, mul_one,
      Real.rpow_two, div_eq_mul_inv, mul_pow] using h

end NKBesicovitch.Projection.Selection
