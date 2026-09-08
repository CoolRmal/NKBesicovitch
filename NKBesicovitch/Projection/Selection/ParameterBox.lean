/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.SchemeBounds
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# One finite parameter box for all time sets of a given minimum measure

The coordinate bound places every selected parameter in the same box.
Its explicit volume pays for the simultaneous-selection averaging step.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

/-- The common coordinate box at a prescribed positive lower time measure. -/
noncomputable def parameterBox (r : ℝ) : Set (Fin D → ℝ) :=
  Icc (fun _ ↦ -(S.upperConstant * r⁻¹ ^ S.boundExponent))
    (fun _ ↦ S.upperConstant * r⁻¹ ^ S.boundExponent)

theorem measurableSet_parameterBox (r : ℝ) : MeasurableSet (S.parameterBox r) :=
  measurableSet_Icc

theorem select_subset_parameterBox {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) {r : ℝ} (hr : 0 < r) (hmeasure : ENNReal.ofReal r ≤ volume I) :
    S.select I ⊆ S.parameterBox r := by
  intro σ hσ
  exact ⟨fun j ↦ (abs_le.mp (S.coordinates_bound_of_measure_lower hI hIunit hr hmeasure hσ j)).1,
    fun j ↦ (abs_le.mp (S.coordinates_bound_of_measure_lower hI hIunit hr hmeasure hσ j)).2⟩

theorem volume_parameterBox {r : ℝ} (hr : 0 ≤ r) :
    volume (S.parameterBox r) =
      ENNReal.ofReal ((2 * S.upperConstant) ^ D * r⁻¹ ^ (S.boundExponent * D)) := by
  have hC : 0 ≤ S.upperConstant := zero_le_one.trans S.one_le_upperConstant
  have hR : 0 ≤ 2 * (S.upperConstant * r⁻¹ ^ S.boundExponent) := by positivity
  simp only [parameterBox, Real.volume_Icc_pi, sub_neg_eq_add, ← two_mul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow hR]
  congr 1
  rw [← mul_assoc, mul_pow, ← pow_mul]

theorem volume_parameterBox_pos {r : ℝ} (hr : 0 < r) : 0 < volume (S.parameterBox r) := by
  have hC : 0 < S.upperConstant := zero_lt_one.trans_le S.one_le_upperConstant
  rw [S.volume_parameterBox hr.le]
  exact ENNReal.ofReal_pos.mpr (by positivity)

theorem volume_parameterBox_ne_top {r : ℝ} (hr : 0 ≤ r) : volume (S.parameterBox r) ≠ ∞ := by
  rw [S.volume_parameterBox hr]
  exact ENNReal.ofReal_ne_top

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
