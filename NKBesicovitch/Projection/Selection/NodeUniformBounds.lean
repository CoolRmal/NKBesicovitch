/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.NodeBounds
public import NKBesicovitch.Projection.Selection.ScaleBounds
public import NKBesicovitch.Projection.Selection.SeparatedTriples

/-!
# A common polynomial bound at every selected node

The scalar, all outer and inner coordinates, and both input projection
constants are bounded by `C (100/|I|)^(8B)`, where `C` and `B` are the
upper constant and bound exponent of the input scheme. This bound is
independent of the node and of all selected labels and scalar values.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

theorem node_reservoir_constants_le {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) :
    S.upperConstant *
        (((volume I).toReal / 100 * (volume I).toReal ^ 7 / 320000000000)⁻¹) ^ S.boundExponent ≤
      S.upperConstant * (100 / (volume I).toReal) ^ (8 * S.boundExponent) ∧
    S.upperConstant *
        (((volume I).toReal / 100 * (volume I).toReal ^ 5 / 8000000)⁻¹) ^ S.boundExponent ≤
      S.upperConstant * (100 / (volume I).toReal) ^ (8 * S.boundExponent) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  have hx1 : (volume I).toReal ≤ 1 := by
    simpa only [measureReal_def, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one] using measureReal_mono (μ := volume) hIunit (by simp)
  have hC := zero_le_one.trans S.one_le_upperConstant
  exact ⟨mul_le_mul_of_nonneg_left
      (inv_pow_le_of_radius_pow_le hx (radius_pow_eight_le_outer_threshold hx.le) _) hC,
    mul_le_mul_of_nonneg_left
      (inv_pow_le_of_radius_pow_le hx (radius_pow_eight_le_inner_threshold hx.le hx1) _) hC⟩

theorem node_scalar_uniform_bound {I : Set ℝ} (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I)
    {q : (ℝ × ℝ) × ℝ} (hq : q ∈ separatedTriples I ((volume I).toReal / 100))
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I q.1.1 q.1.2 q.2 ((volume I).toReal / 100)) :
    |p.1| ≤ S.upperConstant * (100 / (volume I).toReal) ^ (8 * S.boundExponent) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  have hx1 : (volume I).toReal ≤ 1 := by
    simpa only [measureReal_def, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one] using measureReal_mono (μ := volume) hIunit (by simp)
  have hs : 1 ≤ 100 / (volume I).toReal := (le_div_iff₀ hx).mpr (by linarith)
  have hb := mem_separatedTriples.mp hq
  have hκ := (cornerReservoir_scalar_bounds hIunit hIpos (hIunit hb.1) (hIunit hb.2.1)
    (hIunit hb.2.2.1) (by positivity) hb.2.2.2.1 hp.1).2.2
  have hB := S.boundExponent_pos
  exact hκ.trans ((pow_le_pow_right₀ hs (by omega : 3 ≤ 8 * S.boundExponent)).trans
    (le_mul_of_one_le_left (by positivity) S.one_le_upperConstant))

theorem node_outer_coordinates_uniform_bound {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c : ℝ}
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c ((volume I).toReal / 100)) (j : Fin D) :
    |p.2.1 j| ≤ S.upperConstant * (100 / (volume I).toReal) ^ (8 * S.boundExponent) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  exact (S.cornerNodeParameters_outer_coordinates_bound hI hIunit hIpos (by positivity) hp j).trans
    (S.node_reservoir_constants_le hIunit hIpos).1

theorem node_inner_coordinates_uniform_bound {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c : ℝ}
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c ((volume I).toReal / 100)) (i : Fin L) (j : Fin D) :
    |p.2.2 i j| ≤ S.upperConstant * (100 / (volume I).toReal) ^ (8 * S.boundExponent) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  exact (S.cornerNodeParameters_inner_coordinates_bound hI hIunit hIpos
    (by positivity) hp i j).trans
    (S.node_reservoir_constants_le hIunit hIpos).2

theorem node_outer_uniform_estimate {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c : ℝ}
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c ((volume I).toReal / 100))
    {G : Set (Line m)} (hG : MeasurableSet G) (hGb : IsBounded G) :
    (volume G).toReal ≤ (S.upperConstant * (100 / (volume I).toReal) ^ (8 * S.boundExponent)) *
      (parallelMultiplicity G).toReal ^ (2 - β) *
        (sliceSize (Finset.univ.image (S.time p.2.1)) G).toReal ^ β := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  exact (S.cornerNodeParameters_outer_estimate hI hIunit hIpos (by positivity) hp hG hGb).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (S.node_reservoir_constants_le hIunit hIpos).1
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)) (Real.rpow_nonneg ENNReal.toReal_nonneg _))

theorem node_inner_uniform_estimate {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c : ℝ}
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c ((volume I).toReal / 100)) (i : Fin L)
    {G : Set (Line m)} (hG : MeasurableSet G) (hGb : IsBounded G) :
    (volume G).toReal ≤ (S.upperConstant * (100 / (volume I).toReal) ^ (8 * S.boundExponent)) *
      (parallelMultiplicity G).toReal ^ (2 - β) *
        (sliceSize (Finset.univ.image (S.time (p.2.2 i))) G).toReal ^ β := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  exact (S.cornerNodeParameters_inner_estimate hI hIunit hIpos (by positivity) hp i hG hGb).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (S.node_reservoir_constants_le hIunit hIpos).2
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)) (Real.rpow_nonneg ENNReal.toReal_nonneg _))

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
