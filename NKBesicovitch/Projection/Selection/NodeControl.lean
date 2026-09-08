/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PatternControl
public import NKBesicovitch.Projection.Selection.NodePatternLabels
public import NKBesicovitch.Projection.Selection.NodeUniformBounds

/-!
# Uniform control of every selected analytic pattern

All selected nodes have the same separation radius `|I|/100`, at most
`L` outer and inner heights, and the same polynomial input constant.
Their code, pair, and inner Jacobian bounds therefore follow uniformly.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

theorem nodePattern_isControlled {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {q : (ℝ × ℝ) × ℝ}
    (hq : q ∈ separatedTriples I ((volume I).toReal / 100))
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I q.1.1 q.1.2 q.2 ((volume I).toReal / 100)) :
    (S.nodePattern hI hIunit hIpos hq hp).IsControlled ((volume I).toReal / 100)
      (S.upperConstant * (100 / (volume I).toReal) ^ (8 * S.boundExponent)) L := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  have hx1 : (volume I).toReal ≤ 1 := by
    simpa only [measureReal_def, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one] using measureReal_mono (μ := volume) hIunit (by simp)
  have hs : 1 ≤ 100 / (volume I).toReal := (le_div_iff₀ hx).mpr (by linarith)
  have hb := mem_separatedTriples.mp hq
  refine {
    radius_pos := by positivity
    radius_le_one := by linarith
    one_le_constant := one_le_mul_of_one_le_of_one_le S.one_le_upperConstant (one_le_pow₀ hs)
    times_unit := fun t ht ↦ hIunit (S.nodePattern_times_subset hI hIunit hIpos hq hp t ht)
    base_separation := hb.2.2.2.1
    base_c_separation := hb.2.2.2.2.1
    dual_separation := ?_
    outer_card := ?_
    inner_card := ?_
    outer_bound := fun G hG hGb ↦ S.node_outer_uniform_estimate hI hIunit hIpos hp hG hGb
    inner_bound := fun u _ G hG hGb ↦
      S.node_inner_uniform_estimate hI hIunit hIpos hp (S.labelIndex p.2.1 u) hG hGb }
  · intro u hu t ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    have hg := S.cornerNodeParameters_child_triple hI hIunit hIpos (by positivity) hb.2.1 hp
      (S.labelIndex p.2.1 u) j
    rw [S.time_labelIndex hu] at hg
    exact (mem_separatedTriples.mp hg).2.2.2.2.1
  · exact Finset.card_image_le.trans (by simp)
  · exact fun _ _ ↦ Finset.card_image_le.trans (by simp)

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
