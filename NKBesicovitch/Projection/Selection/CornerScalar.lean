/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerCode
public import NKBesicovitch.Projection.Selection.DualReservoir

/-!
# Converting between inner and outer corner scalars

For a fixed outer time `u`, the inner scalar is `κ(u-c)/(u-a)`.
Swapping `a` and `c` gives its inverse. Lebesgue measure of a preimage
scales by `|(u-a)/(u-c)|`; the separation conditions give polynomial
lower and upper bounds on this factor.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

theorem measurable_cornerInnerCoefficient {X : Type*} [MeasurableSpace X]
    {a c κ u : X → ℝ} (ha : Measurable a) (hc : Measurable c) (hκ : Measurable κ)
    (hu : Measurable u) :
    Measurable (fun x ↦ cornerInnerCoefficient (a x) (c x) (κ x) (u x)) :=
  (hκ.mul (hu.sub hc)).div (hu.sub ha)

theorem cornerInnerCoefficient_swap {a c u : ℝ} (hua : u ≠ a) (huc : u ≠ c) (κ : ℝ) :
    cornerInnerCoefficient c a (cornerInnerCoefficient a c κ u) u = κ := by
  unfold cornerInnerCoefficient
  field_simp

theorem volume_preimage_cornerInnerCoefficient {a c u : ℝ} (hua : u ≠ a) (huc : u ≠ c)
    (S : Set ℝ) :
    volume ((fun κ ↦ cornerInnerCoefficient a c κ u) ⁻¹' S) =
      ENNReal.ofReal |(u - a) / (u - c)| * volume S := by
  have he : (fun κ ↦ cornerInnerCoefficient a c κ u) = (· * ((u - c) / (u - a))) := by
    funext κ
    exact mul_div_assoc κ (u - c) (u - a)
  rw [he, Real.volume_preimage_mul_right
    (div_ne_zero (sub_ne_zero.mpr huc) (sub_ne_zero.mpr hua)), inv_div]

theorem corner_scalar_ratio_bounds {a c u r : ℝ} (ha : a ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hu : u ∈ Icc 0 1) (hr : 0 < r) (hua : r ≤ dist u a) (huc : r ≤ dist u c) :
    r ≤ |(u - a) / (u - c)| ∧ |(u - a) / (u - c)| ≤ r⁻¹ := by
  have hua₁ := Real.dist_le_of_mem_Icc_01 hu ha
  have huc₁ := Real.dist_le_of_mem_Icc_01 hu hc
  simp only [Real.dist_eq] at hua huc hua₁ huc₁
  rw [abs_div]
  exact ⟨hua.trans (le_div_self (abs_nonneg _) (hr.trans_le huc) huc₁),
    by simpa only [one_div] using div_le_div₀ zero_le_one hua₁ hr huc⟩

end NKBesicovitch.Projection.Selection
