/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.PlateGeometry
public import NKBesicovitch.Geometry.RigidMotions
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Comparing plate normalizations across one dimension

The product of a contracted lower-dimensional plate and an interval of
length one lies inside the lifted plate. Volume preservation and Haar
scaling give a uniform lower bound for the lifted plate volume. The
bound holds at every positive thickness and is independent of the plane
and of both centers.
-/

public section

open MeasureTheory Set Metric NKBesicovitch.Grassmannian
open scoped ENNReal Pointwise

namespace NKBesicovitch.Induction

variable {n m k : ℕ} {v : EuclideanSpace ℝ (Fin n)}

theorem half_pow_mul_volume_plate_le (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    {δ : ℝ} (hδ : 0 < δ) :
    (2 : ℝ≥0∞)⁻¹ ^ m * volume (plate δ V.val 0) ≤
      volume (plate δ (normalLift hv b V).val 0) := by
  have hsub : ((1 / 2 : ℝ) • plate δ V.val 0) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2) ⊆
      normalCoordinatesWithBasis hv b ⁻¹' plate δ (normalLift hv b V).val 0 := by
    rintro ⟨x, t⟩ ⟨⟨y, hy, rfl⟩, ht⟩
    exact normalCoordinates_half_plate_mem hv b V hδ hy ht
  have hvol := measure_mono (μ := volume) hsub
  have hm : MeasurableSet (plate δ (normalLift hv b V).val 0) :=
    isOpen_thickening.measurableSet
  rw [(measurePreserving_normalCoordinatesWithBasis hv b).measure_preimage
    hm.nullMeasurableSet] at hvol
  rw [Measure.volume_eq_prod, Measure.prod_prod,
    volume.addHaar_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Real.volume_Icc] at hvol
  norm_num [ENNReal.ofReal_pow, ENNReal.ofReal_div_of_pos] at hvol ⊢
  exact hvol

theorem half_pow_mul_volume_plate_le_centers (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    {δ : ℝ} (hδ : 0 < δ) (a : EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin n)) :
    (2 : ℝ≥0∞)⁻¹ ^ m * volume (plate δ V.val a) ≤
      volume (plate δ (normalLift hv b V).val z) := by
  have hlow := volume_plate_rotate (1 : Rotations m) a V δ
  have hhigh := volume_plate_rotate (1 : Rotations n) z (normalLift hv b V) δ
  simp only [rotate_one] at hlow hhigh
  rw [hlow, hhigh]
  exact half_pow_mul_volume_plate_le hv b V hδ

end NKBesicovitch.Induction
