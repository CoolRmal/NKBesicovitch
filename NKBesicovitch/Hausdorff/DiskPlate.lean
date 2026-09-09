/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Hausdorff.OrthogonalPlates
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Comparing disk portions with thickened plate averages

Normal translation of a portion of a disk lies in the corresponding
thickened set. Tonelli and the cylinder volume bounds give a uniform
comparison, with factor `2^k` for thickness at most one.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NKBesicovitch.Hausdorff

variable {n k : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

theorem disk_integral_mul_normal_volume_le (hU : MeasurableSet U)
    (V : Grassmannian n k) (a : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    (∫⁻ v in closedBall (0 : V.val) 1, U.indicator (fun _ ↦ (1 : ℝ≥0∞)) (a + v)) *
        volume (ball (0 : V.valᗮ) δ) ≤
      ∫⁻ x in plate δ V.val a, (thickening δ U).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  let T := fun z : V.val × V.valᗮ ↦ a + (z.1 : EuclideanSpace ℝ (Fin n)) + z.2
  let f := U.indicator (fun _ ↦ (1 : ℝ≥0∞))
  let g := (thickening δ U).indicator (fun _ ↦ (1 : ℝ≥0∞))
  have hf : Measurable f := measurable_const.indicator hU
  have hg : Measurable g := measurable_const.indicator isOpen_thickening.measurableSet
  have hT : Measurable T := (measurePreserving_orthogonal_add V.val a).measurable
  have hm : MeasurableSet (plate δ V.val a) := isOpen_thickening.measurableSet
  rw [← (measurePreserving_orthogonal_add V.val a).setLIntegral_comp_preimage hm hg]
  calc
    _ = ∫⁻ z in closedBall (0 : V.val) 1 ×ˢ ball (0 : V.valᗮ) δ, f (a + z.1) := by
      rw [Measure.volume_eq_prod, setLIntegral_prod]
      · simp only [setLIntegral_const]
        exact (lintegral_mul_const _ (hf.comp (continuous_const.add
          continuous_subtype_val).measurable)).symm
      · exact (hf.comp (by fun_prop)).aemeasurable
    _ ≤ ∫⁻ z in closedBall (0 : V.val) 1 ×ˢ ball (0 : V.valᗮ) δ, g (T z) := by
      apply setLIntegral_mono (hg.comp hT)
      rintro ⟨v, w⟩ ⟨hv, hw⟩
      by_cases hx : a + (v : EuclideanSpace ℝ (Fin n)) ∈ U
      · have hz : T (v, w) ∈ thickening δ U :=
          mem_thickening_iff.mpr ⟨a + v, hx, by simpa [T, dist_eq_norm] using hw⟩
        simp [f, g, hx, hz]
      · simp [f, hx]
    _ ≤ _ := lintegral_mono_set (orthogonal_cylinder_subset_plate V.val a δ)

theorem volume_plate_le_two_pow_mul (V : Grassmannian n k)
    (a : EuclideanSpace ℝ (Fin n)) {δ : ℝ} (hδ : δ ≤ 1) :
    volume (plate δ V.val a) ≤ (2 : ℝ≥0∞) ^ k * volume (closedBall (0 : V.val) 1) *
      volume (ball (0 : V.valᗮ) δ) := by
  have h := volume_plate_le_orthogonal_cylinder V.val a hδ
  have he : volume (closedBall (0 : V.val) 2) =
      (2 : ℝ≥0∞) ^ k * volume (closedBall (0 : V.val) 1) := by
    rw [volume.addHaar_closedBall' _ (by norm_num : (0 : ℝ) ≤ 2)]
    simp [V.property]
  rwa [he] at h

/-- A disk portion is controlled by the plate maximal function of its thickening. -/
theorem diskAverage_indicator_le_plateMaximal (hU : MeasurableSet U)
    (V : Grassmannian n k) (a : EuclideanSpace ℝ (Fin n)) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    diskAverage (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) V a ≤
      (2 : ℝ≥0∞) ^ k * plateMaximal δ
        ((thickening δ U).indicator (fun _ ↦ (1 : ℝ≥0∞))) V := by
  let g := (thickening δ U).indicator (fun _ ↦ (1 : ℝ≥0∞))
  let D := volume (closedBall (0 : V.val) 1)
  let N := volume (ball (0 : V.valᗮ) δ)
  have hD : D ≠ 0 := (measure_closedBall_pos volume _ zero_lt_one).ne'
  have hDf : D ≠ ∞ := measure_closedBall_lt_top.ne
  have hN : N ≠ 0 := (measure_ball_pos volume _ hδ).ne'
  have hNf : N ≠ ∞ := measure_ball_lt_top.ne
  rw [diskAverage, ENNReal.div_le_iff hD hDf]
  apply (ENNReal.mul_le_mul_iff_left hN hNf).mp
  calc
    _ ≤ ∫⁻ x in plate δ V.val a, g x := disk_integral_mul_normal_volume_le hU V a δ
    _ ≤ plateMaximal δ g V * volume (plate δ V.val a) := by
      apply (ENNReal.div_le_iff (volume_plate_pos hδ _ _).ne'
        (volume_plate_lt_top δ _ _).ne).mp
      exact le_iSup (fun a ↦ (∫⁻ x in plate δ V.val a, g x) / volume (plate δ V.val a)) a
    _ ≤ plateMaximal δ g V * ((2 : ℝ≥0∞) ^ k * D * N) :=
      mul_le_mul_right (volume_plate_le_two_pow_mul V a hδ1) _
    _ = _ := by dsimp only [D, N, g]; ac_rfl

end NKBesicovitch.Hausdorff
