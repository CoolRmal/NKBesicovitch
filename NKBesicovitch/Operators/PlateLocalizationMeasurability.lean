/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.PlateMeasurability

/-!
# Joint measurability for localization to moving balls

The ball center and orthogonal frame vary together. For a fixed spatial
point, membership in both the moving ball and moving plate is open.
Fatou and the supremum over plate centers therefore give joint lower
semicontinuity, even when the fixed nonnegative input is merely Borel.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

private theorem lowerSemicontinuous_plate_ball_indicator (δ R : ℝ)
    (a x : EuclideanSpace ℝ (Fin n)) (V : Grassmannian n k) (c : ℝ≥0∞) :
    LowerSemicontinuous (fun z : Rotations n × EuclideanSpace ℝ (Fin n) ↦
      (plate δ (Grassmannian.rotate z.1 V).val a).indicator
        (fun x ↦ (ball z.2 R).indicator (fun _ ↦ c) x) x) := by
  have hopen : IsOpen {z : Rotations n × EuclideanSpace ℝ (Fin n) |
      x ∈ plate δ (Grassmannian.rotate z.1 V).val a ∧ x ∈ ball z.2 R} :=
    ((isOpen_setOf_mem_plate_rotate δ a x V).preimage continuous_fst).inter
      (isOpen_lt (continuous_const.dist continuous_snd) continuous_const)
  have heq (z : Rotations n × EuclideanSpace ℝ (Fin n)) :
      (plate δ (Grassmannian.rotate z.1 V).val a).indicator
          (fun x ↦ (ball z.2 R).indicator (fun _ ↦ c) x) x =
        {z : Rotations n × EuclideanSpace ℝ (Fin n) |
          x ∈ plate δ (Grassmannian.rotate z.1 V).val a ∧ x ∈ ball z.2 R}.indicator
            (fun _ ↦ c) z := by
    classical
    by_cases hp : x ∈ plate δ (Grassmannian.rotate z.1 V).val a <;>
      by_cases hb : x ∈ ball z.2 R <;>
        simp only [indicator, mem_ofPred_eq, hp, hb, and_true, and_false, ite_true, ite_false]
  simp_rw [heq]
  exact hopen.lowerSemicontinuous_indicator bot_le

theorem lowerSemicontinuous_plateAverage_ball_orbit (δ R : ℝ)
    (a : EuclideanSpace ℝ (Fin n)) (V : Grassmannian n k)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    LowerSemicontinuous (fun z : Rotations n × EuclideanSpace ℝ (Fin n) ↦
      (∫⁻ x in plate δ (Grassmannian.rotate z.1 V).val a, (ball z.2 R).indicator f x) /
        volume (plate δ (Grassmannian.rotate z.1 V).val a)) := by
  have heq (z : Rotations n × EuclideanSpace ℝ (Fin n)) :
      (∫⁻ x in plate δ (Grassmannian.rotate z.1 V).val a, (ball z.2 R).indicator f x) /
          volume (plate δ (Grassmannian.rotate z.1 V).val a) =
        ∫⁻ x, (plate δ (Grassmannian.rotate z.1 V).val a).indicator
          (fun x ↦ (ball z.2 R).indicator (fun x ↦ f x *
            (volume (plate δ V.val 0))⁻¹) x) x := by
    have hm : MeasurableSet (plate δ (Grassmannian.rotate z.1 V).val a) :=
      isOpen_thickening.measurableSet
    rw [lintegral_indicator hm, volume_plate_rotate, div_eq_mul_inv,
      ← lintegral_mul_const _ (hf.indicator isOpen_ball.measurableSet)]
    simp only [← indicator_mul_const]
  simp_rw [heq]
  apply lowerSemicontinuous_lintegral
  · intro z
    exact (((hf.mul measurable_const).indicator isOpen_ball.measurableSet).indicator
      isOpen_thickening.measurableSet).aemeasurable
  · intro x
    convert lowerSemicontinuous_plate_ball_indicator δ R a x V
      (f x * (volume (plate δ V.val 0))⁻¹) using 1
    funext z
    by_cases hp : x ∈ plate δ (Grassmannian.rotate z.1 V).val a <;>
      by_cases hb : x ∈ ball z.2 R <;>
        simp only [indicator, hp, hb, ite_true, ite_false]

/-- Localization is jointly Borel in the ball center and orthogonal frame. -/
theorem measurable_plateMaximal_ball_orbit (δ R : ℝ) (V : Grassmannian n k)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : Rotations n × EuclideanSpace ℝ (Fin n) ↦
      plateMaximal δ ((ball z.2 R).indicator f) (Grassmannian.rotate z.1 V)) :=
  (lowerSemicontinuous_iSup fun a ↦
    lowerSemicontinuous_plateAverage_ball_orbit δ R a V hf).measurable

end NKBesicovitch
