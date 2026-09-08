/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.MixedNorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Averaged norms of localization to moving balls

Tonelli and translation invariance show that averaging the `p`th power
of the localized input norm over all ball centers multiplies the original
`p`th power by the volume of one ball. Infinite input norms are included.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

theorem measurable_ball_indicator (R : ℝ) (hf : Measurable f) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
      (ball z.1 R).indicator f z.2) := by
  have hm := (hf.comp measurable_snd).indicator
    (isOpen_lt (g := fun _ ↦ R) (continuous_snd.dist continuous_fst)
      continuous_const).measurableSet
  exact hm

theorem lintegral_lintegral_ball_indicator (R : ℝ) (hf : Measurable f) :
    (∫⁻ y, ∫⁻ x, (ball y R).indicator f x) =
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) R) * ∫⁻ x, f x := by
  have hi (x : EuclideanSpace ℝ (Fin n)) : (∫⁻ y, (ball y R).indicator f x) =
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) R) * f x := by
    have he : (fun y ↦ (ball y R).indicator f x) = (ball x R).indicator (fun _ ↦ f x) := by
      funext y
      simp only [indicator, mem_ball, dist_comm]
    rw [he, lintegral_indicator_const isOpen_ball.measurableSet,
      volume.addHaar_ball_center x, mul_comm]
  rw [lintegral_lintegral_swap (measurable_ball_indicator R hf).aemeasurable]
  simp_rw [hi]
  exact lintegral_const_mul _ hf

theorem lintegral_eLpNorm_ball_rpow (R : ℝ) (hf : Measurable f) {p : ℝ≥0} (hp : 0 < p) :
    (∫⁻ y, eLpNorm ((ball y R).indicator f) p volume ^ (p : ℝ)) =
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) R) * eLpNorm f p volume ^ (p : ℝ) := by
  simp_rw [eLpNorm_nnreal_pow_eq_lintegral hp.ne', enorm_eq_self]
  have he (x y : EuclideanSpace ℝ (Fin n)) : (ball y R).indicator f x ^ (p : ℝ) =
      (ball y R).indicator (fun x ↦ f x ^ (p : ℝ)) x := by
    by_cases hx : x ∈ ball y R
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos (show 0 < (p : ℝ) from hp)]
  simp_rw [he]
  exact lintegral_lintegral_ball_indicator R (hf.pow_const _)

end NKBesicovitch
