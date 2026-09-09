/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Interpolation.ScaledLayerCake

/-!
# Integrating weighted input-level series

Scaled superlevel measures are antitone in the real threshold, hence measurable.
Tonelli and the scaled layer-cake identity evaluate an arbitrary nonnegative
weighted series of these input levels in terms of the input moment.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {X : Type*} [MeasurableSpace X]

theorem measurable_measure_scaled_superlevel (μ : Measure X) (f : X → ℝ≥0∞)
    {c : ℝ} (hc : 0 ≤ c) : Measurable (fun t : ℝ ↦ μ {x | ENNReal.ofReal (c * t) ≤ f x}) := by
  apply Antitone.measurable
  intro s t hst
  apply measure_mono
  intro x hx
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hst hc)).trans hx

/-- Integrating a weighted series of scaled input levels gives its exact moment coefficient. -/
theorem lintegral_input_level_series (μ : Measure X) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hfin : ∀ x, f x ≠ ∞) {p : ℝ} (hp : 0 < p)
    (b : ℕ → ℝ≥0∞) (c : ℕ → ℝ) (hc : ∀ j, 0 < c j) :
    ENNReal.ofReal p * (∫⁻ t in Ioi (0 : ℝ),
      (∑' j : ℕ, b j * μ {x | ENNReal.ofReal (c j * t) ≤ f x}) *
        ENNReal.ofReal (t ^ (p - 1))) =
      (∑' j : ℕ, b j * ENNReal.ofReal (c j) ^ (-p)) * ∫⁻ x, f x ^ p ∂μ := by
  have hm (j) := measurable_measure_scaled_superlevel μ f (hc j).le
  have hw : Measurable (fun t : ℝ ↦ ENNReal.ofReal (t ^ (p - 1))) := by fun_prop
  have hterm (j) : Measurable (fun t : ℝ ↦ b j * μ {x | ENNReal.ofReal (c j * t) ≤ f x} *
      ENNReal.ofReal (t ^ (p - 1))) := (measurable_const.mul (hm j)).mul hw
  simp_rw [← ENNReal.tsum_mul_right]
  rw [lintegral_tsum (fun j ↦ (hterm j).aemeasurable),
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro j
  simp_rw [mul_assoc]
  have hh : Measurable (fun t : ℝ ↦ μ {x | ENNReal.ofReal (c j * t) ≤ f x} *
      ENNReal.ofReal (t ^ (p - 1))) := (hm j).mul hw
  rw [lintegral_const_mul (b j) hh, mul_left_comm (ENNReal.ofReal p),
    lintegral_scaled_ennreal_superlevels_mul_rpow μ hf hfin hp (hc j)]

/-- A distribution bound by scaled input levels gives the corresponding moment bound. -/
theorem lintegral_rpow_le_of_input_level_series {Y : Type*} [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {f : X → ℝ≥0∞} {g : Y → ℝ≥0∞}
    (hf : Measurable f) (hfin : ∀ x, f x ≠ ∞) (hg : Measurable g) (hgfin : ∀ y, g y ≠ ∞)
    {p : ℝ} (hp : 0 < p) (A : ℝ≥0∞) (b : ℕ → ℝ≥0∞) (c : ℕ → ℝ) (hc : ∀ j, 0 < c j)
    (hlevel : ∀ t : ℝ, 0 < t → ν {y | ENNReal.ofReal t < g y} ≤
      A * ∑' j : ℕ, b j * μ {x | ENNReal.ofReal (c j * t) ≤ f x}) :
    (∫⁻ y, g y ^ p ∂ν) ≤
      A * (∑' j : ℕ, b j * ENNReal.ofReal (c j) ^ (-p)) * ∫⁻ x, f x ^ p ∂μ := by
  have hs : Measurable (fun t : ℝ ↦ (∑' j : ℕ, b j *
      μ {x | ENNReal.ofReal (c j * t) ≤ f x}) * ENNReal.ofReal (t ^ (p - 1))) :=
    (Measurable.tsum fun j ↦ measurable_const.mul
      (measurable_measure_scaled_superlevel μ f (hc j).le)).mul (by fun_prop)
  rw [lintegral_ennreal_rpow_eq_lintegral_meas_lt_mul ν hg hgfin hp]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        (A * ∑' j : ℕ, b j * μ {x | ENNReal.ofReal (c j * t) ≤ f x}) *
          ENNReal.ofReal (t ^ (p - 1)) := mul_le_mul_right (lintegral_mono_ae
            ((ae_restrict_mem measurableSet_Ioi).mono fun t ht ↦
              mul_le_mul_left (hlevel t ht) _)) _
    _ = A * (ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        (∑' j : ℕ, b j * μ {x | ENNReal.ofReal (c j * t) ≤ f x}) *
          ENNReal.ofReal (t ^ (p - 1))) := by
      simp_rw [mul_assoc]
      rw [lintegral_const_mul A hs, mul_left_comm]
    _ = _ := by rw [lintegral_input_level_series μ hf hfin hp b c hc, mul_assoc]

end NKBesicovitch
