/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.PlateWeakLevels
public import NKBesicovitch.Operators.PlateMeasurability
public import NKBesicovitch.Operators.Interpolation.LevelMoments
public import NKBesicovitch.Operators.PlateTruncation

/-!
# Moment bounds from a restricted weak plate estimate

For bounded inputs on finite-measure support, integrate the maximal superlevel
cover. The resulting constant is independent of the input bound, so monotone
truncation extends the estimate to all nonnegative extended-real inputs.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NKBesicovitch

/-- A restricted weak plate bound gives a moment estimate with an explicit level-series cost. -/
theorem lintegral_plateMaximal_rpow_le_level_sum_of_bounded {n k : ℕ}
    (ν : Measure (Grassmannian n k)) {δ : ℝ} (hδ : 0 < δ) {A : ℝ≥0∞} {P p : ℝ}
    (hweak : ∀ E : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet E → volume E ≠ ∞ →
      ∀ s : ℝ≥0, 0 < s → ν {V | (s : ℝ≥0∞) <
        plateMaximal δ (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) V} ≤
          A * (s : ℝ≥0∞) ^ (-P) * volume E)
    (hp : 0 < p) {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : volume K ≠ ∞) (hs : Function.support f ⊆ K)
    (B : ℝ≥0) (hB : ∀ x, f x ≤ B) (a : ℕ → ℝ≥0) (ha : ∀ j, 0 < a j)
    (hasum : (∑' j : ℕ, (2 : ℝ≥0∞) ^ j * (a j : ℝ≥0∞)) ≤ (2 : ℝ≥0∞)⁻¹) :
    (∫⁻ V, plateMaximal δ f V ^ p ∂ν) ≤
      A * (∑' j : ℕ, (a j : ℝ≥0∞) ^ (-P) * ENNReal.ofReal ((2 : ℝ) ^ j / 2) ^ (-p)) *
        ∫⁻ x, f x ^ p := by
  have hM (V : Grassmannian n k) : plateMaximal δ f V ≤ B := by
    simpa only [plateMaximal_const hδ] using plateMaximal_mono hB V (δ := δ)
  apply lintegral_rpow_le_of_input_level_series volume ν hf
    (fun x ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hB x)) (measurable_plateMaximal δ hf)
    (fun V ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hM V)) hp A
    (fun j ↦ (a j : ℝ≥0∞) ^ (-P)) (fun j ↦ (2 : ℝ) ^ j / 2) (fun j ↦ by positivity)
  intro t ht
  let s : ℝ≥0 := .mk t ht.le
  have he : (s : ℝ≥0∞) = ENNReal.ofReal t := (ENNReal.ofReal_eq_coe_nnreal ht.le).symm
  have hscale (j : ℕ) : ENNReal.ofReal (((2 : ℝ) ^ j / 2) * t) =
      ENNReal.ofReal t * (2 : ℝ≥0∞) ^ j / 2 := by
    rw [show ((2 : ℝ) ^ j / 2) * t = t * 2 ^ j / 2 by ring,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_mul ht.le, ENNReal.ofReal_pow (by norm_num)]
    norm_num
  simpa only [he, hscale] using measure_plateMaximal_superlevel_le_tsum ν hδ hweak hf
    hK hs s (show 0 < s from ht) a ha hasum

/-- The level-series moment bound holds without a pointwise bound on the input. -/
theorem lintegral_plateMaximal_rpow_le_level_sum {n k : ℕ}
    (ν : Measure (Grassmannian n k)) {δ : ℝ} (hδ : 0 < δ) {A : ℝ≥0∞} {P p : ℝ}
    (hweak : ∀ E : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet E → volume E ≠ ∞ →
      ∀ s : ℝ≥0, 0 < s → ν {V | (s : ℝ≥0∞) <
        plateMaximal δ (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) V} ≤
          A * (s : ℝ≥0∞) ^ (-P) * volume E)
    (hp : 0 < p) {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : volume K ≠ ∞) (hs : Function.support f ⊆ K)
    (a : ℕ → ℝ≥0) (ha : ∀ j, 0 < a j)
    (hasum : (∑' j : ℕ, (2 : ℝ≥0∞) ^ j * (a j : ℝ≥0∞)) ≤ (2 : ℝ≥0∞)⁻¹) :
    (∫⁻ V, plateMaximal δ f V ^ p ∂ν) ≤
      A * (∑' j : ℕ, (a j : ℝ≥0∞) ^ (-P) * ENNReal.ofReal ((2 : ℝ) ^ j / 2) ^ (-p)) *
        ∫⁻ x, f x ^ p := by
  rw [lintegral_plateMaximal_rpow_eq_iSup_truncation ν δ hf hp]
  apply iSup_le
  intro j
  have hs' : Function.support (fun x ↦ min (f x) (j : ℝ≥0∞)) ⊆ K := by
    intro x hx
    apply hs
    intro hz
    exact hx (by simp only [hz, zero_min])
  have h := lintegral_plateMaximal_rpow_le_level_sum_of_bounded ν hδ hweak hp
    (hf.min measurable_const) hK hs' (j : ℝ≥0) (fun x ↦ by simp) a ha hasum
  exact h.trans (mul_le_mul_right (lintegral_mono fun x ↦
    ENNReal.rpow_le_rpow (min_le_left (f x) (j : ℝ≥0∞)) hp.le) _)

end NKBesicovitch
