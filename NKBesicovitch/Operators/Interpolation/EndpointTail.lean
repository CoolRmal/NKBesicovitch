/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Interpolation.SmoothAmplitude
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# An output-tail estimate from two endpoint bounds

Smooth amplitude decomposition and Chebyshev's inequality bound the output
distribution by the squared input tail. The operator only needs endpoint
bounds on Schwartz functions with the prescribed spatial support.
-/

public section

open Function Set MeasureTheory
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Y]

private theorem eLpNorm_two_sq_le_tail (f h : 𝓢(E, ℂ)) {t : ℝ}
    (hnorm : ∀ x, ‖h x‖ ≤ ‖f x‖) (hzero : ∀ x, ‖f x‖ ≤ t → h x = 0) :
    eLpNorm h 2 volume ^ 2 ≤ ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ 2 := by
  have heq := eLpNorm_nnreal_pow_eq_lintegral (f := h) (μ := volume)
    (p := 2) (by norm_num)
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at heq
  rw [heq, ← lintegral_indicator (isOpen_lt continuous_const f.continuous.norm).measurableSet]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ {x | t < ‖f x‖}
  · rw [indicator_of_mem hx]
    have hnorm' : ‖h x‖ₑ ≤ ‖f x‖ₑ := by
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hnorm x)
    exact pow_le_pow_left' hnorm' 2
  · simp only [hzero x (le_of_not_gt hx), enorm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_le]

/-- The `L²` and bounded-input endpoints control every output superlevel set by an input tail. -/
theorem measure_norm_gt_le_of_endpoints (T : 𝓢(E, ℂ) →+ (Y → ℂ)) (μ : Measure Y)
    {s : Set E} {A : ℝ≥0∞} {B : ℝ} (hB : 0 < B)
    (hmeas : ∀ f, AEStronglyMeasurable (T f) μ)
    (h₂ : ∀ f : 𝓢(E, ℂ), support (f : E → ℂ) ⊆ s →
      eLpNorm (T f) 2 μ ≤ A * eLpNorm f 2 volume)
    (h_top : ∀ f : 𝓢(E, ℂ), support (f : E → ℂ) ⊆ s → ∀ r : ℝ, 0 ≤ r →
      (∀ x, ‖f x‖ ≤ r) → ∀ᵐ y ∂μ, ‖T f y‖ ≤ B * r)
    (f : 𝓢(E, ℂ)) (hf : HasCompactSupport (f : E → ℂ))
    (hs : support (f : E → ℂ) ⊆ s) {t : ℝ} (ht : 0 < t) :
    μ {y | 4 * B * t < ‖T f y‖} ≤
      (ENNReal.ofReal (2 * B * t))⁻¹ ^ 2 * A ^ 2 *
        ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ 2 := by
  obtain ⟨g, h, heq, hg, hh, hg_norm, hh_norm, hh_zero⟩ :=
    exists_schwartz_amplitude_decomposition f hf ht
  have hsub : μ {y | 4 * B * t < ‖T f y‖} ≤
      μ {y | ENNReal.ofReal (2 * B * t) ≤ ‖T h y‖ₑ} := by
    apply measure_mono_ae
    filter_upwards [h_top g (hg.trans hs) (2 * t) (by positivity) hg_norm] with y hy hy'
    have hn : ‖T f y‖ ≤ ‖T g y‖ + ‖T h y‖ := by
      rw [heq, map_add, Pi.add_apply]
      exact norm_add_le _ _
    change ENNReal.ofReal (2 * B * t) ≤ ‖T h y‖ₑ
    rw [← ofReal_norm]
    change 4 * B * t < ‖T f y‖ at hy'
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hcheb := meas_ge_le_mul_pow_eLpNorm_enorm μ (p := 2) (by norm_num) (by norm_num)
    (hmeas h) (ENNReal.ofReal_pos.mpr (by positivity : 0 < 2 * B * t)).ne'
    (by simp)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hcheb
  refine (hsub.trans hcheb).trans ?_
  have hsq := pow_le_pow_left' (h₂ h (hh.trans hs)) 2
  rw [mul_pow] at hsq
  have htail := eLpNorm_two_sq_le_tail f h hh_norm hh_zero
  calc
    _ ≤ (ENNReal.ofReal (2 * B * t))⁻¹ ^ 2 *
        (A ^ 2 * ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ 2) :=
      mul_le_mul' le_rfl (hsq.trans (mul_le_mul' le_rfl htail))
    _ = _ := (mul_assoc _ _ _).symm

end NKBesicovitch
