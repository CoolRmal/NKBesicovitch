/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.NormalCoordinates
public import Mathlib.Analysis.LConvolution
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Uniform bounds for smoothed line integrals

A line meets a radius-`R` ball during an interval of length at most `2R`.
Tonelli applies this bound to a convolution, with the kernel contributing
only its integral. The estimate is uniform over line directions and centers.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped ENNReal InnerProductSpace Convolution

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : E}

theorem support_lineIntegrand_subset_interval {f : E → ℝ≥0∞} {R : ℝ}
    (hs : Function.support f ⊆ closedBall 0 R) (hv : ‖v‖ = 1) (x : E) :
    Function.support (fun t : ℝ ↦ f (x + t • v)) ⊆
      Icc (-R - ⟪v, x⟫_ℝ) (R - ⟪v, x⟫_ℝ) := by
  intro t ht
  have hn : ‖x + t • v‖ ≤ R := by
    simpa only [mem_closedBall, dist_zero_right] using hs ht
  have hi := abs_real_inner_le_norm v (x + t • v)
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow,
    mul_one, one_mul] at hi
  have h := abs_le.mp (hi.trans hn)
  constructor <;> linarith

theorem lintegral_line_le_of_support_bound {f : E → ℝ≥0∞} {R : ℝ}
    (hs : Function.support f ⊆ closedBall 0 R) {C : ℝ≥0∞} (hC : ∀ x, f x ≤ C)
    (hv : ‖v‖ = 1) (x : E) :
    (∫⁻ t : ℝ, f (x + t • v)) ≤ ENNReal.ofReal (2 * R) * C := by
  rw [← setLIntegral_eq_of_support_subset (support_lineIntegrand_subset_interval hs hv x)]
  apply (lintegral_mono fun t ↦ hC (x + t • v)).trans_eq
  rw [setLIntegral_const, Real.volume_Icc, mul_comm]
  congr 1
  congr 1
  ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Tonelli bounds an integrated convolution by the absolute kernel integrated along the curve. -/
theorem enorm_integral_convolution_le {f g : E → ℂ} {γ : ℝ → E}
    (hf : Measurable f) (hg : Measurable g) (hγ : Measurable γ) :
    ‖∫ t : ℝ, (g ⋆[ContinuousLinearMap.lsmul ℂ ℂ] f) (γ t)‖ₑ ≤
      ∫⁻ z, ‖f z‖ₑ * ∫⁻ t : ℝ, ‖g (γ t - z)‖ₑ := by
  have hb (t : ℝ) : ‖(g ⋆[ContinuousLinearMap.lsmul ℂ ℂ] f) (γ t)‖ₑ ≤
      ∫⁻ z, ‖g (γ t - z)‖ₑ * ‖f z‖ₑ := by
    rw [convolution_lsmul_swap]
    simpa only [smul_eq_mul, enorm_mul] using
      enorm_integral_le_lintegral_enorm (fun z ↦ g (γ t - z) * f z)
  refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono hb).trans_eq ?_)
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro z
  rw [lintegral_mul_const (‖f z‖ₑ) (f := fun t : ℝ ↦ ‖g (γ t - z)‖ₑ) (by fun_prop), mul_comm]

/-- A uniform absolute-kernel bound on the input support controls the integrated convolution. -/
theorem enorm_integral_convolution_le_of_support {f g : E → ℂ} {γ : ℝ → E}
    (hf : Measurable f) (hg : Measurable g) (hγ : Measurable γ) {K : ℝ≥0∞}
    (hK : ∀ z ∈ Function.support f, (∫⁻ t : ℝ, ‖g (γ t - z)‖ₑ) ≤ K) :
    ‖∫ t : ℝ, (g ⋆[ContinuousLinearMap.lsmul ℂ ℂ] f) (γ t)‖ₑ ≤ K * eLpNorm f 1 volume := by
  apply (enorm_integral_convolution_le hf hg hγ).trans
  calc
    _ ≤ ∫⁻ z, ‖f z‖ₑ * K := by
      apply lintegral_mono
      intro z
      by_cases hz : f z = 0
      · simp [hz]
      · exact mul_le_mul' le_rfl (hK z hz)
    _ = _ := by
      rw [lintegral_mul_const _ hf.enorm, eLpNorm_one_eq_lintegral_enorm]
      exact mul_comm _ _

/-- Smoothing costs only the kernel mass in the uniform line-integral bound. -/
theorem lintegral_line_lconvolution_le {f g : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {R : ℝ} (hs : Function.support f ⊆ closedBall 0 R) {C : ℝ≥0∞} (hC : ∀ x, f x ≤ C)
    (hv : ‖v‖ = 1) (x : E) :
    (∫⁻ t : ℝ, (g ⋆ₗ f) (x + t • v)) ≤ ENNReal.ofReal (2 * R) * C * ∫⁻ z, g z := by
  simp only [lconvolution_def]
  rw [lintegral_lintegral_swap (by fun_prop)]
  simp_rw [← add_assoc]
  have hi (z : E) : (∫⁻ t : ℝ, g z * f (-z + x + t • v)) ≤
      g z * (ENNReal.ofReal (2 * R) * C) := by
    rw [lintegral_const_mul (g z) (f := fun t : ℝ ↦ f (-z + x + t • v)) (by fun_prop)]
    exact mul_le_mul_right (lintegral_line_le_of_support_bound hs hC hv (-z + x)) _
  apply (lintegral_mono hi).trans_eq
  rw [lintegral_mul_const _ hg]
  ac_rfl

/-- Absolute values of a signed smoothed line integral obey the positive convolution bound. -/
theorem enorm_line_convolution_le {f g : E → ℂ} (hf : Measurable f) (hg : Measurable g)
    {R : ℝ} (hs : Function.support f ⊆ closedBall 0 R) {C : ℝ≥0∞}
    (hC : ∀ x, ‖f x‖ₑ ≤ C) (hv : ‖v‖ = 1) (x : E) :
    ‖∫ t : ℝ, (g ⋆[ContinuousLinearMap.lsmul ℂ ℂ] f) (x + t • v)‖ₑ ≤
      ENNReal.ofReal (2 * R) * C * ∫⁻ z, ‖g z‖ₑ := by
  have hb (z : E) : ‖(g ⋆[ContinuousLinearMap.lsmul ℂ ℂ] f) z‖ₑ ≤
      ((fun z ↦ ‖g z‖ₑ) ⋆ₗ (fun z ↦ ‖f z‖ₑ)) z := by
    rw [convolution_lsmul, lconvolution_def]
    simpa only [smul_eq_mul, enorm_mul, sub_eq_add_neg, add_comm] using
      enorm_integral_le_lintegral_enorm (fun y ↦ g y * f (z - y))
  have hs' : Function.support (fun z ↦ ‖f z‖ₑ) ⊆ closedBall 0 R := by
    intro z hz
    apply hs
    intro hzero
    apply hz
    change ‖f z‖ₑ = 0
    rw [hzero, enorm_zero]
  exact (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono fun t ↦ hb (x + t • v)).trans
    (lintegral_line_lconvolution_le hf.enorm hg.enorm hs' hC hv x))

end NKBesicovitch.XRay
