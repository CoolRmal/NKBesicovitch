/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.KernelTail
public import NKBesicovitch.Operators.XRay.ConvolutionBound
public import Mathlib.Analysis.Fourier.Convolution

/-!
# Rapid tails of smoothed X-ray transforms

For input supported in a fixed ball, distant transverse line integrals of a
smoothed input have arbitrary frequency and spatial decay. The input enters
only through its one-norm, and the constant is uniform over rotations.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap ENNReal NNReal Convolution

namespace NKBesicovitch.XRay

variable {m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- A fixed smoothing kernel gives arbitrary spatial decay, controlled by the input one-norm. -/
theorem exists_enorm_frameLineIntegral_convolution_le
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) (N : ℕ) (R : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
      ∀ u : Rotations (m + 1), ∀ x : EuclideanSpace ℝ (Fin m),
        ‖frameLineIntegral v b (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f)
          u x‖ₑ ≤ ENNReal.ofReal ((C : ℝ) * ((1 + ‖x‖) ^ N)⁻¹) * eLpNorm f 1 volume := by
  obtain ⟨C, hC⟩ := exists_lintegral_enorm_sub_frame_le v b ψ N R
  refine ⟨C, fun f hs u x ↦ ?_⟩
  simp only [frameLineIntegral, SchwartzMap.convolution_apply]
  apply enorm_integral_convolution_le_of_support f.continuous.measurable
    ψ.continuous.measurable (by fun_prop)
  intro z hz
  exact hC u x z (by simpa only [mem_closedBall, dist_zero_right] using hs hz)

/-- Smoothed line integrals have arbitrary frequency and spatial decay outside the support ball. -/
theorem exists_enorm_frameLineIntegral_dilation_tail
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) (L N : ℕ) :
    ∃ C : ℝ≥0, ∀ R : ℝ≥0, ∀ a : ℝ, ∀ ha : 0 < a, 1 ≤ a →
      ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
      ∀ u : Rotations (m + 1), ∀ x : EuclideanSpace ℝ (Fin m),
      2 * ((R : ℝ) + 1) ≤ ‖x‖ →
        ‖frameLineIntegral v b (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
          (normalizedDilation a ha ψ) f) u x‖ₑ ≤
            ENNReal.ofReal ((C : ℝ) * (a ^ L)⁻¹ * ((1 + ‖x‖) ^ N)⁻¹) *
              eLpNorm f 1 volume := by
  obtain ⟨C, hC⟩ := exists_lintegral_enorm_dilation_sub_frame_tail v b ψ L N
  refine ⟨C, fun R a ha ha₁ f hs u x hx ↦ ?_⟩
  simp only [frameLineIntegral, SchwartzMap.convolution_apply]
  apply enorm_integral_convolution_le_of_support f.continuous.measurable
    (normalizedDilation a ha ψ).continuous.measurable (by fun_prop)
  intro z hz
  exact hC R a ha ha₁ u x hx z (by simpa only [mem_closedBall, dist_zero_right] using hs hz)

end NKBesicovitch.XRay
