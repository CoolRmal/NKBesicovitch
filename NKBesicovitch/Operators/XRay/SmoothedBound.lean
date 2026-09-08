/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.ConvolutionBound
public import NKBesicovitch.Operators.XRay.AveragedFourier
public import NKBesicovitch.Operators.Fourier.Convolution
public import NKBesicovitch.Operators.Fourier.Dilation
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Endpoint bounds for the smoothed X-ray transform

For input supported in a fixed ball, the smoothed signed X-ray transform
has a joint infinity-norm bound controlled by the input infinity norm and
the kernel one-norm. Consequently kernels with uniformly bounded one-norm
give an endpoint bound independent of their frequency scale.
The two-norm endpoint gains half a derivative when the Fourier transform
of the smoothing kernel vanishes near zero and is uniformly bounded.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.XRay

variable {n m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

private theorem enorm_le_eLpNorm_top {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Continuous f) (x : EuclideanSpace ℝ (Fin n)) : ‖f x‖ₑ ≤ eLpNorm f ∞ volume := by
  have hc : IsClosed {x | ‖f x‖ₑ ≤ eLpNormEssSup f volume} :=
    isClosed_le hf.enorm continuous_const
  have hd := Measure.dense_of_ae (μ := volume) (ae_le_eLpNormEssSup (f := f))
  simpa only [hc.closure_eq, mem_ofPred_eq, eLpNorm_exponent_top] using hd x

/-- A pointwise bound uniform over all rotated lines. -/
theorem enorm_frameLineIntegral_convolution_le
    (f ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {R : ℝ}
    (hs : Function.support (f : EuclideanSpace ℝ (Fin n) → ℂ) ⊆ closedBall 0 R)
    (u : Rotations n) (x : EuclideanSpace ℝ (Fin m)) :
    ‖frameLineIntegral v b (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f) u x‖ₑ ≤
      ENNReal.ofReal (2 * R) * eLpNorm f ∞ volume * eLpNorm ψ 1 volume := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  simp only [frameLineIntegral, normalCoordinatesWithBasis_apply, map_add, map_smul,
    SchwartzMap.convolution_apply]
  apply enorm_line_convolution_le f.continuous.measurable ψ.continuous.measurable hs
    (enorm_le_eLpNorm_top f.continuous)
  exact (Unitary.linearIsometryEquiv u).norm_map (v : EuclideanSpace ℝ (Fin n)) |>.trans
    (norm_eq_of_mem_sphere v)

/-- The fixed-support infinity-norm estimate depends only on the smoothing kernel's one-norm. -/
theorem eLpNorm_frameLineIntegral_convolution_top_le
    (f ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {R : ℝ}
    (hs : Function.support (f : EuclideanSpace ℝ (Fin n) → ℂ) ⊆ closedBall 0 R) :
    eLpNorm (fun z : Rotations n × EuclideanSpace ℝ (Fin m) ↦
      frameLineIntegral v b (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f) z.1 z.2)
      ∞ ((Rotations.probability n).prod volume) ≤
        ENNReal.ofReal (2 * R) * eLpNorm f ∞ volume * eLpNorm ψ 1 volume := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  exact ae_of_all _ fun z ↦ enorm_frameLineIntegral_convolution_le v b f ψ hs z.1 z.2

variable [Nonempty (Fin m)]
  (w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (c : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (w : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- A bounded convolution multiplier with a Fourier gap has a uniform half-derivative gain. -/
theorem exists_eLpNorm_frameLineIntegral_convolution_two_bound :
    ∃ C : ℝ≥0, ∀ R : ℝ, 0 < R → ∀ B : ℝ≥0,
      ∀ f ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
        (∀ ξ, ‖ξ‖ < R → 𝓕 ψ ξ = 0) → (∀ ξ, ‖𝓕 ψ ξ‖ₑ ≤ B) →
          eLpNorm (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
            frameLineIntegral w c
              (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f) z.1 z.2)
            2 ((Rotations.probability (m + 1)).prod volume) ≤
              (C : ℝ≥0∞) * B * (ENNReal.ofReal R) ^ (-1 / 2 : ℝ) * eLpNorm f 2 volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_frameLineIntegral_bound w c
  refine ⟨C, fun R hR B f ψ hgap hB ↦ ?_⟩
  have h := hC R hR (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f) (by
    intro ξ hξ
    simp only [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
      hgap ξ hξ, map_zero, zero_apply])
  refine h.trans ?_
  calc
    _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal R) ^ (-1 / 2 : ℝ) * (B * eLpNorm f 2 volume) :=
      mul_le_mul' le_rfl (eLpNorm_schwartz_convolution_two_le f ψ B hB)
    _ = _ := by ac_rfl

/-- Normalized dilations of a fixed Fourier-localized kernel have uniform endpoint constants. -/
theorem exists_eLpNorm_frameLineIntegral_dilation_bounds :
    ∃ C : ℝ≥0, ∀ a : ℝ, ∀ ha : 0 < a, ∀ B : ℝ≥0,
      ∀ f ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ), ∀ R : ℝ,
        Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
        (∀ ξ, ‖ξ‖ < 1 → 𝓕 ψ ξ = 0) → (∀ ξ, ‖𝓕 ψ ξ‖ₑ ≤ B) →
          (eLpNorm (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
            frameLineIntegral w c (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
              (normalizedDilation a ha ψ) f) z.1 z.2)
            2 ((Rotations.probability (m + 1)).prod volume) ≤
              (C : ℝ≥0∞) * B * (ENNReal.ofReal a) ^ (-1 / 2 : ℝ) * eLpNorm f 2 volume) ∧
          (eLpNorm (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
            frameLineIntegral w c (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
              (normalizedDilation a ha ψ) f) z.1 z.2)
            ∞ ((Rotations.probability (m + 1)).prod volume) ≤
              ENNReal.ofReal (2 * R) * eLpNorm f ∞ volume * eLpNorm ψ 1 volume) := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_frameLineIntegral_convolution_two_bound w c
  refine ⟨C, fun a ha B f ψ R hs hgap hB ↦ ⟨?_, ?_⟩⟩
  · apply hC a ha B f (normalizedDilation a ha ψ)
    · intro ξ hξ
      rw [fourier_normalizedDilation]
      apply hgap
      simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
      exact (inv_mul_lt_iff₀ ha).mpr (by simpa only [mul_one] using hξ)
    · intro ξ
      rw [fourier_normalizedDilation]
      exact hB _
  · simpa only [eLpNorm_normalizedDilation_one] using
      eLpNorm_frameLineIntegral_convolution_top_le w c f (normalizedDilation a ha ψ) hs

end NKBesicovitch.XRay
