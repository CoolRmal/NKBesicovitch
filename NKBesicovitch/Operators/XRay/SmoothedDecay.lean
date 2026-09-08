/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.SmoothedBound
public import NKBesicovitch.Operators.Interpolation.Schwartz

/-!
# The interpolated frequency gain for the smoothed X-ray transform

For input supported in a fixed ball and every `p ≥ 2`, smoothing at frequency
scale `a > 0` gives joint `Lᵖ` decay `a^(-1/p)`. The fixed Schwartz kernel
only needs a Fourier gap at the origin. The interpolation constant is finite
and uniform over the frequency scale and the supported Schwartz input.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.XRay

variable {m : ℕ} [Nonempty (Fin m)]
  (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- The smoothed signed X-ray transform gains `1/p` derivatives on fixed bounded support. -/
theorem exists_eLpNorm_frameLineIntegral_dilation_decay
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ))
    (hgap : ∀ ξ, ‖ξ‖ < 1 → 𝓕 ψ ξ = 0) (R : ℝ≥0) {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ≥0, ∀ a : ℝ, ∀ ha : 0 < a, ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
        eLpNorm (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
          frameLineIntegral v b (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
            (normalizedDilation a ha ψ) f) z.1 z.2)
          (ENNReal.ofReal p) ((Rotations.probability (m + 1)).prod volume) ≤
            C * (ENNReal.ofReal a) ^ (-1 / p : ℝ) * eLpNorm f (ENNReal.ofReal p) volume := by
  let K : ℝ≥0 := ⟨SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ), apply_nonneg _ _⟩
  have hK (ξ : EuclideanSpace ℝ (Fin (m + 1))) : ‖𝓕 ψ ξ‖ₑ ≤ K := by
    rw [← ofReal_norm, ENNReal.ofReal_le_coe]
    exact (𝓕 ψ).norm_le_seminorm ℝ ξ
  obtain ⟨H, hH⟩ := exists_eLpNorm_frameLineIntegral_dilation_bounds v b
  rcases eq_or_lt_of_le hp with rfl | hp
  · refine ⟨H * K, fun a ha f hs ↦ ?_⟩
    simpa only [ENNReal.ofReal_ofNat, ENNReal.coe_mul] using (hH a ha K f ψ R hs hgap hK).1
  let B : ℝ := 2 * (R : ℝ) * (eLpNorm ψ 1 volume).toReal + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨C, hC⟩ := exists_eLpNorm_decay_of_endpoints
    (E := EuclideanSpace ℝ (Fin (m + 1)))
    ((Rotations.probability (m + 1)).prod (volume : Measure (EuclideanSpace ℝ (Fin m))))
    hB hp (H * K)
  refine ⟨C, fun a ha f hs ↦ ?_⟩
  let T : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ) →+
      (Rotations (m + 1) × EuclideanSpace ℝ (Fin m) → ℂ) :=
    ((frameLineIntegralLinearMap v b).comp
      (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
        (normalizedDilation a ha ψ)).toLinearMap).toAddMonoidHom
  refine hC a ha T (closedBall 0 R) ?_ ?_ ?_ f
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R) hs) hs
  · intro g
    exact (measurable_frameLineIntegral v b
      (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
        (normalizedDilation a ha ψ) g).continuous.measurable).aestronglyMeasurable
  · intro g hg
    simpa only [T, LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp,
      ContinuousLinearMap.coe_coe, Function.comp_def, frameLineIntegralLinearMap_apply,
      ENNReal.coe_mul] using (hH a ha K g ψ R hg hgap hK).1
  · intro g hg r hr hgr
    apply ae_of_all
    intro z
    have h := norm_frameLineIntegral_convolution_le_of_bound v b g
      (normalizedDilation a ha ψ) hg hr hgr z.1 z.2
    rw [eLpNorm_normalizedDilation_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) hr)

end NKBesicovitch.XRay
