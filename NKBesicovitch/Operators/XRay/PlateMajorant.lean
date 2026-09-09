/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.FrameContinuity
public import NKBesicovitch.Operators.XRay.Bandlimited
public import NKBesicovitch.Operators.PlateContinuousFamily
public import NKBesicovitch.Operators.Fourier.BandlimitedPlane

/-!
# Measurable plate majorants for signed X-ray integrals

Bandlimited X-ray fibers admit full-plane bounds by their polynomially
weighted plate maxima. These majorants are jointly Borel in the frame
and the lower-dimensional plane, so their frequency sums can be integrated.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.XRay

variable {n m k : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- Weighted plate maxima of a Schwartz X-ray transform are jointly Borel. -/
theorem measurable_plateMaximal_weighted_frameLineIntegral {δ : ℝ} (hδ : 0 < δ)
    (A : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Measurable (fun z : Rotations n × Grassmannian m k ↦
      plateMaximal δ (fun x ↦ ‖(1 + ‖x‖ ^ 2) ^ A • frameLineIntegral v b f z.1 x‖ₑ) z.2) := by
  apply (lowerSemicontinuous_plateMaximal_family (f :=
    fun z ↦ ‖(1 + ‖z.2‖ ^ 2) ^ A • frameLineIntegral v b f z.1 z.2‖ₑ) hδ ?_).measurable
  exact ((show Continuous (fun z : Rotations n × EuclideanSpace ℝ (Fin m) ↦
    (1 + ‖z.2‖ ^ 2) ^ A) by fun_prop).smul (continuous_frameLineIntegral v b f)).enorm

/-- Full-plane integrals of bandlimited signed X-ray fibers have uniform plate majorants. -/
theorem exists_lintegral_frameLineIntegral_le_plateMaximal {A : ℕ} (hA : k < 2 * A)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0, ∀ (a : ℝ), 0 < a → ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      tsupport (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ⊆ closedBall 0 (a * R) →
        ∀ (u : Rotations n) (V : Grassmannian m k) (x : EuclideanSpace ℝ (Fin m)),
          (∫⁻ w : V.val, ‖frameLineIntegral v b f u (x + w)‖ₑ) ≤
            C * plateMaximal a⁻¹
              (fun y ↦ ‖(1 + ‖y‖ ^ 2) ^ A • frameLineIntegral v b f u y‖ₑ) V := by
  obtain ⟨C, hC⟩ := exists_lintegral_plane_le_plateMaximal_of_bandlimited hA R hR
  refine ⟨C, fun a ha f hf u V x ↦ ?_⟩
  obtain ⟨g, hg, hs⟩ := exists_weighted_schwartz_frameLineIntegral_bandlimited v b f hf u 0
  simpa only [hg, pow_zero, one_smul] using hC a ha g hs V x

end NKBesicovitch.XRay
