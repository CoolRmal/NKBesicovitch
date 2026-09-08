/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.FourierFrame
public import NKBesicovitch.Operators.Fourier.PolynomialSupport

/-!
# Bandlimited weighted X-ray fibers

Fourier slicing preserves the ambient frequency radius on every transverse
fiber. Multiplication by the polynomial transverse weight preserves that
radius and the Schwartz class.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap FourierTransform

namespace NKBesicovitch.XRay

variable {n m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- Each polynomially weighted X-ray fiber is Schwartz with the same Fourier radius as the input. -/
theorem exists_weighted_schwartz_frameLineIntegral_bandlimited
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {R : ℝ}
    (hf : tsupport (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ⊆ closedBall 0 R)
    (u : Rotations n) (A : ℕ) :
    ∃ g : 𝓢(EuclideanSpace ℝ (Fin m), ℂ),
      (∀ x, g x = (1 + ‖x‖ ^ 2) ^ A • frameLineIntegral v b f u x) ∧
        tsupport (𝓕 g : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) ⊆ closedBall 0 R := by
  obtain ⟨g, hg⟩ := exists_schwartz_frameLineIntegral v b f u
  have he : (g : EuclideanSpace ℝ (Fin m) → ℂ) = frameLineIntegral v b f u := funext hg
  have hs : tsupport (𝓕 g : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) ⊆ closedBall 0 R := by
    apply closure_minimal ?_ isClosed_closedBall
    intro ξ hξ
    have hξ' : 𝓕 f (Unitary.linearIsometryEquiv u (b ξ : EuclideanSpace ℝ (Fin n))) ≠ 0 := by
      simpa only [Function.mem_support, SchwartzMap.fourier_coe, he,
        fourier_frameLineIntegral v b f.integrable] using hξ
    have h := hf (subset_tsupport _ hξ')
    simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map, Submodule.norm_coe] using h
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x ↦ (1 + ‖x‖ ^ 2) ^ A) g, ?_,
    (tsupport_fourier_smulLeftCLM_one_add_norm_sq_pow_subset g A).trans hs⟩
  intro x
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), hg]

end NKBesicovitch.XRay
