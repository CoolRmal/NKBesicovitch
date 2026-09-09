/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Fourier.PlaneKernelBound
public import NKBesicovitch.Operators.Fourier.PlaneKernelPairing
public import NKBesicovitch.Operators.Fourier.FrequencyKernels

/-!
# Full-plane bounds for bandlimited functions

For Fourier support in a fixed multiple of the inverse-thickness ball,
the full absolute plane integral is bounded by the plate maximum of a
polynomially weighted input. The weight degree must exceed half the plane
dimension. The constant is uniform in thickness, direction, and translation.
-/

public section

open MeasureTheory SchwartzMap Set Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform

namespace NKBesicovitch

private lemma exists_lintegral_plane_le_plateMaximal_aux {n k A : ℕ} {R : ℝ}
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (hφ : ∀ ξ, ‖ξ‖ ≤ R → 𝓕 φ ξ = 1) (hA : k < 2 * A) :
    ∃ C : ℝ≥0, ∀ (a : ℝ), 0 < a → ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      tsupport (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ⊆ closedBall 0 (a * R) →
        ∀ (V : Grassmannian n k) (x : EuclideanSpace ℝ (Fin n)),
          (∫⁻ w : V.val, ‖f (x + w)‖ₑ) ≤
            C * plateMaximal a⁻¹ (fun y ↦ ‖(1 + ‖y‖ ^ 2) ^ A • f y‖ₑ) V := by
  obtain ⟨B, hB⟩ := exists_norm_normalizedDilation_le φ (n + 1)
  obtain ⟨D, hD⟩ := exists_lintegral_mul_weightedPlaneKernel_le hA
    (show n < 2 * (n + 1) by omega)
  refine ⟨B * D, fun a ha f hf V x ↦ ?_⟩
  let g := smulLeftCLM ℂ (fun y : EuclideanSpace ℝ (Fin n) ↦ (1 + ‖y‖ ^ 2) ^ A) f
  have h := lintegral_plane_le_weightedPlaneKernel φ f ha hφ hf (hB a ha) V.val A x
  have hd := hD V a ha x (fun z ↦ ‖g z‖ₑ) g.continuous.measurable.enorm
  simpa only [ENNReal.coe_mul, mul_assoc, g, smulLeftCLM_apply_apply (by fun_prop :
    (fun y : EuclideanSpace ℝ (Fin n) ↦ (1 + ‖y‖ ^ 2) ^ A).HasTemperateGrowth)] using
      h.trans (mul_le_mul_right hd (B : ℝ≥0∞))

/-- Polynomial weights let local plate averages control full integrals of bandlimited inputs. -/
theorem exists_lintegral_plane_le_plateMaximal_of_bandlimited {n k A : ℕ}
    (hA : k < 2 * A) (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0, ∀ (a : ℝ), 0 < a → ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      tsupport (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ⊆ closedBall 0 (a * R) →
        ∀ (V : Grassmannian n k) (x : EuclideanSpace ℝ (Fin n)),
          (∫⁻ w : V.val, ‖f (x + w)‖ₑ) ≤
            C * plateMaximal a⁻¹ (fun y ↦ ‖(1 + ‖y‖ ^ 2) ^ A • f y‖ₑ) V := by
  obtain ⟨ψ, hψ, -, -⟩ := exists_lowFrequencyKernel (E := EuclideanSpace ℝ (Fin n))
  apply exists_lintegral_plane_le_plateMaximal_aux (normalizedDilation R hR ψ) ?_ hA
  intro ξ hξ
  rw [fourier_normalizedDilation, hψ]
  rw [norm_smul, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul]
  exact (div_le_one hR).mpr hξ

end NKBesicovitch
