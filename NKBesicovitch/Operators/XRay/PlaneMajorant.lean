/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.PlateMajorant
public import NKBesicovitch.Operators.XRay.PlaneIntegral

/-!
# Plate majorants for signed flag-plane integrals

Signed flag Fubini is applied before taking absolute values. The resulting
bandlimited transverse integral is controlled by a weighted plate maximum,
uniformly over every translation of the full ambient plane.
-/

public section

open MeasureTheory Submodule Set Metric NKBesicovitch.Grassmannian
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.XRay

variable {n m k : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- Signed flag-plane integrals of bandlimited functions admit translation-uniform majorants. -/
theorem exists_enorm_integral_flag_le_plateMaximal {A : ℕ} (hA : k < 2 * A)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0, ∀ (a : ℝ), 0 < a → ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      tsupport (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ⊆ closedBall 0 (a * R) →
        ∀ (z : Rotations n × Grassmannian m k) (x : EuclideanSpace ℝ (Fin n)),
          ‖∫ w : (flagDirection (norm_eq_of_mem_sphere v) b z).val, f (x + w)‖ₑ ≤
            C * plateMaximal a⁻¹
              (fun y ↦ ‖(1 + ‖y‖ ^ 2) ^ A • frameLineIntegral v b f z.1 y‖ₑ) z.2 := by
  obtain ⟨C, hC⟩ := exists_lintegral_frameLineIntegral_le_plateMaximal v b hA R hR
  refine ⟨C, fun a ha f hf z x ↦ ?_⟩
  obtain ⟨x', rfl⟩ := (Unitary.linearIsometryEquiv z.1).surjective x
  obtain ⟨c, rfl⟩ := (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b).surjective x'
  rw [integral_flagDirection_eq]
  exact (enorm_integral_le_lintegral_enorm _).trans (hC a ha f hf z.1 z.2 c.1)

end NKBesicovitch.XRay
