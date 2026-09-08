/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.FourierFrame
public import NKBesicovitch.Operators.Fourier.Dilation

/-!
# Dilation of a signed line integral

Normalized ambient dilation scales a line integral by `a^(n-1)` and
its transverse displacement by `a`. The missing power of `a` is exactly
the one-dimensional change of variables along the line.
-/

public section

open MeasureTheory Submodule Metric
open scoped SchwartzMap

namespace NKBesicovitch.XRay

variable {n m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- Scalar change of variables along a rotated line, with arbitrary integrand. -/
theorem integral_comp_smul_frame {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : ℝ) (ha : 0 < a) (f : EuclideanSpace ℝ (Fin n) → F) (u : Rotations n)
    (x : EuclideanSpace ℝ (Fin m)) :
    (∫ t : ℝ, f (a • Unitary.linearIsometryEquiv u
      (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)))) =
        a⁻¹ • ∫ t : ℝ, f (Unitary.linearIsometryEquiv u
          (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (a • x, t))) := by
  have he (t : ℝ) : a • Unitary.linearIsometryEquiv u
      (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)) =
      Unitary.linearIsometryEquiv u
        (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (a • x, a * t)) := by
    simp only [normalCoordinatesWithBasis_apply, map_add, map_smul, smul_add, smul_smul,
      Submodule.coe_smul]
  simp_rw [he]
  have hi := Measure.integral_comp_smul_of_nonneg volume
    (fun t : ℝ ↦ f (Unitary.linearIsometryEquiv u
      (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (a • x, t)))) a (hR := ha.le)
  simpa only [Module.finrank_self, pow_one, smul_eq_mul] using hi

/-- The exact change of variables for a normalized dilated Schwartz kernel. -/
theorem frameLineIntegral_normalizedDilation (a : ℝ) (ha : 0 < a)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (u : Rotations n)
    (x : EuclideanSpace ℝ (Fin m)) :
    frameLineIntegral v b (normalizedDilation a ha f) u x =
      (a ^ n * a⁻¹) • frameLineIntegral v b f u (a • x) := by
  simp only [frameLineIntegral, normalizedDilation_apply, finrank_euclideanSpace,
    Fintype.card_fin, integral_smul]
  rw [integral_comp_smul_frame v b a ha, smul_smul]

/-- The same scaling identity holds for the integral of the absolute kernel. -/
theorem integral_norm_frameLineIntegrand_normalizedDilation (a : ℝ) (ha : 0 < a)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (u : Rotations n)
    (x : EuclideanSpace ℝ (Fin m)) :
    (∫ t : ℝ, ‖normalizedDilation a ha f (Unitary.linearIsometryEquiv u
      (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)))‖) =
        (a ^ n * a⁻¹) * ∫ t : ℝ, ‖f (Unitary.linearIsometryEquiv u
          (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (a • x, t)))‖ := by
  simp only [normalizedDilation_apply, norm_smul, finrank_euclideanSpace, Fintype.card_fin,
    Real.norm_of_nonneg (pow_nonneg ha.le n), integral_const_mul]
  rw [integral_comp_smul_frame v b a ha (fun z ↦ ‖f z‖), smul_eq_mul, mul_assoc]

end NKBesicovitch.XRay
