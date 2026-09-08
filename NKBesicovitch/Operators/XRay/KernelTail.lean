/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.KernelDecay
public import NKBesicovitch.Operators.XRay.KernelTranslation

/-!
# Uniform tails after bounded ambient translations

If the ambient translation has norm at most `R` and the transverse
displacement has norm at least `2(R+1)`, its transverse separation stays
outside the unit ball. Projected-kernel tails then retain arbitrary
frequency and spatial decay, uniformly over the translation.
-/

public section

open MeasureTheory Submodule Metric
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch.XRay

private theorem inv_one_add_norm_sub_pow_le {E : Type*} [NormedAddCommGroup E]
    (x z : E) (N : ℕ) (h : 2 * ‖z‖ ≤ ‖x‖) :
    ((1 + ‖x - z‖) ^ N)⁻¹ ≤ (2 : ℝ) ^ N * ((1 + ‖x‖) ^ N)⁻¹ := by
  have hn : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - z) z
  have hw : 1 + ‖x‖ ≤ 2 * (1 + ‖x - z‖) := by nlinarith
  rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hw N

variable {m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- Translations inside the support ball preserve rapid decay at distant transverse points. -/
theorem exists_lintegral_enorm_dilation_sub_frame_tail
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) (L N : ℕ) :
    ∃ C : ℝ≥0, ∀ R : ℝ≥0, ∀ a : ℝ, ∀ ha : 0 < a, 1 ≤ a → ∀ u : Rotations (m + 1),
      ∀ x : EuclideanSpace ℝ (Fin m), 2 * ((R : ℝ) + 1) ≤ ‖x‖ →
      ∀ z : EuclideanSpace ℝ (Fin (m + 1)), ‖z‖ ≤ R →
        (∫⁻ t : ℝ, ‖normalizedDilation a ha ψ (Unitary.linearIsometryEquiv u
          (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)) - z)‖ₑ) ≤
            ENNReal.ofReal ((C : ℝ) * (a ^ L)⁻¹ * ((1 + ‖x‖) ^ N)⁻¹) := by
  obtain ⟨C, hC⟩ := exists_integral_norm_frameLineIntegrand_dilation_tail v b ψ L N
  refine ⟨C * 2 ^ N, fun R a ha ha₁ u x hx z hz ↦ ?_⟩
  let q := ((normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b).symm
    ((Unitary.linearIsometryEquiv u).symm z)).1
  have hq : ‖q‖ ≤ R := by
    exact (norm_normalCoordinatesWithBasis_symm_fst_le (norm_eq_of_mem_sphere v) b _).trans
      (by simpa only [LinearIsometryEquiv.norm_map] using hz)
  have htri : ‖x‖ ≤ ‖x - q‖ + ‖q‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - q) q
  have hsep : 1 ≤ ‖x - q‖ := by nlinarith [R.coe_nonneg]
  have hw := inv_one_add_norm_sub_pow_le x q N (by nlinarith)
  rw [lintegral_sub_frame v b (fun y ↦ ‖normalizedDilation a ha ψ y‖ₑ) u x z]
  change (∫⁻ t : ℝ, ‖normalizedDilation a ha ψ (Unitary.linearIsometryEquiv u
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x - q, t)))‖ₑ) ≤ _
  rw [← ofReal_integral_norm_eq_lintegral_enorm
    (integrable_frameLineIntegrand v b (normalizedDilation a ha ψ) u (x - q))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (C : ℝ) * (a ^ L)⁻¹ * ((1 + ‖x - q‖) ^ N)⁻¹ := hC a ha ha₁ u (x - q) hsep
    _ ≤ (C : ℝ) * (a ^ L)⁻¹ * ((2 : ℝ) ^ N * ((1 + ‖x‖) ^ N)⁻¹) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by
      simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat]
      ring

end NKBesicovitch.XRay
