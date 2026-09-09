/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.PlaneMajorant
public import NKBesicovitch.Operators.Fourier.PlaneDecomposition
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A measurable dyadic majorant for all affine flag planes

The majorant is the sum of the weighted plate maximum of the low-frequency
piece and those of all annular pieces at their corresponding thicknesses.
It controls signed full-plane integrals uniformly over translations.
-/

@[expose] public section

open MeasureTheory Submodule Set Metric NKBesicovitch.Grassmannian
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.XRay

variable {n m k : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- The sum of the weighted low-frequency and annular plate majorants in a flag frame. -/
noncomputable def dyadicFrameMajorant (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (A : ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (z : Rotations n × Grassmannian m k) : ℝ≥0∞ :=
  plateMaximal 1 (fun x ↦ ‖(1 + ‖x‖ ^ 2) ^ A • frameLineIntegral v b
    (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) φ f) z.1 x‖ₑ) z.2 +
    ∑' j : ℕ, plateMaximal ((2 : ℝ) ^ j)⁻¹
      (fun x ↦ ‖(1 + ‖x‖ ^ 2) ^ A • frameLineIntegral v b
        (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
          (normalizedDilation ((2 : ℝ) ^ j) (pow_pos two_pos j)
            (normalizedDilation 2 two_pos φ - φ)) f) z.1 x‖ₑ) z.2

theorem measurable_dyadicFrameMajorant (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (A : ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Measurable (dyadicFrameMajorant v b φ A f (k := k)) :=
  (measurable_plateMaximal_weighted_frameLineIntegral v b zero_lt_one A _).add
    (Measurable.tsum fun j ↦
      measurable_plateMaximal_weighted_frameLineIntegral v b (by positivity) A _)

omit v b in
private lemma convolution_fourier_radius_aux (ψ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    {R a : ℝ} (ha : 0 < a) (hψ : ∀ ξ, R ≤ ‖ξ‖ → 𝓕 ψ ξ = 0) :
    tsupport (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
      (normalizedDilation a ha ψ) f) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ⊆
        closedBall 0 (a * R) := by
  apply closure_minimal ?_ isClosed_closedBall
  intro ξ hξ
  apply tsupport_fourier_normalizedDilation_subset ψ hψ a ha
  apply subset_tsupport
  intro he
  apply hξ
  change 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
    (normalizedDilation a ha ψ) f) ξ = 0
  rw [fourier_convolution_normalizedDilation]
  rw [fourier_normalizedDilation] at he
  rw [he, zero_mul]

/-- Every signed full-plane integral is bounded by the same measurable dyadic majorant. -/
theorem exists_enorm_integral_flag_le_dyadicFrameMajorant {A : ℕ} (hA : k < 2 * A)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (hφ : ∀ ξ, ‖ξ‖ ≤ 1 → 𝓕 φ ξ = 1) (houter : ∀ ξ, 2 ≤ ‖ξ‖ → 𝓕 φ ξ = 0)
    (hbound : ∀ ξ, ‖𝓕 φ ξ‖ ≤ 1) :
    ∃ C : ℝ≥0, ∀ (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (z : Rotations n × Grassmannian m k) (x : EuclideanSpace ℝ (Fin n)),
        ‖∫ w : (flagDirection (norm_eq_of_mem_sphere v) b z).val, f (x + w)‖ₑ ≤
          C * dyadicFrameMajorant v b φ A f z := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_flag_le_plateMaximal v b hA 4 (by norm_num)
  refine ⟨C, fun f z x ↦ ?_⟩
  let W := flagDirection (norm_eq_of_mem_sphere v) b z
  apply (enorm_integral_affine_le_dyadic_sum φ f hφ hbound W.val.subtypeₗᵢ x).trans
  rw [dyadicFrameMajorant, mul_add, ← ENNReal.tsum_mul_left]
  apply add_le_add
  · have hs := convolution_fourier_radius_aux φ f zero_lt_one
      (fun ξ hξ ↦ houter ξ (by linarith : 2 ≤ ‖ξ‖)) (R := 4)
    simp only [normalizedDilation_one] at hs
    simpa only [inv_one, W, Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply]
      using hC 1 zero_lt_one _ hs z x
  · apply ENNReal.tsum_le_tsum
    intro j
    apply hC ((2 : ℝ) ^ j) (pow_pos two_pos j) _ ?_ z x
    exact convolution_fourier_radius_aux _ f (pow_pos two_pos j)
      (fun _ hξ ↦ fourier_dilation_sub_eq_zero_of_le_norm φ houter hξ)

end NKBesicovitch.XRay
