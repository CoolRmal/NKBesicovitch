/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Fourier.DyadicDecomposition
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Reproducing kernels for bandlimited Schwartz functions

A dilated cutoff reproduces any Schwartz function whose closed Fourier
support lies in the region where the multiplier is one. Polynomial decay
of the fixed kernel provides a positive majorant at every dilation scale.
-/

public section

open MeasureTheory SchwartzMap FourierTransform Set Metric
open scoped SchwartzMap FourierTransform NNReal ENNReal

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A smooth Fourier cutoff reproduces every Schwartz function supported in its inner ball. -/
theorem convolution_normalizedDilation_eq_self (φ f : 𝓢(E, ℂ)) {R a : ℝ} (ha : 0 < a)
    (hφ : ∀ ξ : E, ‖ξ‖ ≤ R → 𝓕 φ ξ = 1)
    (hf : tsupport (𝓕 f : 𝓢(E, ℂ)) ⊆ closedBall 0 (a * R)) :
    SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) (normalizedDilation a ha φ) f = f := by
  apply (fourierCLE ℂ 𝓢(E, ℂ)).injective
  ext ξ
  change 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
    (normalizedDilation a ha φ) f) ξ = 𝓕 f ξ
  rw [fourier_convolution_normalizedDilation]
  by_cases hξ : ξ ∈ tsupport (𝓕 f : 𝓢(E, ℂ))
  · rw [hφ _ ?_, one_mul]
    rw [norm_smul, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul]
    exact (div_le_iff₀ ha).mpr (by simpa only [mem_closedBall_zero_iff, mul_comm] using hf hξ)
  · rw [image_eq_zero_of_notMem_tsupport hξ, mul_zero]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Every normalized Schwartz dilation admits a uniformly scaled polynomial majorant. -/
theorem exists_norm_normalizedDilation_le (φ : 𝓢(E, ℂ)) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ (a : ℝ) (ha : 0 < a) (x : E),
      ‖normalizedDilation a ha φ x‖ ≤
        C * a ^ Module.finrank ℝ E * ((1 + ‖a • x‖ ^ 2) ^ N)⁻¹ := by
  let g := smulLeftCLM ℂ (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ N) φ
  refine ⟨NNReal.mk (SchwartzMap.seminorm ℂ 0 0 g) (apply_nonneg _ _), fun a ha x ↦ ?_⟩
  have hg := norm_le_seminorm ℂ g (a • x)
  change ‖smulLeftCLM ℂ (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ N) φ (a • x)‖ ≤
    SchwartzMap.seminorm ℂ 0 0 g at hg
  rw [smulLeftCLM_apply_apply (by fun_prop :
    (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ N).HasTemperateGrowth), norm_smul,
    Real.norm_of_nonneg (by positivity)] at hg
  rw [normalizedDilation_apply, norm_smul, Real.norm_of_nonneg (by positivity), NNReal.coe_mk,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hg (pow_nonneg ha.le (Module.finrank ℝ E))]

/-- A bandlimited input is bounded pointwise by convolution with a positive polynomial profile. -/
theorem enorm_le_polynomial_convolution (φ f : 𝓢(E, ℂ)) {R a : ℝ} (ha : 0 < a)
    (hφ : ∀ ξ : E, ‖ξ‖ ≤ R → 𝓕 φ ξ = 1)
    (hf : tsupport (𝓕 f : 𝓢(E, ℂ)) ⊆ closedBall 0 (a * R)) {N : ℕ} {C : ℝ≥0}
    (hC : ∀ z, ‖normalizedDilation a ha φ z‖ ≤
      C * a ^ Module.finrank ℝ E * ((1 + ‖a • z‖ ^ 2) ^ N)⁻¹) (y : E) :
    ‖f y‖ₑ ≤ C * ENNReal.ofReal (a ^ Module.finrank ℝ E) *
      ∫⁻ z, ‖f z‖ₑ * ENNReal.ofReal (((1 + ‖a • (y - z)‖ ^ 2) ^ N)⁻¹) := by
  have h : ‖f y‖ₑ ≤ ∫⁻ z, ‖f z‖ₑ * ‖normalizedDilation a ha φ (y - z)‖ₑ := by
    nth_rw 1 [← convolution_normalizedDilation_eq_self φ f ha hφ hf]
    rw [SchwartzMap.convolution_apply, convolution_lsmul_swap]
    simpa only [smul_eq_mul, enorm_mul, mul_comm] using
      enorm_integral_le_lintegral_enorm (fun z ↦ f z * normalizedDilation a ha φ (y - z))
  refine h.trans ((lintegral_mono (g := fun z ↦ C * ENNReal.ofReal (a ^ Module.finrank ℝ E) *
    (‖f z‖ₑ * ENNReal.ofReal (((1 + ‖a • (y - z)‖ ^ 2) ^ N)⁻¹))) fun z ↦ ?_).trans_eq ?_)
  · have hb := ENNReal.ofReal_le_ofReal (hC (y - z))
    rw [ofReal_norm, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal] at hb
    exact (mul_le_mul_right hb (‖f z‖ₑ)).trans_eq (by ac_rfl)
  · exact lintegral_const_mul' _ _ (by finiteness)

end NKBesicovitch
