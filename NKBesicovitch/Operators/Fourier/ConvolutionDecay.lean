/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Fourier.Dilation
public import NKBesicovitch.Operators.PolynomialWeight
public import Mathlib.Analysis.Fourier.Convolution

/-!
# Uniform spatial decay of smooth approximations

Convolution with normalized dilations of a fixed Schwartz kernel preserves
polynomial spatial decay, with constants uniform over all scales at least one.
-/

public section

open MeasureTheory SchwartzMap
open scoped SchwartzMap NNReal

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem convolution_normalizedDilation_eq (φ f : 𝓢(E, ℂ)) (a : ℝ) (ha : 0 < a) (x : E) :
    SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) (normalizedDilation a ha φ) f x =
      ∫ y : E, φ y * f (x - a⁻¹ • y) := by
  rw [SchwartzMap.convolution_apply, convolution_lsmul]
  simp only [normalizedDilation_apply, smul_eq_mul, smul_mul_assoc, integral_smul]
  have h := Measure.integral_comp_smul_of_nonneg volume
    (fun y : E ↦ φ y * f (x - a⁻¹ • y)) a (hR := ha.le)
  simp only [inv_smul_smul₀ ha.ne'] at h
  rw [h, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma weighted_convolution_integrand_le_aux (φ f : 𝓢(E, ℂ)) (A : ℕ)
    {a : ℝ} (ha : 1 ≤ a) (x y : E) :
    (1 + ‖x‖ ^ 2) ^ A * ‖φ y * f (x - a⁻¹ • y)‖ ≤
      (2 ^ A * SchwartzMap.seminorm ℂ 0 0
        (smulLeftCLM ℂ (fun z : E ↦ (1 + ‖z‖ ^ 2) ^ A) f)) *
          ‖smulLeftCLM ℂ (fun z : E ↦ (1 + ‖z‖ ^ 2) ^ A) φ y‖ := by
  have hw : (fun z : E ↦ (1 + ‖z‖ ^ 2) ^ A).HasTemperateGrowth := by fun_prop
  have hs := norm_le_seminorm ℂ (smulLeftCLM ℂ (fun z : E ↦ (1 + ‖z‖ ^ 2) ^ A) f)
    (x - a⁻¹ • y)
  simp only [smulLeftCLM_apply_apply hw, norm_smul] at hs ⊢
  rw [Real.norm_of_nonneg (by positivity)] at hs
  rw [Real.norm_of_nonneg (by positivity)]
  have hy : ‖a⁻¹ • y‖ ≤ ‖y‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (norm_nonneg y) (inv_le_one_of_one_le₀ ha)
  have hx := one_add_norm_sq_pow_add_le (x - a⁻¹ • y) (a⁻¹ • y) A
  rw [sub_add_cancel] at hx
  have hp : (1 + ‖a⁻¹ • y‖ ^ 2) ^ A ≤ (1 + ‖y‖ ^ 2) ^ A := by gcongr
  rw [norm_mul]
  calc
    _ ≤ (2 ^ A * (1 + ‖x - a⁻¹ • y‖ ^ 2) ^ A * (1 + ‖y‖ ^ 2) ^ A) *
        (‖φ y‖ * ‖f (x - a⁻¹ • y)‖) := by gcongr; exact hx.trans (by gcongr)
    _ ≤ _ := by
      convert! mul_le_mul_of_nonneg_left hs
        (show 0 ≤ 2 ^ A * (1 + ‖y‖ ^ 2) ^ A * ‖φ y‖ by positivity) using 1 <;> ring

/-- Smooth approximations have polynomial spatial decay uniformly in the dilation scale. -/
theorem exists_norm_convolution_normalizedDilation_le (φ f : 𝓢(E, ℂ)) (A : ℕ) :
    ∃ C : ℝ≥0, ∀ (a : ℝ) (ha : 0 < a), 1 ≤ a → ∀ x : E,
      ‖SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
        (normalizedDilation a ha φ) f x‖ ≤ C * ((1 + ‖x‖ ^ 2) ^ A)⁻¹ := by
  let wφ := smulLeftCLM ℂ (fun z : E ↦ (1 + ‖z‖ ^ 2) ^ A) φ
  let B := 2 ^ A * SchwartzMap.seminorm ℂ 0 0
    (smulLeftCLM ℂ (fun z : E ↦ (1 + ‖z‖ ^ 2) ^ A) f)
  refine ⟨NNReal.mk (B * ∫ y : E, ‖wφ y‖) (by positivity), fun a ha ha₁ x ↦ ?_⟩
  rw [NNReal.coe_mk, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
    convolution_normalizedDilation_eq, mul_comm]
  have h := norm_integral_le_of_norm_le (μ := volume) (wφ.integrable.norm.const_mul B)
    (ae_of_all _ fun y ↦ ?_ : ∀ᵐ y : E, ‖(1 + ‖x‖ ^ 2) ^ A •
      (φ y * f (x - a⁻¹ • y))‖ ≤ B * ‖wφ y‖)
  · simpa only [integral_smul, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖ ^ 2) ^ A),
      integral_const_mul] using h
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact weighted_convolution_integrand_le_aux φ f A ha₁ x y

end NKBesicovitch
