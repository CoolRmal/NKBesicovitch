/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Normalized dilation of smoothing kernels

The dilation `a^dim • f (a • x)`, for `a > 0`, preserves the one-norm.
Its Fourier transform is `𝓕 f (a⁻¹ • ξ)`, so a fixed Fourier gap scales
linearly while uniform multiplier bounds remain unchanged.
-/

public section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Dilation normalized to preserve the integral and the one-norm of a smoothing kernel. -/
@[expose] noncomputable def normalizedDilation (a : ℝ) (ha : 0 < a)
    (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  (a ^ Module.finrank ℝ E) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Units.mk0 a ha.ne' • ContinuousLinearEquiv.refl ℝ E) f

@[simp] theorem normalizedDilation_apply (a : ℝ) (ha : 0 < a) (f : 𝓢(E, ℂ)) (x : E) :
    normalizedDilation a ha f x = (a ^ Module.finrank ℝ E) • f (a • x) := rfl

@[simp] theorem normalizedDilation_one (f : 𝓢(E, ℂ)) : normalizedDilation 1 zero_lt_one f = f := by
  ext x
  simp only [normalizedDilation_apply, one_pow, one_smul]

@[simp] theorem normalizedDilation_sub (a : ℝ) (ha : 0 < a) (f g : 𝓢(E, ℂ)) :
    normalizedDilation a ha (f - g) = normalizedDilation a ha f - normalizedDilation a ha g := by
  ext x
  simp only [normalizedDilation_apply, sub_apply, smul_sub]

theorem normalizedDilation_mul (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (f : 𝓢(E, ℂ)) :
    normalizedDilation a ha (normalizedDilation b hb f) =
      normalizedDilation (a * b) (mul_pos ha hb) f := by
  ext x
  simp only [normalizedDilation_apply, smul_smul, mul_pow, mul_comm]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem eLpNorm_normalizedDilation_one (a : ℝ) (ha : 0 < a) (f : 𝓢(E, ℂ)) :
    eLpNorm (normalizedDilation a ha f) 1 volume = eLpNorm f 1 volume := by
  simp only [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (normalizedDilation a ha f).integrable,
    ← ofReal_integral_norm_eq_lintegral_enorm f.integrable]
  congr 1
  simp only [normalizedDilation_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos ha _), integral_const_mul]
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x ↦ ‖f x‖) a (hR := ha.le)]
  simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]

theorem fourier_normalizedDilation (a : ℝ) (ha : 0 < a) (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (normalizedDilation a ha f) ξ = 𝓕 f (a⁻¹ • ξ) := by
  simp only [SchwartzMap.fourier_coe, Real.fourier_eq, normalizedDilation_apply]
  simp_rw [smul_comm _ (a ^ Module.finrank ℝ E), integral_smul]
  rw [← Measure.integral_comp_inv_smul_of_nonneg volume _ ha.le]
  simp only [real_inner_smul_left, real_inner_smul_right, smul_inv_smul₀ ha.ne']

end NKBesicovitch
