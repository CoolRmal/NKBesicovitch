/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Fourier.ConvolutionDecay
public import NKBesicovitch.Operators.Fourier.DyadicConvergence

/-!
# Convergence of smooth approximations on full affine planes

Uniform spatial decay gives an integrable bound on every translated linear
isometric image. Dominated convergence therefore applies to the signed
integrals over the entire plane, with no truncation of its unbounded directions.
-/

public section

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology NNReal

namespace NKBesicovitch

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- One integrable function bounds all smooth approximations on a fixed full affine plane. -/
theorem exists_integrable_bound_convolution_normalizedDilation_affine (φ f : 𝓢(E, ℂ))
    (e : F →ₗᵢ[ℝ] E) (x : E) :
    ∃ g : F → ℝ, Integrable g volume ∧ ∀ (a : ℝ) (ha : 0 < a), 1 ≤ a → ∀ y : F,
      ‖SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
        (normalizedDilation a ha φ) f (x + e y)‖ ≤ g y := by
  let A := Module.finrank ℝ F + 1
  obtain ⟨C, hC⟩ := exists_norm_convolution_normalizedDilation_le φ f A
  have hI : Integrable (fun y : F ↦ ((1 + ‖y‖ ^ 2) ^ A)⁻¹) volume := by
    have hA : (Module.finrank ℝ F : ℝ) < 2 * (A : ℝ) := by
      dsimp [A]
      push_cast
      linarith [Nat.cast_nonneg (Module.finrank ℝ F) (α := ℝ)]
    convert! integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure F)) hA using 1
    ext y
    rw [show -(2 * (A : ℝ)) / 2 = -(A : ℝ) by ring,
      Real.rpow_neg (by positivity), Real.rpow_natCast]
  refine ⟨fun y ↦ (C * (2 ^ A * (1 + ‖x‖ ^ 2) ^ A)) * ((1 + ‖y‖ ^ 2) ^ A)⁻¹,
    hI.const_mul _, fun a ha ha₁ y ↦ (hC a ha ha₁ (x + e y)).trans ?_⟩
  have h := inv_one_add_norm_sq_pow_add_le x (e y) A
  rw [e.norm_map] at h
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h C.coe_nonneg

/-- Signed integrals of smooth dyadic approximations converge on every full affine plane. -/
theorem tendsto_integral_convolution_dyadic_affine (φ f : 𝓢(E, ℂ))
    (hφ : ∀ ξ : E, ‖ξ‖ ≤ 1 → 𝓕 φ ξ = 1) (hbound : ∀ ξ : E, ‖𝓕 φ ξ‖ ≤ 1)
    (e : F →ₗᵢ[ℝ] E) (x : E) :
    Tendsto (fun N : ℕ ↦ ∫ y : F,
      SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
        (normalizedDilation ((2 : ℝ) ^ N) (pow_pos two_pos N) φ) f (x + e y))
      atTop (𝓝 (∫ y : F, f (x + e y))) := by
  obtain ⟨g, hg, hgf⟩ := exists_integrable_bound_convolution_normalizedDilation_affine φ f e x
  apply tendsto_integral_of_dominated_convergence g (fun N ↦ ?_) hg
    (fun N ↦ ae_of_all _ (hgf _ _ (one_le_pow₀ one_le_two)))
    (ae_of_all _ fun y ↦ (tendstoUniformly_convolution_dyadic φ f hφ hbound).tendsto_at (x + e y))
  exact ((SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
    (normalizedDilation ((2 : ℝ) ^ N) (pow_pos two_pos N) φ) f).continuous.comp
      (continuous_const.add e.continuous)).aestronglyMeasurable

end NKBesicovitch
