/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Fourier.DyadicDecomposition
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence of dyadic smooth cutoffs

The Fourier transform of the dyadic approximation eventually agrees with the
input at every fixed frequency. A uniform multiplier bound then gives
convergence of the Fourier error in the one-norm and uniform convergence of
the approximations themselves.
-/

public section

open MeasureTheory Set FourierTransform Filter
open scoped SchwartzMap FourierTransform Topology

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- At each fixed frequency, sufficiently large dyadic cutoffs reproduce the input exactly. -/
theorem eventually_fourier_convolution_dyadic_eq (φ f : 𝓢(E, ℂ))
    (hφ : ∀ ξ : E, ‖ξ‖ ≤ 1 → 𝓕 φ ξ = 1) (ξ : E) :
    ∀ᶠ N : ℕ in atTop, 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
      (normalizedDilation ((2 : ℝ) ^ N) (pow_pos two_pos N) φ) f) ξ = 𝓕 f ξ := by
  filter_upwards [(tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)) ‖ξ‖] with N hN
  rw [fourier_convolution_normalizedDilation, hφ _ ?_, one_mul]
  rw [norm_smul, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul]
  exact (div_le_one (pow_pos two_pos N)).mpr hN

/-- The Fourier errors of bounded smooth cutoffs converge to zero in the one-norm. -/
theorem tendsto_integral_norm_fourier_convolution_dyadic_sub (φ f : 𝓢(E, ℂ))
    (hφ : ∀ ξ : E, ‖ξ‖ ≤ 1 → 𝓕 φ ξ = 1) (hbound : ∀ ξ : E, ‖𝓕 φ ξ‖ ≤ 1) :
    Tendsto (fun N : ℕ ↦ ∫ ξ : E,
      ‖𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
        (normalizedDilation ((2 : ℝ) ^ N) (pow_pos two_pos N) φ) f) ξ - 𝓕 f ξ‖)
      atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := volume) (fun ξ : E ↦ 2 * ‖𝓕 f ξ‖)
    (F := fun N ξ ↦ ‖𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
      (normalizedDilation ((2 : ℝ) ^ N) (pow_pos two_pos N) φ) f) ξ - 𝓕 f ξ‖)
    (f := fun _ ↦ (0 : ℝ)) (fun N ↦ ?_) ((𝓕 f).integrable.norm.const_mul 2)
    (fun N ↦ ae_of_all _ fun ξ ↦ ?_) (ae_of_all _ fun ξ ↦ ?_)
  · simpa only [integral_zero] using h
  · exact ((𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
      (normalizedDilation ((2 : ℝ) ^ N) (pow_pos two_pos N) φ) f) : 𝓢(E, ℂ)).continuous.sub
        (𝓕 f).continuous).norm.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (norm_nonneg _), fourier_convolution_normalizedDilation]
    calc
      _ ≤ ‖𝓕 φ (((2 : ℝ) ^ N)⁻¹ • ξ) * 𝓕 f ξ‖ + ‖𝓕 f ξ‖ := norm_sub_le _ _
      _ ≤ 2 * ‖𝓕 f ξ‖ := by
        rw [norm_mul]
        nlinarith [hbound (((2 : ℝ) ^ N)⁻¹ • ξ), norm_nonneg (𝓕 f ξ)]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_fourier_convolution_dyadic_eq φ f hφ ξ] with N hN
    simp only [hN, sub_self, norm_zero]

/-- The smooth dyadic approximations of a Schwartz input converge uniformly on the whole space. -/
theorem tendstoUniformly_convolution_dyadic (φ f : 𝓢(E, ℂ))
    (hφ : ∀ ξ : E, ‖ξ‖ ≤ 1 → 𝓕 φ ξ = 1) (hbound : ∀ ξ : E, ‖𝓕 φ ξ‖ ≤ 1) :
    TendstoUniformly (fun N : ℕ ↦ (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
      (normalizedDilation ((2 : ℝ) ^ N) (pow_pos two_pos N) φ) f : E → ℂ)) f atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.1
    (tendsto_integral_norm_fourier_convolution_dyadic_sub φ f hφ hbound)).2 ε hε] with N hN
  intro x
  let g := SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
    (normalizedDilation ((2 : ℝ) ^ N) (pow_pos two_pos N) φ) f
  have hb : ‖(g - f) x‖ ≤ ∫ ξ : E, ‖𝓕 g ξ - 𝓕 f ξ‖ := by
    have he : (𝓕 (g - f) : 𝓢(E, ℂ)) = 𝓕 g - 𝓕 f := (fourierCLM ℂ 𝓢(E, ℂ)).map_sub _ _
    nth_rw 1 [← fourierInv_fourier_eq (F := 𝓢(E, ℂ)) (g - f)]
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    apply (norm_integral_le_integral_norm _).trans_eq
    simp only [Circle.norm_smul, he, sub_apply]
  simpa only [dist_eq_norm, norm_sub_rev, sub_apply, g] using hb.trans_lt hN

end NKBesicovitch
