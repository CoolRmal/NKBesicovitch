/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Fourier.PlaneConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Signed dyadic decomposition on affine planes

Affine-plane integration is linear on Schwartz inputs. Finite telescoping,
the triangle inequality, and dominated convergence bound its absolute value
by the sum of the absolute values of its signed frequency pieces.
-/

public section

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform ENNReal Topology

namespace NKBesicovitch

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Signed full-plane integration is bounded by its low-frequency and annular pieces. -/
theorem enorm_integral_affine_le_dyadic_sum (φ f : 𝓢(E, ℂ))
    (hφ : ∀ ξ : E, ‖ξ‖ ≤ 1 → 𝓕 φ ξ = 1) (hbound : ∀ ξ : E, ‖𝓕 φ ξ‖ ≤ 1)
    (e : F →ₗᵢ[ℝ] E) (x : E) :
    ‖∫ y : F, f (x + e y)‖ₑ ≤
      ‖∫ y : F, SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) φ f (x + e y)‖ₑ +
        ∑' j : ℕ, ‖∫ y : F, SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
          (normalizedDilation ((2 : ℝ) ^ j) (pow_pos two_pos j)
            (normalizedDilation 2 two_pos φ - φ)) f (x + e y)‖ₑ := by
  let L : 𝓢(E, ℂ) →L[ℂ] ℂ := (SchwartzMap.integralCLM ℂ volume).comp
    (SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun y : F ↦ x + e y)
      ((Function.HasTemperateGrowth.const x).add e.toContinuousLinearMap.hasTemperateGrowth)
      (((IsometryEquiv.addLeft x).isometry.comp e.isometry).antilipschitz))
  have hlim := (tendsto_integral_convolution_dyadic_affine φ f hφ hbound e x).enorm
  apply le_of_tendsto hlim
  refine Eventually.of_forall fun N ↦ ?_
  have he := congrArg L (sum_convolution_normalizedDilation_annular φ f N)
  simp only [map_add, map_sum] at he
  change ‖L (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
    (normalizedDilation ((2 : ℝ) ^ N) (pow_pos two_pos N) φ) f)‖ₑ ≤ _
  rw [← he]
  apply (enorm_add_le _ _).trans
  apply add_le_add le_rfl
  exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum (Finset.range N))

end NKBesicovitch
