/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.SmoothedTail

/-!
# Polynomially weighted smoothed tails

The weighted transform is bounded by a constant multiple of the unweighted
transform plus an arbitrarily decaying spatial tail. Both constants are
uniform over the frequency scale and the supported input.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch.XRay

private lemma polynomial_weight_decay_le (r : ℝ) (hr : 0 ≤ r) (A N : ℕ) :
    (1 + r ^ 2) ^ A * ((1 + r) ^ (2 * A + N))⁻¹ ≤ ((1 + r) ^ N)⁻¹ := by
  have hw : (1 + r ^ 2) ^ A ≤ (1 + r) ^ (2 * A) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) A
  apply (mul_le_mul_of_nonneg_right hw (by positivity)).trans_eq
  rw [pow_add, mul_inv_rev]
  field_simp [show 1 + r ≠ 0 by positivity]

variable {m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- Polynomial weights cost a bounded local factor and an arbitrarily decaying tail. -/
theorem exists_norm_weighted_frameLineIntegral_dilation_le
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) (A L N : ℕ) (R : ℝ≥0) :
    ∃ B C : ℝ≥0, ∀ a : ℝ, ∀ ha : 0 < a, 1 ≤ a →
      ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
      ∀ u : Rotations (m + 1), ∀ x : EuclideanSpace ℝ (Fin m),
        let g := frameLineIntegral v b (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
          (normalizedDilation a ha ψ) f) u x
        ‖(1 + ‖x‖ ^ 2) ^ A • g‖ ≤ (B : ℝ) * ‖g‖ +
          (C : ℝ) * (a ^ L)⁻¹ * (eLpNorm f 1 volume).toReal * ((1 + ‖x‖) ^ N)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_enorm_frameLineIntegral_dilation_tail v b ψ L (2 * A + N)
  refine ⟨.mk ((1 + (2 * ((R : ℝ) + 1)) ^ 2) ^ A) (by positivity), C,
    fun a ha ha₁ f hs u x ↦ ?_⟩
  dsimp only
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  by_cases hx : ‖x‖ < 2 * ((R : ℝ) + 1)
  · apply le_add_of_le_of_nonneg ?_ (by positivity)
    apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact pow_le_pow_left₀ (by positivity)
      (by nlinarith [norm_nonneg x]) A
  · have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (f.memLp 1 volume).2.ne)
      (hC R a ha ha₁ f hs u x (le_of_not_gt hx))
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at ht
    apply le_add_of_nonneg_of_le (by positivity)
    calc
      _ ≤ (1 + ‖x‖ ^ 2) ^ A * ((C : ℝ) * (a ^ L)⁻¹ *
          ((1 + ‖x‖) ^ (2 * A + N))⁻¹ * (eLpNorm f 1 volume).toReal) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = (C : ℝ) * (a ^ L)⁻¹ * (eLpNorm f 1 volume).toReal *
          ((1 + ‖x‖ ^ 2) ^ A * ((1 + ‖x‖) ^ (2 * A + N))⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (polynomial_weight_decay_le ‖x‖ (norm_nonneg x) A N)
        (by positivity)

end NKBesicovitch.XRay
