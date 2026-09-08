/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.WeightedNorm
public import NKBesicovitch.Operators.XRay.SmoothedDecay

/-!
# Frequency decay with polynomial transverse weights

For each polynomial weight, the smoothed X-ray transform retains the gain
`a^(-1/p)` for every finite `p ≥ 2` and every `a ≥ 1`. The constant is uniform
over frequency scales and Schwartz inputs supported in a fixed ball.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.XRay

variable {m : ℕ} [Nonempty (Fin m)]
  (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- Every polynomial transverse weight preserves the smoothed `1/p` frequency gain. -/
theorem exists_eLpNorm_weighted_frameLineIntegral_dilation_decay
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ))
    (hgap : ∀ ξ, ‖ξ‖ < 1 → 𝓕 ψ ξ = 0) (A : ℕ) (R : ℝ≥0) {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ≥0, ∀ a : ℝ, ∀ ha : 0 < a, 1 ≤ a →
      ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
        eLpNorm (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
          (1 + ‖z.2‖ ^ 2) ^ A • frameLineIntegral v b
            (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
              (normalizedDilation a ha ψ) f) z.1 z.2)
          (ENNReal.ofReal p) ((Rotations.probability (m + 1)).prod volume) ≤
            C * (ENNReal.ofReal a) ^ (-1 / p : ℝ) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp₁ : 1 ≤ p := by linarith
  have hq : 1 / p ≤ 1 := (div_le_one (by linarith : 0 < p)).mpr hp₁
  let K := (volume (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) R)) ^ (1 - 1 / p)
  have hK : K ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hq) measure_closedBall_lt_top.ne
  obtain ⟨B, C, hC⟩ := exists_eLpNorm_weighted_frameLineIntegral_dilation_le v b ψ A 1 R hp₁
  obtain ⟨D, hD⟩ := exists_eLpNorm_frameLineIntegral_dilation_decay v b ψ hgap R hp
  refine ⟨B * D + C * K.toNNReal, fun a ha ha₁ f hs ↦ ?_⟩
  have hf₁ : eLpNorm f 1 volume ≤ eLpNorm f (ENNReal.ofReal p) volume * K := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (closedBall 0 R))
      (ENNReal.one_le_ofReal.mpr hp₁) f.continuous.measurable.aestronglyMeasurable
    simpa only [eLpNorm_restrict_eq_of_support_subset hs, Measure.restrict_apply_univ,
      ENNReal.toReal_one, div_one, ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using h
  have ha' : ENNReal.ofReal a⁻¹ ≤ ENNReal.ofReal a ^ (-1 / p : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_pos ha]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le ha₁ (by simpa only [neg_div] using neg_le_neg hq)
  apply (hC a ha ha₁ f hs).trans
  calc
    _ ≤ B * (D * ENNReal.ofReal a ^ (-1 / p : ℝ) * eLpNorm f (ENNReal.ofReal p) volume) +
        C * ENNReal.ofReal a ^ (-1 / p : ℝ) * (eLpNorm f (ENNReal.ofReal p) volume * K) :=
      add_le_add (mul_le_mul' le_rfl (hD a ha f hs))
        (mul_le_mul' (mul_le_mul' le_rfl (by simpa only [pow_one] using ha')) hf₁)
    _ = _ := by
      simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_toNNReal hK, add_mul]
      ac_rfl

end NKBesicovitch.XRay
