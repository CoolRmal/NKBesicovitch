/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.Seed

/-!
# Extending estimates beyond small thicknesses

The ambient-dimension estimate controls thicknesses at least one. Thus a local
plate estimate with deficit at most the ambient dimension only needs a separate
proof at thicknesses at most one.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

/-- Small-thickness bounds with deficit at most `n` extend to every positive thickness. -/
theorem hasPlateEstimate_of_small_thickness {n k : ℕ} (hkn : k ≤ n) {α p : ℝ}
    (hα : α ≤ n) (hp : 1 ≤ p)
    (hsmall : ∀ R : ℝ≥0, ∃ C : ℝ≥0, ∀ δ : ℝ≥0, 0 < δ → δ ≤ 1 →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable f →
        Function.support f ⊆ closedBall 0 (R : ℝ) →
          eLpNorm (plateMaximal δ f) (ENNReal.ofReal p) (Grassmannian.probability hkn) ≤
            (C * δ ^ (-α / p) : ℝ≥0) * eLpNorm f (ENNReal.ofReal p) volume) :
    HasPlateEstimate hkn α p := by
  intro R
  obtain ⟨C, hC⟩ := hsmall R
  obtain ⟨D, hD⟩ := hasPlateEstimate_seed hkn hp R
  refine ⟨C + D, fun δ hδ f hf hs ↦ ?_⟩
  by_cases hδ1 : δ ≤ 1
  · apply (hC δ hδ hδ1 f hf hs).trans
    exact mul_le_mul_left (ENNReal.coe_le_coe.mpr
      (mul_le_mul_left (le_add_of_nonneg_right (show 0 ≤ D from zero_le)) _)) _
  · apply (hD δ hδ f hf hs).trans
    apply mul_le_mul_left
    apply ENNReal.coe_le_coe.mpr
    apply mul_le_mul' (le_add_of_nonneg_left (show 0 ≤ C from zero_le))
    exact NNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge hδ1)
      (div_le_div_of_nonneg_right (neg_le_neg hα) (zero_lt_one.trans_le hp).le)

end NKBesicovitch.Induction
