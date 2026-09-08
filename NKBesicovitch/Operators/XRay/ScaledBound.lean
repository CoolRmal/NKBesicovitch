/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.Power
public import NKBesicovitch.Operators.XRay.SphericalBound

/-!
# The proved spherical X-ray estimate at arbitrary larger scales

The selectable projection estimate supplies an exponent `Q > 2`. For every
`p > Q/β` and every `t ≥ 1`, the spherical estimate holds with exponents
`tp`, `tQ`, and `tQ/(β-1)`. The constant is finite and uniform over inputs
in a fixed ball. Thus later induction steps can match an already chosen
lower-dimensional exponent without changing the X-ray ratios.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- All three exponents in the proved X-ray estimate may be increased by a common factor. -/
theorem exists_sphericalXRayNorm_bound_scaled (m : ℕ) [Nonempty (Fin m)]
    [Fact (Module.finrank ℝ E = m + 1)] {β : ℝ}
    (hβ : projectionExponent < β) (hβ2 : β ≤ 2) :
    ∃ Q : ℕ, 2 < Q ∧ ∀ p : ℝ, (Q : ℝ) / β < p → ∀ t : ℝ, 1 ≤ t →
      ∀ R : ℝ≥0, ∃ C : ℝ≥0, ∀ f : E → ℝ≥0∞, Measurable f →
        Function.support f ⊆ closedBall 0 (R : ℝ) →
          sphericalXRayNorm f (ENNReal.ofReal (t * Q))
            (ENNReal.ofReal (t * ((Q : ℝ) / (β - 1)))) ≤
              C * eLpNorm f (ENNReal.ofReal (t * p)) volume := by
  obtain ⟨Q, hQ, hx⟩ := exists_sphericalXRayNorm_bound (E := E) m hβ hβ2
  refine ⟨Q, hQ, fun p hp t ht R ↦ ?_⟩
  obtain ⟨B, hB, hbound⟩ := hx (closedBall 0 (R : ℝ)) isBounded_closedBall p hp
  let B' : ℝ≥0 := .mk B hB.le
  refine ⟨((2 * R) ^ (t - 1) * B') ^ t⁻¹, fun f hf hs ↦ ?_⟩
  have h := sphericalXRayNorm_le_of_power ht R hbound hf hs
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  simp only [ENNReal.ofReal_mul ht0, mul_comm (ENNReal.ofReal t)]
  convert h using 1
  rw [ENNReal.coe_rpow_of_nonneg _ (inv_nonneg.mpr ht0), ENNReal.coe_mul]
  simp only [B', ENNReal.ofReal_eq_coe_nnreal hB.le]

end NKBesicovitch.XRay
