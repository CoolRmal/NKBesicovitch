/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.Step
public import NKBesicovitch.Operators.XRay.SphericalBound

/-!
# A one-dimensional induction step from the proved X-ray estimate

For every strictly supercritical projection exponent `β`, the spherical
estimate supplies an outer exponent `Q > 2`. A plate bound in dimension
`m` with input exponent `Q / (β - 1)` then gives a bound in dimension
`m + 1` with any input exponent above `Q / β`. Its thickness-dependent
constant is multiplied by a factor independent of the thickness.
-/

public section

open MeasureTheory Set Metric NKBesicovitch.Grassmannian NKBesicovitch.XRay
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

variable {n m k : ℕ} [Nonempty (Fin m)]
    (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

include v b in
/-- The proved spherical X-ray estimate upgrades a lower-dimensional plate estimate. -/
theorem exists_plateMaximal_induction_step (hkn : k + 1 ≤ n) (hkm : k ≤ m)
    {β : ℝ} (hβ : projectionExponent < β) (hβ2 : β ≤ 2) :
    ∃ Q : ℕ, 2 < Q ∧ ∀ R p : ℝ, (Q : ℝ) / β < p → ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → ∀ A : ℝ≥0,
        (∀ g : EuclideanSpace ℝ (Fin m) → ℝ≥0∞, Measurable g →
          Function.support g ⊆ closedBall 0 R →
            eLpNorm (plateMaximal δ g) (ENNReal.ofReal Q) (probability hkm) ≤
              A * eLpNorm g (ENNReal.ofReal ((Q : ℝ) / (β - 1))) volume) →
        ∀ f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable f →
          Function.support f ⊆ closedBall 0 R →
            eLpNorm (plateMaximal δ f) (ENNReal.ofReal Q) (probability hkn) ≤
              ENNReal.ofReal C * A * eLpNorm f (ENNReal.ofReal p) volume := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = m + 1 :=
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b).toLinearEquiv.finrank_eq.symm.trans
      (by simp [Module.finrank_prod])
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = m + 1) := ⟨hdim⟩
  obtain ⟨Q, hQ, hxray⟩ := exists_sphericalXRayNorm_bound (E := EuclideanSpace ℝ (Fin n)) m hβ hβ2
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hβ1 : 1 < β := projectionExponent_mem.1.trans hβ
  have hr : 0 < (Q : ℝ) / (β - 1) := div_pos hQpos (sub_pos.mpr hβ1)
  refine ⟨Q, hQ, fun R p hp ↦ ?_⟩
  obtain ⟨B, _, hx⟩ := hxray (closedBall 0 R) isBounded_closedBall p hp
  let S : ℝ≥0∞ := (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ)⁻¹) ^
    (1 / (ENNReal.ofReal (Q : ℝ)).toReal)
  let D : ℝ≥0∞ := (2 : ℝ≥0∞) ^ m * S * ENNReal.ofReal B
  have hμ0 : (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ ≠ 0 :=
    isOpen_univ.measure_ne_zero _ ⟨v, mem_univ v⟩
  have hS : S ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.inv_ne_top.mpr hμ0)
  have hD : D ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) hS)
    ENNReal.ofReal_ne_top
  refine ⟨D.toReal + 1, by positivity, fun δ hδ A hlow f hf hs ↦ ?_⟩
  apply (eLpNorm_plateMaximal_le_sphericalXRay v b hkn hkm hδ
    (ENNReal.ofReal_pos.mpr hQpos).ne' ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top A hlow hf hs).trans
  calc
    _ ≤ D * A * eLpNorm f (ENNReal.ofReal p) volume := by
      have h := mul_le_mul_right (mul_le_mul_right (hx f hf hs) S)
        (((2 : ℝ≥0) ^ m * A : ℝ≥0) : ℝ≥0∞)
      convert h using 1
      simp only [D, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat]
      ac_rfl
    _ ≤ _ := mul_le_mul_left (mul_le_mul_left (calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ ENNReal.ofReal (D.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)) _) _

end NKBesicovitch.Induction
