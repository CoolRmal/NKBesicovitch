/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.Step
public import NKBesicovitch.Operators.PlateMeasurability
public import NKBesicovitch.Operators.PlatePower

/-!
# Matching diagonal plate estimates to the X-ray exponents

Increase a lower-dimensional diagonal estimate from exponent `a` to `t*a`,
then decrease its output exponent on the probability direction space.
The flag argument applies the X-ray estimate and gives another diagonal
estimate. The previous constant becomes its `1/t` power, which is the
required reduction of the thickness loss.
-/

public section

open MeasureTheory Set Metric NKBesicovitch.Grassmannian NKBesicovitch.XRay
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

variable {n m k : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

theorem eLpNorm_plateMaximal_le_of_diagonal (hkm : k ≤ m)
    {δ R t : ℝ} (hδ : 0 < δ) (ht : 1 ≤ t) {a q : ℝ≥0∞}
    (hqa : q ≤ a * ENNReal.ofReal t) (A : ℝ≥0)
    (hbound : ∀ g : EuclideanSpace ℝ (Fin m) → ℝ≥0∞, Measurable g →
      Function.support g ⊆ closedBall 0 R →
        eLpNorm (plateMaximal δ g) a (probability hkm) ≤ A * eLpNorm g a volume)
    {g : EuclideanSpace ℝ (Fin m) → ℝ≥0∞} (hg : Measurable g)
    (hs : Function.support g ⊆ closedBall 0 R) :
    eLpNorm (plateMaximal δ g) q (probability hkm) ≤
      (A ^ t⁻¹ : ℝ≥0) * eLpNorm g (a * ENNReal.ofReal t) volume := by
  apply (eLpNorm_le_eLpNorm_of_exponent_le hqa
    (measurable_plateMaximal δ hg).aestronglyMeasurable).trans
  have h := eLpNorm_plateMaximal_le_of_power hδ ht hbound hg hs
  rwa [← ENNReal.coe_rpow_of_nonneg A (inv_nonneg.mpr (zero_le_one.trans ht))] at h

include v b in
/-- A diagonal plate bound and a compatible mixed X-ray estimate give the next diagonal bound. -/
theorem eLpNorm_plateMaximal_diagonal_step (hkn : k + 1 ≤ n) (hkm : k ≤ m)
    {δ R t : ℝ} (hδ : 0 < δ) (ht : 1 ≤ t) {a p q : ℝ≥0∞}
    (ha : a ≠ 0) (hafin : a ≠ ∞) (hpq : p ≤ q)
    (hqa : q ≤ a * ENNReal.ofReal t) (hq : q ≠ 0) (hqfin : q ≠ ∞)
    (A B : ℝ≥0)
    (hlow : ∀ g : EuclideanSpace ℝ (Fin m) → ℝ≥0∞, Measurable g →
      Function.support g ⊆ closedBall 0 R →
        eLpNorm (plateMaximal δ g) a (probability hkm) ≤ A * eLpNorm g a volume)
    (hxray : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable f →
      Function.support f ⊆ closedBall 0 R →
        sphericalXRayNorm f q (a * ENNReal.ofReal t) ≤ B * eLpNorm f p volume)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f)
    (hs : Function.support f ⊆ closedBall 0 R) :
    eLpNorm (plateMaximal δ f) p (probability hkn) ≤
      (((2 : ℝ≥0) ^ m * A ^ t⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ((((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ)⁻¹) ^ (1 / q.toReal) *
          (B * eLpNorm f p volume)) := by
  have ht0 := zero_lt_one.trans_le ht
  have hr : a * ENNReal.ofReal t ≠ 0 := mul_ne_zero ha (ENNReal.ofReal_pos.mpr ht0).ne'
  have hrfin : a * ENNReal.ofReal t ≠ ∞ := ENNReal.mul_ne_top hafin ENNReal.ofReal_ne_top
  apply (eLpNorm_le_eLpNorm_of_exponent_le hpq
    (measurable_plateMaximal δ hf).aestronglyMeasurable).trans
  apply (eLpNorm_plateMaximal_le_sphericalXRay v b hkn hkm hδ hq hqfin hr hrfin
    (A ^ t⁻¹) (fun g hg hgs ↦ eLpNorm_plateMaximal_le_of_diagonal hkm hδ ht hqa A
      hlow hg hgs) hf hs).trans
  exact mul_le_mul_right (mul_le_mul_right (hxray f hf hs) _) _

end NKBesicovitch.Induction
