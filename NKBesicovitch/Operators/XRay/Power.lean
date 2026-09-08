/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.Spherical
public import NKBesicovitch.Operators.MixedNorm.Powers

/-!
# Increasing the exponents of the spherical X-ray estimate

For input supported in a centered ball of radius `R`, the arclength
parameter lies in `[-R,R]`. Hölder therefore increases all three exponents
of a mixed X-ray estimate by the same factor, preserving their ratios.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped ENNReal InnerProductSpace NNReal

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ≥0∞} {t : ℝ}

theorem support_lineIntegrand_subset {R : ℝ}
    (hs : Function.support f ⊆ closedBall 0 R)
    (w : sphere (0 : E) 1) (y : (ℝ ∙ (w : E))ᗮ) :
    Function.support (fun s : ℝ ↦ f ((y : E) + s • (w : E))) ⊆ Icc (-R) R := by
  intro s hs'
  have hn : ‖(y : E) + s • (w : E)‖ ≤ R := by
    simpa only [mem_closedBall, dist_zero_right] using hs hs'
  have hi := abs_real_inner_le_norm (w : E) ((y : E) + s • (w : E))
  have hw := norm_eq_of_mem_sphere w
  have he := inner_normalCoordinates hw y s
  rw [normalCoordinates_apply] at he
  rw [he, hw, one_mul] at hi
  exact abs_le.mp (hi.trans hn)

variable [MeasurableSpace E] [BorelSpace E]

theorem lineIntegral_rpow_le (ht : 1 ≤ t) (R : ℝ≥0) (hf : Measurable f)
    (hs : Function.support f ⊆ closedBall 0 (R : ℝ))
    (w : sphere (0 : E) 1) (y : (ℝ ∙ (w : E))ᗮ) :
    (∫⁻ s : ℝ, f ((y : E) + s • (w : E))) ^ t ≤
      ((2 * R : ℝ≥0) ^ (t - 1) : ℝ≥0) *
        ∫⁻ s : ℝ, f ((y : E) + s • (w : E)) ^ t := by
  have hm : Measurable (fun s : ℝ ↦ f ((y : E) + s • (w : E))) := hf.comp (by fun_prop)
  have h := lintegral_rpow_le_measure_mul (μ := volume.restrict (Icc (-(R : ℝ)) R)) hm ht
  rw [setLIntegral_eq_of_support_subset (support_lineIntegrand_subset hs w y)] at h
  apply h.trans
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  have he : ENNReal.ofReal ((R : ℝ) - -(R : ℝ)) = (2 * R : ℝ≥0) := by
    rw [sub_neg_eq_add, ← two_mul]
    norm_num [ENNReal.ofReal_mul]
  rw [he, ← ENNReal.coe_rpow_of_nonneg _ (sub_nonneg.mpr ht)]
  exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _

variable [FiniteDimensional ℝ E]

theorem directionXRayNorm_rpow_le (ht : 1 ≤ t) (R : ℝ≥0) (hf : Measurable f)
    (hs : Function.support f ⊆ closedBall 0 (R : ℝ)) (w : sphere (0 : E) 1) (r : ℝ≥0∞) :
    directionXRayNorm f (r * ENNReal.ofReal t) w ^ t ≤
      ((2 * R : ℝ≥0) ^ (t - 1) : ℝ≥0) * directionXRayNorm (fun x ↦ f x ^ t) r w := by
  have he := eLpNorm_enorm_rpow (μ := volume) (p := r)
    (fun y : (ℝ ∙ (w : E))ᗮ ↦ ∫⁻ s : ℝ, f ((y : E) + s • (w : E)))
    (zero_lt_one.trans_le ht)
  simp only [enorm_eq_self] at he
  unfold directionXRayNorm
  rw [← he]
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (c := (2 * R) ^ (t - 1))
  exact ae_of_all _ fun y ↦ by
    simpa only [enorm_eq_self] using lineIntegral_rpow_le ht R hf hs w y

theorem sphericalXRayNorm_rpow_le (ht : 1 ≤ t) (R : ℝ≥0) (hf : Measurable f)
    (hs : Function.support f ⊆ closedBall 0 (R : ℝ)) (q r : ℝ≥0∞) :
    sphericalXRayNorm f (q * ENNReal.ofReal t) (r * ENNReal.ofReal t) ^ t ≤
      ((2 * R : ℝ≥0) ^ (t - 1) : ℝ≥0) * sphericalXRayNorm (fun x ↦ f x ^ t) q r := by
  have he := eLpNorm_enorm_rpow (μ := (volume : Measure E).toSphere) (p := q)
    (directionXRayNorm f (r * ENNReal.ofReal t)) (zero_lt_one.trans_le ht)
  simp only [enorm_eq_self] at he
  unfold sphericalXRayNorm
  rw [← he]
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (c := (2 * R) ^ (t - 1))
  exact ae_of_all _ fun w ↦ by
    simpa only [enorm_eq_self] using directionXRayNorm_rpow_le ht R hf hs w r

/-- A local mixed X-ray estimate holds at every common larger exponent scale. -/
theorem sphericalXRayNorm_le_of_power (ht : 1 ≤ t) (R : ℝ≥0) {p q r A : ℝ≥0∞}
    (hbound : ∀ g : E → ℝ≥0∞, Measurable g →
      Function.support g ⊆ closedBall 0 (R : ℝ) →
        sphericalXRayNorm g q r ≤ A * eLpNorm g p volume)
    (hf : Measurable f) (hs : Function.support f ⊆ closedBall 0 (R : ℝ)) :
    sphericalXRayNorm f (q * ENNReal.ofReal t) (r * ENNReal.ofReal t) ≤
      (((2 * R : ℝ≥0) ^ (t - 1) : ℝ≥0) * A) ^ t⁻¹ *
        eLpNorm f (p * ENNReal.ofReal t) volume := by
  have ht0 := zero_lt_one.trans_le ht
  have hs' : Function.support (fun x ↦ f x ^ t) ⊆ closedBall 0 (R : ℝ) := by
    intro x hx
    apply hs
    intro hzero
    exact hx (by simp only [hzero, ENNReal.zero_rpow_of_pos ht0])
  have h := (sphericalXRayNorm_rpow_le ht R hf hs q r).trans
    (mul_le_mul_right (hbound _ (hf.pow_const _) hs') _)
  have he := eLpNorm_enorm_rpow (μ := volume) (p := p) f ht0
  simp only [enorm_eq_self] at he
  rw [he, ← mul_assoc] at h
  have hp := ENNReal.rpow_le_rpow h (inv_nonneg.mpr ht0.le)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr ht0.le),
    ← ENNReal.rpow_mul, mul_inv_cancel₀ ht0.ne', ENNReal.rpow_one] using hp

end NKBesicovitch.XRay
