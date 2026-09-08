/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.FourierFrame
public import NKBesicovitch.Geometry.RotatedHyperplaneIntegral

/-!
# Averaged Fourier decay of the signed X-ray transform

Fiberwise Plancherel and polar averaging give the exact inverse-radius
Fourier weight, with the ratio of sphere areas as normalization. A gap of
radius `R > 0` in the Fourier support therefore gives an `R⁻¹` gain for the
squared norm, or `R⁻¹ᐟ²` for the joint direction-displacement `L²` norm.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.XRay

variable {m : ℕ} [Nonempty (Fin m)]
  (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- The exact averaged Fourier-slice identity with normalized Haar directions. -/
theorem lintegral_lintegral_enorm_sq_frameLineIntegral
    (f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) :
    (∫⁻ u, ∫⁻ x, ‖frameLineIntegral v b f u x‖ₑ ^ 2 ∂volume
      ∂Rotations.probability (m + 1)) =
      (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere univ *
        ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere univ)⁻¹ *
          ∫⁻ ξ, (ENNReal.ofReal ‖ξ‖)⁻¹ * ‖𝓕 f ξ‖ₑ ^ 2 := by
  simp_rw [lintegral_enorm_sq_frameLineIntegral]
  exact lintegral_rotate_linearIsometry
    ((ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ.subtypeₗᵢ.comp b.toLinearIsometry)
    ((𝓕 f).continuous.measurable.enorm.pow_const 2)

/-- A Fourier gap of radius `R` gives inverse-radius decay of the squared joint norm. -/
theorem lintegral_lintegral_enorm_sq_frameLineIntegral_le
    (f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) {R : ℝ} (hR : 0 < R)
    (hgap : ∀ ξ, ‖ξ‖ < R → 𝓕 f ξ = 0) :
    (∫⁻ u, ∫⁻ x, ‖frameLineIntegral v b f u x‖ₑ ^ 2 ∂volume
      ∂Rotations.probability (m + 1)) ≤
      (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere univ *
        ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere univ)⁻¹ *
          (ENNReal.ofReal R)⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  rw [lintegral_lintegral_enorm_sq_frameLineIntegral]
  have h : (∫⁻ ξ, (ENNReal.ofReal ‖ξ‖)⁻¹ * ‖𝓕 f ξ‖ₑ ^ 2) ≤
      ∫⁻ ξ, (ENNReal.ofReal R)⁻¹ * ‖𝓕 f ξ‖ₑ ^ 2 := by
    apply lintegral_mono
    intro ξ
    by_cases hξ : ‖ξ‖ < R
    · simp only [hgap ξ hξ, enorm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, le_refl]
    · exact mul_le_mul' (ENNReal.inv_le_inv.mpr
        (ENNReal.ofReal_le_ofReal (le_of_not_gt hξ))) le_rfl
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hR).ne'),
    lintegral_enorm_sq_fourier] at h
  simpa only [mul_assoc] using mul_le_mul_right h
    ((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere univ *
      ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere univ)⁻¹)

/-- The signed X-ray transform gains half a derivative in the joint `L²` norm. -/
theorem eLpNorm_frameLineIntegral_le (f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ))
    {R : ℝ} (hR : 0 < R) (hgap : ∀ ξ, ‖ξ‖ < R → 𝓕 f ξ = 0) :
    eLpNorm (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
      frameLineIntegral v b f z.1 z.2) 2 ((Rotations.probability (m + 1)).prod volume) ≤
      ((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere univ *
        ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere univ)⁻¹ *
          (ENNReal.ofReal R)⁻¹) ^ (1 / 2 : ℝ) * eLpNorm f 2 volume := by
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [lintegral_prod _ ((measurable_frameLineIntegral v b f.continuous.measurable).enorm.pow_const
    (2 : ℕ)).aemeasurable]
  have h := ENNReal.rpow_le_rpow
    (lintegral_lintegral_enorm_sq_frameLineIntegral_le v b f hR hgap)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h

/-- The half-derivative estimate has a finite constant independent of the Fourier gap. -/
theorem exists_eLpNorm_frameLineIntegral_bound :
    ∃ C : ℝ≥0, ∀ R : ℝ, 0 < R → ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      (∀ ξ, ‖ξ‖ < R → 𝓕 f ξ = 0) →
        eLpNorm (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
          frameLineIntegral v b f z.1 z.2) 2 ((Rotations.probability (m + 1)).prod volume) ≤
          (C : ℝ≥0∞) * (ENNReal.ofReal R) ^ (-1 / 2 : ℝ) * eLpNorm f 2 volume := by
  let A := (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere univ *
    ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere univ)⁻¹
  have hA : A ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _)
    (ENNReal.inv_ne_top.mpr (Measure.measure_univ_ne_zero.mpr
      (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere_ne_zero))
  refine ⟨A.toNNReal ^ (1 / 2 : ℝ), ?_⟩
  intro R hR f hgap
  have h := eLpNorm_frameLineIntegral_le v b f hR hgap
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_neg_one (ENNReal.ofReal R), ← ENNReal.rpow_mul] at h
  simpa only [ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.coe_toNNReal hA, neg_one_mul, neg_div, A, mul_assoc] using h

end NKBesicovitch.XRay
