/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.DirectionChart
public import NKBesicovitch.Operators.XRay.FullLine
public import NKBesicovitch.Operators.XRay.TransverseMeasure
public import NKBesicovitch.Operators.XRay.Arclength

/-!
# Perpendicular X-ray norms in slope coordinates

An orthonormal basis identifies the transverse hyperplane with the model
Euclidean space. Projection compares its displacement norm to the norm
on the hyperplane perpendicular to the line. Normalizing the direction
then introduces precisely the arclength factor `‖ξ + v‖`.
-/

@[expose] public section

open MeasureTheory Submodule
open scoped ENNReal InnerProductSpace

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} {v : E}

theorem chartXRay_normalCoordinates (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (f : E → ℝ≥0∞)
    (ξ x : EuclideanSpace ℝ (Fin m)) :
    chartXRay (f ∘ normalCoordinatesWithBasis hv b) ξ x =
      ∫⁻ t : ℝ, f ((b x : E) + t • ((b ξ : E) + v)) := by
  unfold chartXRay
  congr 1
  funext t
  simp only [Function.comp_def, normalCoordinatesWithBasis_apply, map_add, map_smul,
    Submodule.coe_add, Submodule.coe_smul, smul_add, add_assoc]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The displacement norm of the arclength X-ray integral in a unit direction. -/
noncomputable def directionXRayNorm (f : E → ℝ≥0∞) (r : ℝ≥0∞)
    (w : Metric.sphere (0 : E) 1) : ℝ≥0∞ :=
  eLpNorm (fun y : (ℝ ∙ (w : E))ᗮ ↦ ∫⁻ t : ℝ, f ((y : E) + t • (w : E))) r volume

theorem eLpNorm_perpendicular_normalDirection_le (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {f : E → ℝ≥0∞} (hf : Measurable f) (ξ : EuclideanSpace ℝ (Fin m)) (r : ℝ≥0∞) :
    directionXRayNorm f r (normalDirection hv (b ξ)) ≤
        ENNReal.ofReal ‖(b ξ : E) + v‖ *
          eLpNorm (chartXRay (f ∘ normalCoordinatesWithBasis hv b) ξ) r volume := by
  have hw : (b ξ : E) + v ≠ 0 := norm_pos_iff.mp
    (zero_lt_one.trans_le (one_le_norm_add_normal hv (b ξ)))
  have hm : Measurable (fun x : (ℝ ∙ v)ᗮ ↦
      ∫⁻ t : ℝ, f ((x : E) + t • (normalDirection hv (b ξ) : E))) := by
    have h : Measurable (fun z : (ℝ ∙ v)ᗮ × ℝ ↦
        f ((z.1 : E) + z.2 • (normalDirection hv (b ξ) : E))) := hf.comp (by fun_prop)
    exact h.lintegral_prod_right' (ν := volume)
  have heq := eLpNorm_comp_measurePreserving (p := r) hm.aestronglyMeasurable b.measurePreserving
  apply (eLpNorm_perpendicular_le_transverse (inner_normalDirection_pos hv (b ξ)).ne' hf r).trans
  rw [← heq]
  rw [← coe_nnnorm ((b ξ : E) + v), ENNReal.ofReal_coe_nnreal]
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (c := ‖(b ξ : E) + v‖₊)
  apply ae_of_all
  intro x
  simp only [Function.comp_apply, enorm_eq_self, coe_normalDirection]
  rw [lintegral_normalize_direction hf hw, chartXRay_normalCoordinates]
  simp only [← coe_nnnorm ((b ξ : E) + v), ENNReal.ofReal_coe_nnreal, le_refl]

end NKBesicovitch.XRay
