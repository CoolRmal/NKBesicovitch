/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.DirectionMeasure
public import NKBesicovitch.Operators.XRay.DirectionNorm

/-!
# Spherical X-ray norms and their comparison on direction caps

The geometric mixed norm integrates the perpendicular displacement norm
over the unit sphere with its Euclidean surface measure. On a cap where
the normal component is at least `c > 0`, it is controlled by the model
chart norm with factor `dim(E)^(1/q) / c`.
-/

@[expose] public section

open MeasureTheory Submodule Set Metric NKBesicovitch.Projection
open scoped ENNReal InnerProductSpace NNReal

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} {v : E}

/-- The mixed norm in perpendicular displacement and spherical direction of the X-ray integral. -/
noncomputable def sphericalXRayNorm (f : E → ℝ≥0∞) (q r : ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (directionXRayNorm f r) q (volume : Measure E).toSphere

theorem eLpNorm_directionXRayNorm_slope_le (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {A : Set (ℝ ∙ v)ᗮ} (hA : MeasurableSet A) {c : ℝ} (hc : 0 < c)
    (hcap : ∀ ξ ∈ A, c ≤ ⟪v, (normalDirection hv ξ : E)⟫_ℝ)
    {f : E → ℝ≥0∞} (hf : Measurable f) (q r : ℝ≥0∞) :
    eLpNorm (directionXRayNorm f r ∘ normalDirection hv) q (volume.restrict A) ≤
      ENNReal.ofReal (1 / c) * mixedNorm ((Prod.snd ⁻¹' (b ⁻¹' A)).indicator
        (fun g : Line m ↦ chartXRay (f ∘ normalCoordinatesWithBasis hv b) g.2 g.1))
          q r volume volume := by
  have hb : MeasurableEmbedding b := b.toHomeomorph.measurableEmbedding
  have hmp := b.measurePreserving.restrict_preimage_emb hb A
  rw [← hmp.map_eq, hb.eLpNorm_map_measure]
  rw [mixedNorm_indicator_snd (hA.preimage hb.measurable)]
  unfold mixedNorm
  have hcn : 0 ≤ 1 / c := le_of_lt (one_div_pos.mpr hc)
  rw [ENNReal.ofReal_eq_coe_nnreal hcn]
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (c := ⟨1 / c, hcn⟩)
  filter_upwards [ae_restrict_mem (hA.preimage hb.measurable)] with ξ hξ
  simp only [Function.comp_apply, enorm_eq_self]
  apply (eLpNorm_perpendicular_normalDirection_le hv b hf ξ r).trans
  apply mul_le_mul_left
  exact (ENNReal.ofReal_le_ofReal
    (norm_add_normal_le_of_inner_lower hv hc (hcap _ hξ))).trans_eq
      (ENNReal.ofReal_eq_coe_nnreal hcn)

/-- A cap estimate with an explicit constant from sphere measure and arclength. -/
theorem eLpNorm_directionXRayNorm_cap_le (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {A : Set (ℝ ∙ v)ᗮ} (hA : MeasurableSet A) {c : ℝ} (hc : 0 < c)
    (hcap : ∀ ξ ∈ A, c ≤ ⟪v, (normalDirection hv ξ : E)⟫_ℝ)
    {f : E → ℝ≥0∞} (hf : Measurable f) (q r : ℝ≥0∞) :
    eLpNorm (directionXRayNorm f r) q
        ((volume : Measure E).toSphere.restrict (normalDirection hv '' A)) ≤
      ((Module.finrank ℝ E : ℝ≥0∞) ^ (1 / q.toReal) * ENNReal.ofReal (1 / c)) *
        mixedNorm ((Prod.snd ⁻¹' (b ⁻¹' A)).indicator
          (fun g : Line m ↦ chartXRay (f ∘ normalCoordinatesWithBasis hv b) g.2 g.1))
            q r volume volume := by
  apply (eLpNorm_toSphere_normalDirection_le hv hA (directionXRayNorm f r) q).trans
  rw [mul_assoc]
  exact mul_le_mul_right (eLpNorm_directionXRayNorm_slope_le hv b hA hc hcap hf q r) _

end NKBesicovitch.XRay
