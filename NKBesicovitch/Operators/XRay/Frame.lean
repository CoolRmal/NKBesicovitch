/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.DirectionMeasurability

/-!
# The X-ray transform in orthogonal frame coordinates

Integrate along the normal line after an ambient rotation, retaining
orthonormal transverse coordinates for the lower-dimensional input.
Its displacement norm is exactly the geometric direction norm. Inputs
supported in a fixed centered ball give transforms supported in the
same-radius transverse ball, uniformly over all rotations.
-/

@[expose] public section

open MeasureTheory Submodule Set Metric
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {n m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- The full X-ray integral in the orthogonal frame obtained by rotating a fixed normal frame. -/
noncomputable def frameXRay (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (u : Rotations n)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, f (Unitary.linearIsometryEquiv u
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)))

theorem measurable_frameXRay {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) (u : Rotations n) : Measurable (frameXRay v b f u) := by
  have hm := (hf.comp (Unitary.linearIsometryEquiv u).continuous.measurable).comp
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b).continuous.measurable
  exact hm.lintegral_prod_right' (ν := volume)

theorem support_frameXRay_subset_closedBall {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    {R : ℝ} (hs : Function.support f ⊆ closedBall 0 R) (u : Rotations n) :
    Function.support (frameXRay v b f u) ⊆ closedBall 0 R := by
  intro x hx
  by_contra hnot
  have hzero (t : ℝ) : f (Unitary.linearIsometryEquiv u
      (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t))) = 0 := by
    by_contra hne
    apply hnot
    have hpoint := hs hne
    have hnorm := norm_normalCoordinatesWithBasis_symm_fst_le (norm_eq_of_mem_sphere v) b
      (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t))
    simp only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] at hpoint ⊢
    rw [ContinuousLinearEquiv.symm_apply_apply] at hnorm
    exact hnorm.trans hpoint
  exact hx (by simp only [frameXRay, hzero, lintegral_zero])

theorem eLpNorm_frameXRay {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) (u : Rotations n) (r : ℝ≥0∞) :
    eLpNorm (frameXRay v b f u) r volume =
      directionXRayNorm (f ∘ Unitary.linearIsometryEquiv u) r v := by
  have hm : Measurable (fun y : (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ ↦
      ∫⁻ t : ℝ, f (Unitary.linearIsometryEquiv u
        ((y : EuclideanSpace ℝ (Fin n)) + t • (v : EuclideanSpace ℝ (Fin n))))) := by
    have h : Measurable (fun z : (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ × ℝ ↦
        f (Unitary.linearIsometryEquiv u
          ((z.1 : EuclideanSpace ℝ (Fin n)) + z.2 • (v : EuclideanSpace ℝ (Fin n))))) :=
      hf.comp (by fun_prop)
    exact h.lintegral_prod_right' (ν := volume)
  unfold frameXRay directionXRayNorm
  simpa only [normalCoordinatesWithBasis_apply, Function.comp_def]
    using eLpNorm_comp_measurePreserving (p := r) hm.aestronglyMeasurable b.measurePreserving

theorem eLpNorm_eLpNorm_frameXRay {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) {r : ℝ≥0∞} (hr : r ≠ 0) (hrfin : r ≠ ∞) (q : ℝ≥0∞) :
    eLpNorm (fun u ↦ eLpNorm (frameXRay v b f u) r volume) q (Rotations.probability n) =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ)⁻¹) ^ (1 / q.toReal) *
        sphericalXRayNorm f q r := by
  simp only [eLpNorm_frameXRay v b hf]
  exact eLpNorm_directionXRayNorm_rotate hf hr hrfin q v

end NKBesicovitch.XRay
