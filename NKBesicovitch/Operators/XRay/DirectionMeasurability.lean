/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.NormalIsometry
public import NKBesicovitch.Geometry.SphereMeasure
public import NKBesicovitch.Operators.XRay.Spherical
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurability of geometric X-ray direction norms

In an orthogonal frame the displacement domain is fixed, so Tonelli
gives joint measurability. The norm is unchanged by transporting the
frame. A surjective Borel orbit map from the compact orthogonal group
then transfers measurability to the unit sphere.
The resulting norm identity includes the normalization factor for sphere measure.
-/

public section

open MeasureTheory Submodule Metric
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {n : ℕ}

theorem directionXRayNorm_rotate {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) (r : ℝ≥0∞) (u : Rotations n)
    (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    directionXRayNorm f r (Rotations.rotateSphere u v) =
      directionXRayNorm (f ∘ Unitary.linearIsometryEquiv u) r v := by
  let e := Unitary.linearIsometryEquiv u
  have hm : Measurable (fun y : (ℝ ∙ e v)ᗮ ↦
      ∫⁻ t : ℝ, f ((y : EuclideanSpace ℝ (Fin n)) + t • e v)) := by
    have h : Measurable (fun z : (ℝ ∙ e v)ᗮ × ℝ ↦
        f ((z.1 : EuclideanSpace ℝ (Fin n)) + z.2 • e v)) := hf.comp (by fun_prop)
    exact h.lintegral_prod_right' (ν := volume)
  have heq := eLpNorm_comp_measurePreserving (p := r) hm.aestronglyMeasurable
    (normalIsometry e v).measurePreserving
  change eLpNorm (fun y : (ℝ ∙ e v)ᗮ ↦
    ∫⁻ t : ℝ, f ((y : EuclideanSpace ℝ (Fin n)) + t • e v)) r volume = _
  rw [← heq]
  simp only [Function.comp_apply, coe_normalIsometry, directionXRayNorm, map_add, map_smul,
    Function.comp_def, e]

theorem measurable_directionXRayNorm {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) {r : ℝ≥0∞} (hr : r ≠ 0) (hrfin : r ≠ ∞)
    (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : Measurable (directionXRayNorm f r) := by
  apply ((Rotations.measurable_sphereOrbit v).measurable_comp_iff_of_surjective
    (Rotations.exists_rotateSphere_eq v)).mp
  have hm : Measurable (fun z : ((ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ × Rotations n) × ℝ ↦
      f ((z.1.2 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        ((z.1.1 : EuclideanSpace ℝ (Fin n)) + z.2 • (v : EuclideanSpace ℝ (Fin n))))) :=
    hf.comp (by fun_prop)
  have hn := measurable_eLpNorm_fiber (μ := volume)
    (hm.lintegral_prod_right' (ν := volume)) hr hrfin
  simp only [Function.comp_def]
  simp_rw [directionXRayNorm_rotate hf r]
  exact hn

/-- The frame norm equals the spherical X-ray norm with the surface-area normalization. -/
theorem eLpNorm_directionXRayNorm_rotate {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) {r : ℝ≥0∞} (hr : r ≠ 0) (hrfin : r ≠ ∞) (q : ℝ≥0∞)
    (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    eLpNorm (fun u : Rotations n ↦ directionXRayNorm (f ∘ Unitary.linearIsometryEquiv u) r v)
        q (Rotations.probability n) =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ)⁻¹) ^ (1 / q.toReal) *
        sphericalXRayNorm f q r := by
  have hm := measurable_directionXRayNorm hf hr hrfin v
  calc
    _ = eLpNorm (directionXRayNorm f r) q (Rotations.sphereOrbitMeasure v) := by
      rw [Rotations.sphereOrbitMeasure,
        eLpNorm_map_measure hm.aestronglyMeasurable
          (Rotations.measurable_sphereOrbit v).aemeasurable]
      congr 1
      funext u
      exact (directionXRayNorm_rotate hf r u v).symm
    _ = _ := by
      rw [Rotations.sphereOrbitMeasure_eq_normalized_toSphere,
        eLpNorm_smul_measure_of_ne_zero (by
          simpa only [ENNReal.inv_ne_zero] using
            measure_ne_top (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ)]
      simp only [ENNReal.toReal_div, ENNReal.toReal_one, smul_eq_mul, sphericalXRayNorm]

end NKBesicovitch.XRay
