/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.PolarIntegral
public import NKBesicovitch.Geometry.SphereMeasure

/-!
# Averaging integrals over rotated hyperplanes

Polar coordinates in a hyperplane have one fewer radial power than in the
ambient space. Haar averaging makes the angular distribution uniform, so
the averaged hyperplane integral equals an ambient integral with weight
`‖x‖⁻¹` and the ratio of the two sphere areas. Positive hyperplane dimension
excludes the exceptional zero-dimensional fiber, whose volume has an atom.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NKBesicovitch

theorem lintegral_rotate_smul {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (r : ℝ) :
    (∫⁻ u, f (Unitary.linearIsometryEquiv u (r • (v : EuclideanSpace ℝ (Fin n))))
      ∂Rotations.probability n) =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ)⁻¹ *
        ∫⁻ w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, f (r • (w : EuclideanSpace ℝ (Fin n)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  have hm : Measurable (fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
      f (r • (w : EuclideanSpace ℝ (Fin n)))) := hf.comp (by fun_prop)
  have h := Rotations.lintegral_sphereOrbit v v hm
  rw [Rotations.sphereOrbitMeasure_eq_normalized_toSphere, lintegral_smul_measure] at h
  simpa only [map_smul, Rotations.rotateSphere, smul_eq_mul] using h

variable {m : ℕ} [Nonempty (Fin m)] {f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞}

private theorem lintegral_rotate_linearIsometry_polar
    (L : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (hf : Measurable f) :
    (∫⁻ u, ∫⁻ y, f (Unitary.linearIsometryEquiv u (L y)) ∂volume
      ∂Rotations.probability (m + 1)) =
      (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere univ *
        ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere univ)⁻¹ *
          ∫⁻ r : Ioi (0 : ℝ),
            ∫⁻ w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
              f ((r : ℝ) • (w : EuclideanSpace ℝ (Fin (m + 1))))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere
            ∂Measure.volumeIoiPow (m - 1) := by
  have hm : Measurable (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
      f (Unitary.linearIsometryEquiv z.1 (L z.2))) :=
    hf.comp ((continuous_subtype_val.comp continuous_fst).clm_apply
      (L.continuous.comp continuous_snd)).measurable
  rw [lintegral_lintegral_swap hm.aemeasurable]
  rw [lintegral_polar volume (hm.lintegral_prod_left' (μ := Rotations.probability (m + 1)))]
  have he (w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) (r : Ioi (0 : ℝ)) :
      (∫⁻ u, f (Unitary.linearIsometryEquiv u (L ((r : ℝ) • (w : EuclideanSpace ℝ (Fin m)))))
        ∂Rotations.probability (m + 1)) =
        ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere univ)⁻¹ *
          ∫⁻ z : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
            f ((r : ℝ) • (z : EuclideanSpace ℝ (Fin (m + 1))))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere := by
    let z : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
      ⟨L w, by simpa only [mem_sphere, dist_zero_right, L.norm_map] using norm_eq_of_mem_sphere w⟩
    simpa only [map_smul] using lintegral_rotate_smul hf z r
  simp_rw [he]
  rw [lintegral_const_mul' _ _
    (ENNReal.inv_ne_top.mpr (Measure.measure_univ_ne_zero.mpr
      (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere_ne_zero)),
    lintegral_const]
  simp only [finrank_euclideanSpace_fin]
  ac_rfl

private theorem lintegral_inv_norm_polar (hf : Measurable f) :
    (∫⁻ x, (ENNReal.ofReal ‖x‖)⁻¹ * f x) =
      ∫⁻ r : Ioi (0 : ℝ),
        ∫⁻ w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
          f ((r : ℝ) • (w : EuclideanSpace ℝ (Fin (m + 1))))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere
        ∂Measure.volumeIoiPow (m - 1) := by
  rw [lintegral_polar volume (f := fun x ↦ (ENNReal.ofReal ‖x‖)⁻¹ * f x) (by fun_prop)]
  simp only [finrank_euclideanSpace_fin, Nat.add_sub_cancel]
  have he (w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (r : Ioi (0 : ℝ)) :
      (ENNReal.ofReal ‖(r : ℝ) • (w : EuclideanSpace ℝ (Fin (m + 1)))‖)⁻¹ =
        (ENNReal.ofReal (r : ℝ))⁻¹ := by
    rw [norm_smul, norm_eq_of_mem_sphere w, mul_one, Real.norm_eq_abs, abs_of_pos r.property]
  simp_rw [he]
  have hp : 0 < m := Fin.pos_iff_nonempty.mpr inferInstance
  trans ∫⁻ w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
    ∫⁻ r : Ioi (0 : ℝ), f ((r : ℝ) • (w : EuclideanSpace ℝ (Fin (m + 1))))
      ∂Measure.volumeIoiPow (m - 1)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere
  · apply lintegral_congr
    intro w
    exact lintegral_volumeIoiPow_inv hp (hf.comp (by fun_prop))
  · exact lintegral_lintegral_swap (hf.comp (by fun_prop)).aemeasurable

/-- Haar-averaged hyperplane volume is ambient volume weighted by inverse radius. -/
theorem lintegral_rotate_linearIsometry
    (L : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (hf : Measurable f) :
    (∫⁻ u, ∫⁻ y, f (Unitary.linearIsometryEquiv u (L y)) ∂volume
      ∂Rotations.probability (m + 1)) =
      (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere univ *
        ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere univ)⁻¹ *
          ∫⁻ x, (ENNReal.ofReal ‖x‖)⁻¹ * f x := by
  rw [lintegral_rotate_linearIsometry_polar L hf, lintegral_inv_norm_polar hf]

end NKBesicovitch
