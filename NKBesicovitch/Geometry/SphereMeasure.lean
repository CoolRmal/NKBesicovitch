/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.SphereRotations
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Haar-distributed directions and Euclidean sphere measure

Rotating a fixed unit vector by a Haar-distributed orthogonal operator
gives normalized surface measure. The cone formula proves invariance of
surface measure, and transitivity identifies the invariant probability.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace NKBesicovitch.Rotations

variable {n : ℕ}

theorem measurable_sphereOrbit (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measurable (fun u : Rotations n ↦ rotateSphere u v) :=
  (continuous_rotateSphere.comp (continuous_id.prodMk continuous_const)).measurable

/-- The distribution of a fixed unit vector after an independent Haar rotation. -/
noncomputable def sphereOrbitMeasure (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measure (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (probability n).map (fun u ↦ rotateSphere u v)

instance (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    IsProbabilityMeasure (sphereOrbitMeasure v) :=
  Measure.isProbabilityMeasure_map (measurable_sphereOrbit v).aemeasurable

instance (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    SMulInvariantMeasure (Rotations n) (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
      (sphereOrbitMeasure v) :=
  smulInvariantMeasure_map (probability n) _
    (fun u w ↦ rotateSphere_mul u w v) (measurable_sphereOrbit v)

theorem preimage_sphereCone_rotate (u : Rotations n)
    (s : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    (Unitary.linearIsometryEquiv u) ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      Ioo (0 : ℝ) 1 • (Subtype.val '' (rotateSphere u ⁻¹' s)) := by
  ext x
  constructor
  · rintro ⟨a, ha, _, ⟨w, hw, rfl⟩, h⟩
    have heq : rotateSphere u (rotateSphere u⁻¹ w) = w := by
      rw [← rotateSphere_mul, mul_inv_cancel, rotateSphere_one]
    refine ⟨a, ha, _, ⟨rotateSphere u⁻¹ w, ?_, rfl⟩, ?_⟩
    · change rotateSphere u (rotateSphere u⁻¹ w) ∈ s
      rwa [heq]
    · apply (Unitary.linearIsometryEquiv u).injective
      change Unitary.linearIsometryEquiv u
        (a • (rotateSphere u⁻¹ w : EuclideanSpace ℝ (Fin n))) = _
      rw [map_smul]
      change a • (rotateSphere u (rotateSphere u⁻¹ w) : EuclideanSpace ℝ (Fin n)) = _
      simpa only [heq] using h
  · rintro ⟨a, ha, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨a, ha, _, ⟨rotateSphere u w, hw, rfl⟩, ?_⟩
    exact (map_smul (Unitary.linearIsometryEquiv u) a
      (w : EuclideanSpace ℝ (Fin n))).symm

theorem measurePreserving_rotateSphere (u : Rotations n) :
    MeasurePreserving (rotateSphere u)
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  have hm : Measurable (rotateSphere u) :=
    (continuous_rotateSphere.comp (continuous_const.prodMk continuous_id)).measurable
  refine ⟨hm, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' _ (hs.preimage hm),
    Measure.toSphere_apply' _ hs, ← preimage_sphereCone_rotate]
  congr 1
  exact (Unitary.linearIsometryEquiv u).measurePreserving.measure_preimage_emb
    (Unitary.linearIsometryEquiv u).toHomeomorph.measurableEmbedding _

instance : SMulInvariantMeasure (Rotations n) (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere where
  measure_preimage_smul u _ hs :=
    (measurePreserving_rotateSphere u).measure_preimage hs.nullMeasurableSet

theorem sphereOrbitMeasure_rotate (u : Rotations n)
    (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    sphereOrbitMeasure (rotateSphere u v) = sphereOrbitMeasure v := by
  unfold sphereOrbitMeasure
  simp_rw [← rotateSphere_mul]
  change Measure.map ((fun w ↦ rotateSphere w v) ∘ (· * u)) _ = _
  rw [← Measure.map_map (measurable_sphereOrbit v)
    (continuous_mul_const u).measurable, map_mul_right_eq_self]

theorem sphereOrbitMeasure_eq (v w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    sphereOrbitMeasure v = sphereOrbitMeasure w := by
  obtain ⟨u, rfl⟩ := exists_rotateSphere_eq v w
  exact (sphereOrbitMeasure_rotate u v).symm

theorem lintegral_sphereOrbit (v w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {f : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u, f (rotateSphere u w) ∂probability n) = ∫⁻ z, f z ∂sphereOrbitMeasure v := by
  rw [sphereOrbitMeasure_eq v w]
  exact (lintegral_map hf (measurable_sphereOrbit w)).symm

/-- There is a unique rotation-invariant probability measure on unit directions. -/
theorem eq_sphereOrbitMeasure_of_invariant (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (μ : Measure (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure (Rotations n) (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) μ] :
    μ = sphereOrbitMeasure v := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hinv (u : Rotations n) : (∫⁻ w, f (rotateSphere u w) ∂μ) = ∫⁻ w, f w ∂μ :=
    (measurePreserving_smul u μ).lintegral_comp hf
  calc
    (∫⁻ w, f w ∂μ) = ∫⁻ u, ∫⁻ w, f (rotateSphere u w) ∂μ ∂probability n := by
      simp only [hinv, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ w, ∫⁻ u, f (rotateSphere u w) ∂probability n ∂μ :=
      lintegral_lintegral_swap (hf.comp continuous_rotateSphere.measurable).aemeasurable
    _ = ∫⁻ w, f w ∂sphereOrbitMeasure v := by
      simp only [lintegral_sphereOrbit v _ hf, lintegral_const, measure_univ, mul_one]

/-- A Haar-distributed unit vector has normalized Euclidean surface measure. -/
theorem sphereOrbitMeasure_eq_normalized_toSphere
    (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    sphereOrbitMeasure v =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ)⁻¹ •
        (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  have hμ0 : μ univ ≠ 0 := isOpen_univ.measure_ne_zero μ ⟨v, mem_univ v⟩
  let : IsProbabilityMeasure ((μ univ)⁻¹ • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hμ0 (measure_ne_top μ univ)]⟩
  exact (eq_sphereOrbitMeasure_of_invariant v ((μ univ)⁻¹ • μ)).symm

end NKBesicovitch.Rotations
