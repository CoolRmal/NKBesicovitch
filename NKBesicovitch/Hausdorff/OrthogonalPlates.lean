/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.Plates
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.Linarith

/-!
# Orthogonal cylinders inside and around plates

Tangential and normal coordinates preserve volume. At thickness at most
one, a unit-disk plate lies between cylinders with tangential radii one
and two and the same normal radius.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NKBesicovitch.Hausdorff

variable {n : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))

theorem measurePreserving_orthogonal_add (a : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (fun z : V × Vᗮ ↦ a + (z.1 : EuclideanSpace ℝ (Fin n)) + z.2)
      volume volume := by
  have h := (measurePreserving_add_left volume a).comp
    (V.orthogonalDecomposition.symm.measurePreserving.comp
      (WithLp.volume_preserving_toLp V Vᗮ))
  simpa [Function.comp_def, Submodule.orthogonalDecomposition_symm_apply, add_assoc] using h

theorem orthogonal_components_mem_of_mem_plate {a x : EuclideanSpace ℝ (Fin n)}
    {δ : ℝ} (hδ : δ ≤ 1) (hx : x ∈ plate δ V a) :
    V.orthogonalProjectionOnto (x - a) ∈ closedBall 0 2 ∧
      Vᗮ.orthogonalProjectionOnto (x - a) ∈ ball 0 δ := by
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
  have he (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
      W.orthogonalProjectionOnto (x - a) =
        W.orthogonalProjectionOnto (x - y) + W.orthogonalProjectionOnto (y - a) := by
    rw [← map_add, sub_add_sub_cancel]
  constructor
  · rw [mem_closedBall_zero_iff, he]
    have h := (norm_add_le (V.orthogonalProjectionOnto (x - y))
      (V.orthogonalProjectionOnto (y - a))).trans
      (add_le_add (V.norm_orthogonalProjectionOnto_apply_le _)
        (V.norm_orthogonalProjectionOnto_apply_le _))
    have hd : ‖x - y‖ < δ := by simpa only [dist_eq_norm] using hxy
    exact h.trans (by linarith [hy.2])
  · rw [mem_ball_zero_iff, he,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
        (show y - a ∈ Vᗮᗮ by simpa using hy.1), add_zero]
    exact (Vᗮ.norm_orthogonalProjectionOnto_apply_le _).trans_lt
      (by simpa only [dist_eq_norm] using hxy)

theorem orthogonal_cylinder_subset_plate (a : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    closedBall (0 : V) 1 ×ˢ ball (0 : Vᗮ) δ ⊆
      (fun z : V × Vᗮ ↦ a + (z.1 : EuclideanSpace ℝ (Fin n)) + z.2) ⁻¹' plate δ V a := by
  rintro ⟨v, w⟩ ⟨hv, hw⟩
  refine mem_thickening_iff.mpr ⟨a + v, ?_, ?_⟩
  · simpa [unitDisk, mem_closedBall_zero_iff] using And.intro v.property hv
  · simpa [dist_eq_norm, mem_ball_zero_iff] using hw

theorem preimage_plate_subset_orthogonal_cylinder (a : EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : δ ≤ 1) :
    (fun z : V × Vᗮ ↦ a + (z.1 : EuclideanSpace ℝ (Fin n)) + z.2) ⁻¹' plate δ V a ⊆
      closedBall (0 : V) 2 ×ˢ ball (0 : Vᗮ) δ := by
  rintro ⟨v, w⟩ hx
  have h := orthogonal_components_mem_of_mem_plate V hδ hx
  simpa [add_sub_cancel_left, add_sub_assoc, map_add,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal w.property,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
      (show (v : EuclideanSpace ℝ (Fin n)) ∈ Vᗮᗮ by simp)] using h

theorem volume_plate_le_orthogonal_cylinder (a : EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : δ ≤ 1) :
    volume (plate δ V a) ≤
      volume (closedBall (0 : V) 2) * volume (ball (0 : Vᗮ) δ) := by
  have h := measure_mono (μ := volume) (preimage_plate_subset_orthogonal_cylinder V a hδ)
  have hm : MeasurableSet (plate δ V a) := isOpen_thickening.measurableSet
  rw [(measurePreserving_orthogonal_add V a).measure_preimage
    hm.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod] at h
  exact h

end NKBesicovitch.Hausdorff
