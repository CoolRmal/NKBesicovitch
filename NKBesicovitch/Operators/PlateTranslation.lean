/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.PlateRotation

/-!
# Translation invariance of plate maximal functions

Translating the input only changes the center over which the supremum is
taken. The covariance holds for arbitrary nonnegative inputs, including
infinite values, by the measurable change of variables for translations.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

theorem preimage_plate_add_right (a y : EuclideanSpace ℝ (Fin n))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    (fun x ↦ x + y) ⁻¹' plate δ V (a + y) = plate δ V a := by
  have hi : (fun x ↦ x + y) '' unitDisk V a = unitDisk V (a + y) := by
    have he : (fun x ↦ x + y) ⁻¹' unitDisk V (a + y) = unitDisk V a := by
      ext x
      simp only [mem_preimage, unitDisk, mem_ofPred_eq, add_sub_add_right_eq_sub]
    rw [← he]
    exact (Homeomorph.addRight y).surjective.image_preimage _
  rw [plate, ← hi]
  ext x
  simp only [mem_preimage, plate, mem_thickening_iff_infEDist_lt,
    infEDist_image (isometry_add_right y)]

theorem plateAverage_add_right (a y : EuclideanSpace ℝ (Fin n))
    (V : Grassmannian n k) (δ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    (∫⁻ x in plate δ V.val (a + y), f x) / volume (plate δ V.val (a + y)) =
      (∫⁻ x in plate δ V.val a, f (x + y)) / volume (plate δ V.val a) := by
  have hi := (measurePreserving_add_right volume y).setLIntegral_comp_preimage_emb
    (Homeomorph.addRight y).measurableEmbedding f (plate δ V.val (a + y))
  have hv := (measurePreserving_add_right volume y).measure_preimage_emb
    (Homeomorph.addRight y).measurableEmbedding (plate δ V.val (a + y))
  rw [preimage_plate_add_right] at hi hv
  rw [← hi, ← hv]

theorem plateMaximal_add_right (y : EuclideanSpace ℝ (Fin n)) (V : Grassmannian n k)
    (δ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    plateMaximal δ (fun x ↦ f (x + y)) V = plateMaximal δ f V := by
  apply le_antisymm
  · apply iSup_le
    intro a
    rw [← plateAverage_add_right]
    exact le_iSup (fun a ↦ (∫⁻ x in plate δ V.val a, f x) / volume (plate δ V.val a)) (a + y)
  · apply iSup_le
    intro z
    obtain ⟨a, rfl⟩ := (Homeomorph.addRight y).surjective z
    change (∫⁻ x in plate δ V.val (a + y), f x) / volume (plate δ V.val (a + y)) ≤ _
    rw [plateAverage_add_right]
    exact le_iSup (fun a ↦ (∫⁻ x in plate δ V.val a, f (x + y)) /
      volume (plate δ V.val a)) a

end NKBesicovitch
