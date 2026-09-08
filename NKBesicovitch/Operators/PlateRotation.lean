/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.RigidMotions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Rotation covariance of plate maximal functions

Orthogonal changes of variables preserve plate integrals and their
normalizing volumes. Bijectivity of the change of center therefore
gives exact covariance of the supremum over all centers.
-/

public section

open MeasureTheory Metric
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

theorem plateAverage_rotate (u : Rotations n) (a : EuclideanSpace ℝ (Fin n))
    (V : Grassmannian n k) (δ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    (∫⁻ z in plate δ (Grassmannian.rotate u V).val (Unitary.linearIsometryEquiv u a), f z) /
        volume (plate δ (Grassmannian.rotate u V).val (Unitary.linearIsometryEquiv u a)) =
      (∫⁻ z in plate δ V.val a, f (Unitary.linearIsometryEquiv u z)) /
        volume (plate δ V.val a) := by
  have hi := (Unitary.linearIsometryEquiv u).measurePreserving.setLIntegral_comp_preimage_emb
    (Unitary.linearIsometryEquiv u).toHomeomorph.measurableEmbedding f
    (plate δ (Grassmannian.rotate u V).val (Unitary.linearIsometryEquiv u a))
  have hvol := (Unitary.linearIsometryEquiv u).measurePreserving.measure_preimage_emb
    (Unitary.linearIsometryEquiv u).toHomeomorph.measurableEmbedding
    (plate δ (Grassmannian.rotate u V).val (Unitary.linearIsometryEquiv u a))
  rw [preimage_plate_rotate] at hi hvol
  rw [← hi, ← hvol]

theorem plateMaximal_rotate (u : Rotations n) (V : Grassmannian n k) (δ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    plateMaximal δ f (Grassmannian.rotate u V) =
      plateMaximal δ (f ∘ Unitary.linearIsometryEquiv u) V := by
  apply le_antisymm
  · apply iSup_le
    intro z
    obtain ⟨a, rfl⟩ := (Unitary.linearIsometryEquiv u).surjective z
    rw [plateAverage_rotate]
    exact le_iSup (fun c ↦ (∫⁻ z in plate δ V.val c, f (Unitary.linearIsometryEquiv u z)) /
      volume (plate δ V.val c)) a
  · apply iSup_le
    intro a
    change (∫⁻ z in plate δ V.val a, f (Unitary.linearIsometryEquiv u z)) / _ ≤ _
    rw [← plateAverage_rotate]
    exact le_iSup (fun c ↦ (∫⁻ z in plate δ (Grassmannian.rotate u V).val c, f z) /
      volume (plate δ (Grassmannian.rotate u V).val c)) (Unitary.linearIsometryEquiv u a)

end NKBesicovitch
