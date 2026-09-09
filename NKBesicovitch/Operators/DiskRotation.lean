/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Defs
public import NKBesicovitch.Grassmannian.Action
public import NKBesicovitch.Grassmannian.Volume
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Rotation covariance of intrinsic disk averages

The induced isometry between a plane and its rotation preserves intrinsic
volume and the unit ball. Rotation covariance of the maximal function then
follows by changing the center over which its supremum is taken.
-/

public section

open MeasureTheory Metric
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

theorem diskAverage_rotate (u : Rotations n) (V : Grassmannian n k)
    (a : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    diskAverage f (Grassmannian.rotate u V) (Unitary.linearIsometryEquiv u a) =
      diskAverage (f ∘ Unitary.linearIsometryEquiv u) V a := by
  let e : V.val ≃ₗᵢ[ℝ] (Grassmannian.rotate u V).val :=
    (Unitary.linearIsometryEquiv u).submoduleMap V.val
  have he : e ⁻¹' closedBall (0 : (Grassmannian.rotate u V).val) 1 =
      closedBall (0 : V.val) 1 := by
    ext x
    simp only [Set.mem_preimage, mem_closedBall_zero_iff, e.norm_map]
  have hi := e.measurePreserving.setLIntegral_comp_preimage_emb
    e.toHomeomorph.measurableEmbedding
    (fun w ↦ f (Unitary.linearIsometryEquiv u a + w))
    (closedBall (0 : (Grassmannian.rotate u V).val) 1)
  rw [he] at hi
  unfold diskAverage
  rw [← hi, Grassmannian.volume_closedBall, Grassmannian.volume_closedBall]
  congr 1
  apply lintegral_congr
  intro w
  change f (Unitary.linearIsometryEquiv u a + Unitary.linearIsometryEquiv u w) = _
  rw [← map_add, Function.comp_apply]

theorem diskMaximal_rotate (u : Rotations n) (V : Grassmannian n k)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    diskMaximal f (Grassmannian.rotate u V) =
      diskMaximal (f ∘ Unitary.linearIsometryEquiv u) V := by
  unfold diskMaximal
  rw [← (Unitary.linearIsometryEquiv u).surjective.iSup_comp
    (fun a ↦ diskAverage f (Grassmannian.rotate u V) a)]
  exact iSup_congr fun a ↦ diskAverage_rotate u V a f

end NKBesicovitch
