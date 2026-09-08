/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Defs
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.Prod

/-!
# The two-slice projection estimate

The map from a line's intercept and slope to its positions at two heights has
determinant `(t - s)^m`. Its inverse image of the product of the two projection
images contains the line family. Lebesgue outer measure suffices throughout.
This is equation (40) of the supplied projection manuscript.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Encode a line by its positions at two specified heights. -/
def twoSlice (s t : ℝ) : Line m →ₗ[ℝ] Line m :=
  ((LinearMap.fst ℝ (Space m) (Space m)) + s • LinearMap.snd ℝ (Space m) (Space m)).prod
    ((LinearMap.fst ℝ (Space m) (Space m)) + t • LinearMap.snd ℝ (Space m) (Space m))

theorem twoSlice_apply (s t : ℝ) (g : Line m) :
    twoSlice s t g = (atHeight s g, atHeight t g) := rfl

theorem twoSlice_toMatrix (s t : ℝ) (b : Module.Basis (Fin m) ℝ (Space m)) :
    LinearMap.toMatrix (b.prod b) (b.prod b) (twoSlice s t) =
    Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ) (s • 1) 1 (t • 1) := by
  ext (i | i) (j | j) <;>
    simp [LinearMap.toMatrix, twoSlice, Matrix.one_apply, mul_ite, Finsupp.single_apply, eq_comm]

theorem det_twoSlice (s t : ℝ) : LinearMap.det (twoSlice (m := m) s t) = (t - s) ^ m := by
  rw [← LinearMap.det_toMatrix ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis.prod
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis), twoSlice_toMatrix,
    Matrix.det_fromBlocks_one₁₁, one_mul, ← sub_smul]
  simp

/-- The seed projection bound, with its exact time-separation constant. -/
theorem volume_le_two_slice {s t : ℝ} (hst : s ≠ t) (G : Set (Line m)) :
    volume G ≤ ENNReal.ofReal |((t - s) ^ m)⁻¹| *
      (volume (atHeight s '' G) * volume (atHeight t '' G)) := by
  have : Measure.IsAddHaarMeasure (volume : Measure (Line m)) := by
    change Measure.IsAddHaarMeasure
      ((volume : Measure (Space m)).prod (volume : Measure (Space m)))
    infer_instance
  have hd : LinearMap.det (twoSlice (m := m) s t) ≠ 0 := by
    rw [det_twoSlice]
    exact pow_ne_zero _ (sub_ne_zero.mpr hst.symm)
  calc
    volume G ≤ volume (twoSlice s t ⁻¹' ((atHeight s '' G) ×ˢ (atHeight t '' G))) :=
      measure_mono fun g hg ↦ ⟨mem_image_of_mem _ hg, mem_image_of_mem _ hg⟩
    _ = _ := by
      rw [Measure.addHaar_preimage_linearMap (volume : Measure (Line m)) hd,
        det_twoSlice, Measure.volume_eq_prod, Measure.prod_prod]

end NKBesicovitch.Projection
