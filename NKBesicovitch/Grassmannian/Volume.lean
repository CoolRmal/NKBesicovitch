/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Intrinsic ball volume in each direction

An orthonormal basis identifies a `k`-plane with Euclidean `k`-space while
preserving its canonical volume. In particular, disk normalization is
independent of the direction.
-/

public section

open MeasureTheory Metric

namespace NKBesicovitch.Grassmannian

/-- Intrinsic centered ball volume depends only on the dimension and radius. -/
theorem volume_closedBall (V : Grassmannian n k) (r : ℝ) :
    volume (closedBall (0 : V.val) r) =
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) := by
  let e : V.val ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) :=
    ((stdOrthonormalBasis ℝ V.val).reindex (finCongr V.property)).repr
  have he : e ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin k)) r = closedBall (0 : V.val) r := by
    ext x
    simp only [Set.mem_preimage, mem_closedBall_zero_iff, e.norm_map]
  rw [← he]
  exact e.measurePreserving.measure_preimage measurableSet_closedBall.nullMeasurableSet

end NKBesicovitch.Grassmannian
