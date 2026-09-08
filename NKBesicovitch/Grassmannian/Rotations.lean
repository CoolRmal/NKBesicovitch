/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Orthogonal operators and their Haar probability measure

The full orthogonal group is realized as the unitary continuous endomorphisms
of a real Euclidean space, with the operator norm topology.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace

namespace NKBesicovitch

/-- The full orthogonal group of Euclidean n-space, including reflections. -/
noncomputable abbrev Rotations (n : ℕ) :=
  unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))

namespace Rotations

variable {n : ℕ}

instance : CompactSpace (Rotations n) := by
  apply isCompact_iff_compactSpace.mp
  refine (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n)) 1).of_isClosed_subset
    isClosed_unitary ?_
  intro u hu
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x ↦ by simp [ContinuousLinearMap.norm_map_of_mem_unitary hu])

noncomputable instance : MeasurableSpace (Rotations n) := borel (Rotations n)

instance : BorelSpace (Rotations n) := ⟨rfl⟩

/-- Haar measure normalized by the entire compact orthogonal group. -/
noncomputable def probability (n : ℕ) : Measure (Rotations n) :=
  Measure.haarMeasure ⊤

instance : IsProbabilityMeasure (probability n) where
  measure_univ := Measure.haarMeasure_self

instance : Measure.IsHaarMeasure (probability n) := by
  unfold probability
  infer_instance

instance : Measure.IsMulRightInvariant (probability n) where
  map_mul_right_eq_self u := by
    have : IsProbabilityMeasure ((probability n).map (· * u)) :=
      Measure.isProbabilityMeasure_map (continuous_mul_const u).measurable.aemeasurable
    exact ((Measure.haarMeasure_eq_iff ⊤ _).mpr (by simp)).symm

end Rotations

end NKBesicovitch
