/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Defs
public import Mathlib.Tactic.NormNum

/-!
# Disk averages on sets containing disks

The denominator in each disk average is strictly positive and finite, including
zero-dimensional subspaces. A set containing a disk therefore has average one.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

theorem diskAverage_indicator_eq_one (V : Grassmannian n k) (a : EuclideanSpace ℝ (Fin n))
    {E : Set (EuclideanSpace ℝ (Fin n))} (h : unitDisk V.val a ⊆ E) :
    diskAverage (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) V a = 1 := by
  have he : ∀ v ∈ Metric.closedBall (0 : V.val) 1,
      E.indicator (fun _ ↦ (1 : ℝ≥0∞)) (a + v) = 1 := by
    intro v hv
    apply Set.indicator_of_mem
    apply h
    simpa [unitDisk, Metric.mem_closedBall, dist_zero_right] using
      And.intro v.property hv
  unfold diskAverage
  rw [setLIntegral_congr_fun measurableSet_closedBall he, setLIntegral_const, one_mul]
  exact ENNReal.div_self (Metric.measure_closedBall_pos volume _ (by norm_num)).ne'
    measure_closedBall_lt_top.ne

/-- The disk maximal function of a Besicovitch-set indicator is at least one in every direction. -/
theorem one_le_diskMaximal_indicator {E : Set (EuclideanSpace ℝ (Fin n))} (h : IsBesicovitch k E)
    (V : Grassmannian n k) : 1 ≤ diskMaximal (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) V := by
  obtain ⟨a, ha⟩ := isBesicovitch_iff_unitDisk_subset.mp h V.val V.property
  rw [diskMaximal]
  exact (diskAverage_indicator_eq_one V a ha).symm.le.trans (le_iSup _ a)

end NKBesicovitch
