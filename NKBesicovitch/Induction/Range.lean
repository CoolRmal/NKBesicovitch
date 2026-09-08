/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Exponents
public import NKBesicovitch.Geometry.Disks

/-!
# The critical range

The unresolved proper-dimensional case requires the selectable projection
estimate, its mixed-norm X-ray consequence, and the Bourgain–Oberlin induction.
-/

public section

open MeasureTheory Set

namespace NKBesicovitch.Induction

/-- The critical-range positive-measure theorem, including the full-dimensional boundary. -/
theorem volume_pos_of_criticalExponent {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (h : (n : ℝ) < criticalExponent ^ (k - 1) + (k : ℝ))
    {E : Set (Space n)} (hE : NullMeasurableSet E volume) (hB : IsBesicovitch k E) :
    0 < volume E := by
  obtain rfl | hkn := eq_or_lt_of_le hkn
  · exact volume_pos_of_isBesicovitch_self hB
  · sorry

end NKBesicovitch.Induction
