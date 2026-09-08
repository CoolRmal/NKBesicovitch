/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Exponents
public import NKBesicovitch.Geometry.Disks
public import NKBesicovitch.Induction.Iteration
public import NKBesicovitch.Induction.Globalization

/-!
# The critical range

The selectable projection estimate, its mixed-norm X-ray consequence, and
the finite plate induction now supply a lower-dimensional deficit below one.
The plate estimate is globalized without changing this deficit.
The proper-dimensional case still requires the Fourier terminal argument.
-/

public section

open MeasureTheory Set

namespace NKBesicovitch.Induction

/-- The critical-range positive-measure theorem, including the full-dimensional boundary. -/
theorem volume_pos_of_criticalExponent {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (h : (n : ℝ) < criticalExponent ^ (k - 1) + (k : ℝ))
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume)
    (hB : IsBesicovitch k E) :
    0 < volume E := by
  obtain rfl | hkn := eq_or_lt_of_le hkn
  · exact volume_pos_of_isBesicovitch_self hB
  · obtain ⟨α, p, hα, hα1, hp, hplate⟩ :=
      exists_hasPlateEstimate_deficit_lt_one hk hkn h
    obtain ⟨C, hC⟩ := hplate.global_bound (by linarith)
    sorry

end NKBesicovitch.Induction
