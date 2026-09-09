/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Exponents
public import NKBesicovitch.Induction.Range
public import NKBesicovitch.Hausdorff.Range

/-!
# Solution interface

This module deliberately does not import Challenge. The critical-exponent bound
and the positive-measure and Hausdorff-dimension theorems use only the standard axioms.
-/

public section

open MeasureTheory Set

namespace NKBesicovitch

/-- Besicovitch sets have positive measure when `p_c^(k-1) + k > n`. -/
theorem volume_pos_of_criticalExponent {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (h : (n : ℝ) < criticalExponent ^ (k - 1) + (k : ℝ))
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume)
    (hB : IsBesicovitch k E) :
    0 < volume E :=
  Induction.volume_pos_of_criticalExponent hk hkn h hE hB

/-- Every `(n,k)`-Besicovitch set has Hausdorff dimension at least `n - (n-k)/p_c^k`. -/
theorem le_dimH_of_isBesicovitch {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hB : IsBesicovitch k E) :
    ENNReal.ofReal ((n : ℝ) - ((n : ℝ) - k) / criticalExponent ^ k) ≤ dimH E :=
  Hausdorff.le_dimH_of_isBesicovitch hk hkn hB

end NKBesicovitch
