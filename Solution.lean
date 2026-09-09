/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Exponents
public import NKBesicovitch.Induction.Range
public import NKBesicovitch.FiveTwo.Main

/-!
# Solution interface

This module deliberately does not import Challenge. The critical-exponent bound
and general positive-measure theorem are proved with only the standard axioms.
The independent `(5,2)` theorem still contains a proof gap, so the complete
interface is not yet a passing Comparator solution.
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

/-- Every Lebesgue measurable `(5,2)`-Besicovitch set has positive measure.

This is not implied by `volume_pos_of_criticalExponent`: for `k = 2`, that theorem
requires `n < p_c + 2`, while `p_c + 2 < 4.482 < 5`. -/
theorem volume_pos_five_two {E : Set (EuclideanSpace ℝ (Fin 5))} (hE : NullMeasurableSet E volume)
    (hB : IsBesicovitch 2 E) : 0 < volume E := FiveTwo.volume_pos hE hB

end NKBesicovitch
