/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.FiveTwo.Maximal
public import NKBesicovitch.Induction.TerminalPositiveMeasure

/-!
# The five-dimensional two-plane target

The four-dimensional restricted weak estimate gives maximal loss `79/80`
at exponent four. The proved Fourier terminal argument then gives positive
measure. The geometric restricted weak input remains a proof obligation.
-/

public section

open MeasureTheory Set

namespace NKBesicovitch.FiveTwo

/-- Every Lebesgue measurable `(5,2)`-Besicovitch set has positive volume.

The general critical-exponent theorem requires `n < p_c + 2` when `k = 2`.
Since `p_c + 2 < 4.482 < 5`, this case needs a separate proof. -/
theorem volume_pos {E : Set (EuclideanSpace ℝ (Fin 5))} (_hE : NullMeasurableSet E volume)
    (hB : IsBesicovitch 2 E) : 0 < volume E := by
  exact hasPlateEstimate_four_one.volume_pos (by norm_num) (by norm_num) hB

end NKBesicovitch.FiveTwo
