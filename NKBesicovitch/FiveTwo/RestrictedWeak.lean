/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.Measure
public import NKBesicovitch.Operators.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The remaining four-dimensional restricted weak estimate

The corrected Guth–Zahl shading exponent is `121/40`. The shading loss `39/40`
and two losses of `1/160` give deficit `79/80`. The required estimate below
includes arbitrary translations, canonical direction measure, and the project's
radius-one disk plates. Its proof must supply polynomial concentration,
shading, direction packing, spatial localization, and the fixed tube rescaling.
It remains unproved; the following `sorry` is the independent geometric gap.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NKBesicovitch.FiveTwo

/-- The four-dimensional restricted weak estimate with exponent `121/40` and loss `79/80`. -/
theorem restricted_weak_plateMaximal :
    ∃ A : ℝ≥0, ∀ δ : ℝ≥0, 0 < δ → δ ≤ 1 →
      ∀ E : Set (EuclideanSpace ℝ (Fin 4)), MeasurableSet E → volume E ≠ ∞ →
        ∀ s : ℝ≥0, 0 < s → (Grassmannian.probability (show 1 ≤ 4 by decide))
          {V | (s : ℝ≥0∞) < plateMaximal δ (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) V} ≤
            (A * δ ^ (-(79 / 80 : ℝ)) : ℝ≥0) * (s : ℝ≥0∞) ^ (-(121 / 40 : ℝ)) * volume E := by
  sorry

end NKBesicovitch.FiveTwo
