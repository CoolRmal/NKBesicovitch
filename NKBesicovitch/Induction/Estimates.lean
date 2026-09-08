/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.Measure
public import NKBesicovitch.Operators.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Local diagonal plate estimates and their dimension deficit

The estimate is uniform over positive thicknesses and Borel nonnegative
inputs supported in any fixed centered ball. The factor `δ^(-α/p)` records
the dimension deficit `α`. Applications require a finite real `p ≥ 1`.
Using positive nonnegative-real thicknesses keeps every coefficient finite.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

/-- A local diagonal maximal estimate with deficit `α` and input exponent `p`. -/
def HasPlateEstimate {n k : ℕ} (hkn : k ≤ n) (α p : ℝ) : Prop :=
  ∀ R : ℝ≥0, ∃ C : ℝ≥0, ∀ δ : ℝ≥0, 0 < δ →
    ∀ f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable f →
      Function.support f ⊆ closedBall 0 (R : ℝ) →
        eLpNorm (plateMaximal δ f) (ENNReal.ofReal p) (Grassmannian.probability hkn) ≤
          (C * δ ^ (-α / p) : ℝ≥0) * eLpNorm f (ENNReal.ofReal p) volume

end NKBesicovitch.Induction
