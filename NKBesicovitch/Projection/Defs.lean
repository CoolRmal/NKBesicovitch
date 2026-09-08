/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Basic
public import Mathlib.MeasureTheory.Function.EssSup

/-!
# Slope-intercept line families

A line is encoded by its intercept x and slope ξ; its horizontal position at
height t is x + tξ. Projection image volumes below are Lebesgue outer measures,
so the definitions do not assert Borel measurability of arbitrary images.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

/-- Nonhorizontal lines in one higher dimension, represented by intercept and slope. -/
abbrev Line (m : ℕ) := Space m × Space m

/-- Horizontal position at height t. -/
def atHeight {m : ℕ} (t : ℝ) (g : Line m) : Space m := g.1 + t • g.2

/-- Essential supremum of the measures of parallel subfamilies. -/
noncomputable def parallelMultiplicity {m : ℕ} (G : Set (Line m)) : ℝ≥0∞ :=
  essSup (fun ξ : Space m ↦ volume {x : Space m | (x, ξ) ∈ G}) volume

/-- Largest outer measure of a projection onto the selected finite set of heights. -/
noncomputable def sliceSize {m : ℕ} (Γ : Finset ℝ) (G : Set (Line m)) : ℝ≥0∞ :=
  ⨆ t ∈ Γ, volume (atHeight t '' G)

end NKBesicovitch.Projection
