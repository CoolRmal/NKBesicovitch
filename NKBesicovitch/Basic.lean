/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Euclidean Besicovitch sets

The geometric predicate uses closed disks of radius one in every linear direction.
Measurability is a separate hypothesis in the final theorems.
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch

/-- A set containing a translate of the closed unit disk in every k-dimensional direction. -/
def IsBesicovitch {n : ℕ} (k : ℕ) (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)), Module.finrank ℝ V = k →
    ∃ a : EuclideanSpace ℝ (Fin n), ∀ v ∈ V, ‖v‖ ≤ 1 → a + v ∈ E

/-- The exact critical ratio, specified by the roots of its cubic in `[2,3]`. -/
noncomputable def criticalExponent : ℝ :=
  sSup {p : ℝ | p ∈ Icc 2 3 ∧ p ^ 3 - 2 * p ^ 2 - 2 * p + 2 = 0}

end NKBesicovitch
