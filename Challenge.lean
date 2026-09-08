/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Positive measure for (n,k)-Besicovitch sets

The general positive-measure target uses the unique root `p_c ∈ (2,3)` of
`p_c³ - 2p_c² - 2p_c + 2 = 0`. Its numerical bounds are a separate target below.
The `(5,2)` positive-measure target lies outside the general dimension range.
`NullMeasurableSet` means measurability in the completion of Lebesgue measure.
The deliberate `sorry`s specify the challenge; they are not proofs of the claims.
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

/-- The exact rational bounds `2.481 < p_c < 2.482`. -/
theorem criticalExponent_bounds :
    2.481 < criticalExponent ∧ criticalExponent < 2.482 := by
  sorry

/-- Besicovitch sets have positive measure when `p_c^(k-1) + k > n`. -/
theorem volume_pos_of_criticalExponent {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (h : (n : ℝ) < criticalExponent ^ (k - 1) + (k : ℝ))
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume)
    (hB : IsBesicovitch k E) :
    0 < volume E := by
  sorry

/-- Every Lebesgue measurable `(5,2)`-Besicovitch set has positive measure.

This is not implied by `volume_pos_of_criticalExponent`: for `k = 2`, that theorem
requires `n < p_c + 2`, while `p_c + 2 < 4.482 < 5`. -/
theorem volume_pos_five_two {E : Set (EuclideanSpace ℝ (Fin 5))} (hE : NullMeasurableSet E volume)
    (hB : IsBesicovitch 2 E) : 0 < volume E := by
  sorry

end NKBesicovitch
