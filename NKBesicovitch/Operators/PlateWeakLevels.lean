/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.PlateLevels
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Applying a restricted weak estimate to input superlevels

The summable superlevel cover converts a restricted weak bound for indicators
to a bound for arbitrary Borel inputs of finite-measure support. All level sets
have finite measure because their thresholds are strictly positive, even if
the input itself takes infinite values.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NKBesicovitch

variable {n k : ℕ} {δ : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

/-- Restricted weak control bounds each maximal superlevel by a weighted input-level sum. -/
theorem measure_plateMaximal_superlevel_le_tsum (ν : Measure (Grassmannian n k))
    (hδ : 0 < δ) {A : ℝ≥0∞} {P : ℝ}
    (hweak : ∀ E : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet E → volume E ≠ ∞ →
      ∀ s : ℝ≥0, 0 < s → ν {V | (s : ℝ≥0∞) <
        plateMaximal δ (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) V} ≤
          A * (s : ℝ≥0∞) ^ (-P) * volume E)
    (hf : Measurable f) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : volume K ≠ ∞) (hs : Function.support f ⊆ K)
    (t : ℝ≥0) (ht : 0 < t) (a : ℕ → ℝ≥0) (ha : ∀ j, 0 < a j)
    (hasum : (∑' j : ℕ, (2 : ℝ≥0∞) ^ j * (a j : ℝ≥0∞)) ≤ (2 : ℝ≥0∞)⁻¹) :
    ν {V | (t : ℝ≥0∞) < plateMaximal δ f V} ≤
      A * ∑' j : ℕ, (a j : ℝ≥0∞) ^ (-P) *
        volume {x | (t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j / 2 ≤ f x} := by
  have hsub (j : ℕ) : {x | (t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j / 2 ≤ f x} ⊆ K := by
    intro x hx
    apply hs
    have hpos : 0 < (t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j / 2 := ENNReal.div_pos
      (mul_ne_zero (ENNReal.coe_ne_zero.mpr ht.ne') (pow_ne_zero _ (by norm_num))) (by norm_num)
    exact (hpos.trans_le hx).ne'
  apply (measure_mono (plateMaximal_superlevel_subset_iUnion hδ hf t ht
    (fun j ↦ (a j : ℝ≥0∞)) hasum)).trans
  apply (measure_iUnion_le _).trans
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  simpa only [mul_assoc] using hweak _ (measurableSet_le measurable_const hf)
    (ne_top_of_le_ne_top hK (measure_mono (hsub j))) (a j) (ha j)

end NKBesicovitch
