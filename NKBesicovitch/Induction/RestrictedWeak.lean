/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.SmallThickness
public import NKBesicovitch.Operators.PlateWeakStrong

/-!
# Plate induction bounds from restricted weak estimates

A small-thickness restricted weak estimate with loss `δ^(-α)` gives the
diagonal induction estimate with loss `δ^(-α/p)` at every finite `p > P`.
The ambient estimate supplies the large-thickness part when `α ≤ n`.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

/-- A uniform restricted weak plate estimate supplies the corresponding induction bound. -/
theorem hasPlateEstimate_of_restricted_weak {n k : ℕ} (hkn : k ≤ n) {α P p : ℝ}
    (hα : α ≤ n) (hP : 0 < P) (hPp : P < p) (hp : 1 ≤ p)
    (hweak : ∃ A : ℝ≥0, ∀ δ : ℝ≥0, 0 < δ → δ ≤ 1 →
      ∀ E : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet E → volume E ≠ ∞ →
        ∀ s : ℝ≥0, 0 < s → (Grassmannian.probability hkn)
          {V | (s : ℝ≥0∞) < plateMaximal δ (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) V} ≤
            (A * δ ^ (-α) : ℝ≥0) * (s : ℝ≥0∞) ^ (-P) * volume E) :
    HasPlateEstimate hkn α p := by
  obtain ⟨A, hA⟩ := hweak
  obtain ⟨C, hC⟩ := exists_plateMaximal_eLpNorm_bound (n := n) (k := k) hP hPp
  apply hasPlateEstimate_of_small_thickness hkn hα hp
  intro R
  refine ⟨C * A ^ (1 / p), fun δ hδ hδ1 f hf hs ↦ ?_⟩
  have hi := (one_div_pos.mpr (hP.trans hPp)).le
  have h := hC (Grassmannian.probability hkn) δ (A * δ ^ (-α) : ℝ≥0) hδ
    (hA δ hδ hδ1) f hf (closedBall 0 (R : ℝ)) measure_closedBall_lt_top.ne hs
  apply h.trans_eq
  rw [← ENNReal.coe_rpow_of_nonneg _ hi, NNReal.mul_rpow, ← NNReal.rpow_mul]
  simp only [mul_one_div, ENNReal.coe_mul, mul_assoc]

end NKBesicovitch.Induction
