/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.TerminalGlobal
public import NKBesicovitch.PositiveMeasure.FromSchwartz

/-!
# Positive measure from a subunit plate deficit

The Fourier terminal estimate, smooth localization, approximation of open
indicators, and outer regularity convert a plate deficit below one into
positive measure after increasing both dimensions by one.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

/-- The terminal step converts a subunit plate deficit to positive measure one dimension up. -/
theorem HasPlateEstimate.volume_pos {m k : ℕ} [Nonempty (Fin m)]
    {hkm : k ≤ m} {α p : ℝ} (h : HasPlateEstimate hkm α p) (hα : α < 1) (hp : 2 ≤ p)
    {E : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hE : IsBesicovitch (k + 1) E) :
    0 < volume E := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  let q : ℝ≥0 := .mk p hp0.le
  have hq : 0 < q := hp0
  have he : ENNReal.ofReal p = (q : ℝ≥0∞) := ENNReal.ofReal_eq_coe_nnreal hp0.le
  obtain ⟨C, hC⟩ := h.exists_eLpNorm_diskMaximal_schwartz_global_le hα hp
  rw [he] at hC
  exact volume_pos_of_schwartz_diskMaximal_bound
    (Grassmannian.probability (Nat.succ_le_succ hkm)) hq C hC hE

end NKBesicovitch.Induction
