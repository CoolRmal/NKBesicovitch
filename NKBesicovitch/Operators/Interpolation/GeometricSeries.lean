/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Summing the two interpolated halving scales

Positive powers of both scales give a finite double geometric series.
Its bound is independent of the extended nonnegative coefficient, even
when that coefficient is zero or infinite.
-/

public section

open scoped ENNReal

namespace NKBesicovitch

theorem tsum_dyadic_rpow_ne_top {u : ℝ} (hu : 0 < u) :
    (∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ^ u) ≠ ∞ := by
  have hpow (j : ℕ) : ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ^ u =
      (ENNReal.ofReal (1 / 2) ^ u) ^ j := by
    rw [ENNReal.ofReal_pow (by norm_num), ← ENNReal.rpow_natCast_mul,
      ← ENNReal.rpow_mul_natCast]
    congr 1
    ring
  simp_rw [hpow]
  exact (tsum_geometric_lt_top.mpr (ENNReal.rpow_lt_one (by norm_num) hu)).ne

theorem exists_double_dyadic_constant {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    ∃ D : ℝ, 0 < D ∧ ∀ A : ℝ≥0∞,
      (∑' j : ℕ, ∑' l : ℕ, A * ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ^ u *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ l) ^ v) ≤ ENNReal.ofReal D * A := by
  let U := ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ^ u
  let V := ∑' l : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ l) ^ v
  have hfin : U * V ≠ ∞ := ENNReal.mul_ne_top (tsum_dyadic_rpow_ne_top hu)
    (tsum_dyadic_rpow_ne_top hv)
  refine ⟨(U * V).toReal + 1, by positivity, fun A ↦ ?_⟩
  have hbound : U * V ≤ ENNReal.ofReal ((U * V).toReal + 1) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc
    _ = A * (U * V) := by
      simp only [U, V, mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ ≤ A * ENNReal.ofReal ((U * V).toReal + 1) := mul_le_mul_right hbound A
    _ = _ := mul_comm _ _

end NKBesicovitch
