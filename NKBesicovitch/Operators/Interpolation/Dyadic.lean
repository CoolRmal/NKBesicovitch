/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Halving scales below a prescribed upper bound

Every positive value at most `B` belongs to one interval
`(B (1/2)^n / 2, B (1/2)^n]`, indexed by a natural number.
The extended-real version records finiteness through the upper bound.
-/

public section

open scoped ENNReal

namespace NKBesicovitch

theorem exists_dyadic_scale {x B : ℝ} (hx : 0 < x) (hB : 0 < B) (hxB : x ≤ B) :
    ∃ n : ℕ, B * (1 / 2 : ℝ) ^ n / 2 < x ∧ x ≤ B * (1 / 2 : ℝ) ^ n := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one (div_pos hx hB)
    ((div_le_one hB).mpr hxB) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  refine ⟨n, ?_, ?_⟩
  · have h := (lt_div_iff₀ hB).mp hn
    rw [pow_succ] at h
    nlinarith
  · simpa only [mul_comm] using (div_le_iff₀ hB).mp hn'

theorem exists_dyadic_scale_ennreal {x : ℝ≥0∞} {B : ℝ} (hx : 0 < x) (hB : 0 < B)
    (hxB : x ≤ ENNReal.ofReal B) :
    ∃ n : ℕ, ENNReal.ofReal (B * (1 / 2 : ℝ) ^ n / 2) < x ∧
      x ≤ ENNReal.ofReal (B * (1 / 2 : ℝ) ^ n) := by
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxB
  have hx' := ENNReal.toReal_pos hx.ne' hfin
  have hupper : x.toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hxB
  obtain ⟨n, hn, hn'⟩ := exists_dyadic_scale hx' hB hupper
  refine ⟨n, ?_, ?_⟩
  · rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hx').mpr hn
  · rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hn'

end NKBesicovitch
