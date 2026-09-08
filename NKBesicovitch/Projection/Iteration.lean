/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Exponents

/-!
# Arithmetic of the corner iteration

This is the rational update from Sections 2.4 and 13 of the supplied projection
manuscript. Its algebra does not itself prove the geometric corner estimate.
-/

@[expose] public section

namespace NKBesicovitch.Projection

/-- The ideal projection exponent after a corner improvement. -/
noncomputable def cornerUpdate (β : ℝ) : ℝ := (3 * β ^ 2 + 2 * β - 2) / (β ^ 2 + 3 * β - 2)

private lemma denominator_pos_aux {β : ℝ} (hβ : 1 < β) : 0 < β ^ 2 + 3 * β - 2 := by
  nlinarith [sq_nonneg β]

theorem cornerUpdate_sub {β : ℝ} (hβ : 1 < β) :
    cornerUpdate β - β = -(β ^ 3 - 4 * β + 2) / (β ^ 2 + 3 * β - 2) := by
  unfold cornerUpdate
  apply (eq_div_iff (denominator_pos_aux hβ).ne').2
  rw [sub_mul, div_mul_cancel₀ _ (denominator_pos_aux hβ).ne']
  ring

theorem cornerUpdate_projectionExponent : cornerUpdate projectionExponent = projectionExponent := by
  have h := cornerUpdate_sub projectionExponent_mem.1
  rw [projectionExponent_cubic, neg_zero, zero_div, sub_eq_zero] at h
  exact h

theorem cornerUpdate_lt_self {β : ℝ} (hβ : 1 < β) (h : 0 < β ^ 3 - 4 * β + 2) :
    cornerUpdate β < β := by
  rw [← sub_neg, cornerUpdate_sub hβ]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos h) (denominator_pos_aux hβ)

end NKBesicovitch.Projection
