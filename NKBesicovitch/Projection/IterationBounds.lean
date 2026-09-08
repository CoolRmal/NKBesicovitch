/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Iteration

/-!
# Strict decrease of the corner update above the critical exponent

The projection exponent lies above `3/2`. Above that root, the defining
cubic is positive, so the corner update strictly decreases the exponent.
The update is continuous throughout the range where input estimates are
used. These facts justify approximation to the critical exponent.
-/

public section

namespace NKBesicovitch.Projection

theorem three_halves_lt_projectionExponent : (3 : ℝ) / 2 < projectionExponent := by
  unfold projectionExponent
  have hd : 0 < criticalExponent - 1 := by linarith [criticalExponent_bounds.1]
  apply (lt_div_iff₀ hd).mpr
  linarith [criticalExponent_bounds.2]

theorem cornerUpdate_lt_self_of_gt {β : ℝ} (hβ : projectionExponent < β) :
    cornerUpdate β < β := by
  apply cornerUpdate_lt_self (projectionExponent_mem.1.trans hβ)
  have hα := three_halves_lt_projectionExponent
  have hq : 0 < β ^ 2 + β * projectionExponent + projectionExponent ^ 2 - 4 := by
    nlinarith [sq_nonneg β, mul_pos (sub_pos.mpr hβ)
      (zero_lt_one.trans projectionExponent_mem.1)]
  nlinarith [projectionExponent_cubic, mul_pos (sub_pos.mpr hβ) hq]

theorem continuousAt_cornerUpdate {β : ℝ} (hβ : 1 < β) : ContinuousAt cornerUpdate β := by
  have hd : β ^ 2 + 3 * β - 2 ≠ 0 := by nlinarith [sq_nonneg β]
  unfold cornerUpdate
  fun_prop

end NKBesicovitch.Projection
