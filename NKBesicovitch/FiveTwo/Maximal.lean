/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.FiveTwo.RestrictedWeak
public import NKBesicovitch.Induction.RestrictedWeak

/-!
# The four-dimensional maximal input

The restricted weak estimate at exponent `121/40` supplies a strong estimate
at exponent four with deficit `79/80`. This assembly still depends on the
unproved geometric estimate in `FiveTwo/RestrictedWeak`.
-/

public section

namespace NKBesicovitch.FiveTwo

/-- The geometric restricted weak estimate supplies the subunit deficit for the terminal step. -/
theorem hasPlateEstimate_four_one :
    Induction.HasPlateEstimate (show 1 ≤ 4 by decide) (79 / 80) 4 := by
  exact Induction.hasPlateEstimate_of_restricted_weak (show 1 ≤ 4 by decide)
    (by norm_num) (by norm_num : (0 : ℝ) < 121 / 40) (by norm_num) (by norm_num)
    restricted_weak_plateMaximal

end NKBesicovitch.FiveTwo
