/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PairAlgebra

/-!
# Eliminating the selected corner density

Combine the input projection estimate on a corner fiber with the upper
bound from its parent-pair density. The parallel-multiplicity powers combine
to exactly two. All powers and divisions have explicit sign hypotheses.
-/

public section

namespace NKBesicovitch.Projection

theorem corner_threshold_bound_of_code_bound {β A D M N Q H τ : ℝ}
    (hβ : 1 < β) (hA : 0 ≤ A) (hD : 0 ≤ D) (hM : 0 < M) (hN : 0 ≤ N) (hQ : 0 ≤ Q)
    (hH : 0 < H) (hτ : 0 < τ)
    (hseed : H ≤ A * M ^ (3 - β) * (H / τ) ^ β) (hcode : H ≤ D * M * N * Q) :
    τ ^ β ≤ A * D ^ (β - 1) * M ^ 2 * (N * Q) ^ (β - 1) := by
  have ht : τ ^ β ≤ A * M ^ (3 - β) * H ^ (β - 1) := by
    have h := pair_threshold_bound (M := 1) (A := A * M ^ (3 - β))
      hH (show (0 : ℝ) < 1 by norm_num) hτ (by simpa using hseed)
    simpa using h
  have hMpow : M ^ (3 - β) * M ^ (β - 1) = M ^ 2 := by
    rw [← Real.rpow_add hM, show (3 - β) + (β - 1) = 2 by ring, Real.rpow_two]
  have hcode' : H ≤ (D * M) * (N * Q) := by simpa only [mul_assoc] using hcode
  calc
    _ ≤ A * M ^ (3 - β) * H ^ (β - 1) := ht
    _ ≤ A * M ^ (3 - β) * ((D * M) * (N * Q)) ^ (β - 1) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hH.le hcode' (sub_nonneg.mpr hβ.le))
        (mul_nonneg hA (Real.rpow_nonneg hM.le _))
    _ = A * D ^ (β - 1) * (M ^ (3 - β) * M ^ (β - 1)) * (N * Q) ^ (β - 1) := by
      rw [Real.mul_rpow (mul_nonneg hD hM.le) (mul_nonneg hN hQ), Real.mul_rpow hD hM.le]
      ring
    _ = _ := by rw [hMpow]

end NKBesicovitch.Projection
