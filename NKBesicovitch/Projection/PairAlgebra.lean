/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Numerical amplification for the basic pair estimate

These inequalities combine the selected-fiber estimate, the upper bound for
code density, and the pair-mass lower bound. All denominators are positive.
-/

public section

namespace NKBesicovitch.Projection

theorem lower_bound_of_density_power {β A T H : ℝ} (hβ : 1 < β) (hA : 0 < A)
    (hT : 0 ≤ T) (hH : 0 ≤ H) (hpower : T ≤ A * H ^ (β - 1)) :
    (T / A) ^ (1 / (β - 1)) ≤ H := by
  rw [one_div]
  apply (Real.rpow_inv_le_iff_of_pos (div_nonneg hT hA.le) hH (sub_pos.mpr hβ)).mpr
  exact (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using hpower)

theorem pair_threshold_bound {β A M H q ℓ : ℝ} (hH : 0 < H) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hseed : H ≤ A * M ^ (2 - β) * (H / (q * ℓ)) ^ β) :
    (q * ℓ) ^ β ≤ A * M ^ (2 - β) * H ^ (β - 1) := by
  rw [Real.div_rpow hH.le (mul_pos hq hℓ).le, ← mul_div_assoc] at hseed
  have h := (le_div_iff₀ (Real.rpow_pos_of_pos (mul_pos hq hℓ) β)).mp hseed
  rw [Real.rpow_sub_one hH.ne', ← mul_div_assoc]
  exact (le_div_iff₀ hH).mpr (by simpa only [mul_comm H] using h)

theorem pair_threshold_bound_of_code_bound {β A D M N H q ℓ : ℝ}
    (hβ : 1 < β) (hA : 0 ≤ A) (hD : 0 ≤ D) (hM : 0 < M) (hN : 0 < N)
    (hH : 0 < H) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hseed : H ≤ A * M ^ (2 - β) * (H / (q * ℓ)) ^ β) (hcode : H ≤ D * M * N) :
    (q * ℓ) ^ β ≤ A * D ^ (β - 1) * M * N ^ (β - 1) := by
  have hpow := Real.rpow_le_rpow hH.le hcode (sub_nonneg.mpr hβ.le)
  have hMpow : M ^ (2 - β) * M ^ (β - 1) = M := by
    rw [← Real.rpow_add hM]
    rw [show (2 - β) + (β - 1) = 1 by ring, Real.rpow_one]
  calc
    _ ≤ A * M ^ (2 - β) * H ^ (β - 1) := pair_threshold_bound hH hq hℓ hseed
    _ ≤ A * M ^ (2 - β) * (D * M * N) ^ (β - 1) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hA (Real.rpow_nonneg hM.le _))
    _ = A * D ^ (β - 1) * (M ^ (2 - β) * M ^ (β - 1)) * N ^ (β - 1) := by
      rw [Real.mul_rpow (mul_nonneg hD hM.le) hN.le, Real.mul_rpow hD hM.le]
      ring
    _ = _ := by rw [hMpow]

theorem pair_mass_power_bound {β K L M N R q ℓ : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hN : 0 < N) (hR : 0 < R) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hmass : L ^ 2 ≤ R * ℓ * N ^ 3)
    (hthreshold : (q * ℓ) ^ β ≤ K * M * N ^ (β - 1)) :
    L ^ (2 * β) ≤ (K * (R / q) ^ β) * M * N ^ (4 * β - 1) := by
  have hℓpow : ℓ ^ β ≤ K * M * N ^ (β - 1) / q ^ β := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hq β)).mpr
    simpa only [Real.mul_rpow hq.le hℓ.le, mul_comm] using hthreshold
  have hNpow : N ^ (β - 1) * N ^ (3 * β) = N ^ (4 * β - 1) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  calc
    L ^ (2 * β) = (L ^ 2) ^ β := by rw [Real.rpow_mul hL, Real.rpow_two]
    _ ≤ (R * ℓ * N ^ 3) ^ β := Real.rpow_le_rpow (sq_nonneg L) hmass hβ
    _ = R ^ β * ℓ ^ β * N ^ (3 * β) := by
      rw [Real.mul_rpow (mul_pos hR hℓ).le (pow_nonneg hN.le 3), Real.mul_rpow hR.le hℓ.le,
        Real.rpow_mul hN.le, Real.rpow_ofNat N 3]
    _ ≤ R ^ β * (K * M * N ^ (β - 1) / q ^ β) * N ^ (3 * β) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓpow
        (Real.rpow_nonneg hR.le _)) (Real.rpow_nonneg hN.le _)
    _ = (K * (R / q) ^ β) * M * (N ^ (β - 1) * N ^ (3 * β)) := by
      rw [Real.div_rpow hR.le hq.le]
      ring
    _ = _ := by rw [hNpow]

theorem pair_take_root {β K L M N : ℝ} (hβ : 0 < β) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hpower : L ^ (2 * β) ≤ K * M * N ^ (4 * β - 1)) :
    L ≤ K ^ (1 / (2 * β)) * M ^ (1 / (2 * β)) * N ^ (2 - 1 / (2 * β)) := by
  have hp : 0 < 2 * β := by positivity
  have h := (Real.le_rpow_inv_iff_of_pos hL
    (mul_nonneg (mul_nonneg hK hM) (Real.rpow_nonneg hN _)) hp).mpr hpower
  have he : (4 * β - 1) * (2 * β)⁻¹ = 2 - 1 / (2 * β) := by
    field_simp
    ring
  simpa only [Real.mul_rpow (mul_nonneg hK hM) (Real.rpow_nonneg hN _),
    Real.mul_rpow hK hM, ← Real.rpow_mul hN, he, one_div] using h

theorem pair_amplification {β A D L M N H R q ℓ : ℝ} (hβ : 1 < β)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hL : 0 ≤ L) (hM : 0 < M) (hN : 0 < N)
    (hH : 0 < H) (hR : 0 < R) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hseed : H ≤ A * M ^ (2 - β) * (H / (q * ℓ)) ^ β)
    (hcode : H ≤ D * M * N) (hmass : L ^ 2 ≤ R * ℓ * N ^ 3) :
    L ≤ ((A * D ^ (β - 1)) * (R / q) ^ β) ^ (1 / (2 * β)) *
      M ^ (1 / (2 * β)) * N ^ (2 - 1 / (2 * β)) := by
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  apply pair_take_root hβ0 (by positivity) hL hM.le hN.le
  exact pair_mass_power_bound hβ0.le hL hN hR hq hℓ hmass
    (pair_threshold_bound_of_code_bound hβ hA hD hM hN hH hq hℓ hseed hcode)

end NKBesicovitch.Projection
