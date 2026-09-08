/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.StoppingParameters

/-!
# Numerical bounds from balanced pair and companion masses

The half-mass corner quota gives the cubic line-mass lower bound with the
finite-depth loss. The upper bound on balanced pair mass also gives the
quadratic line-mass upper bound for the selected parent density.
-/

public section

namespace NKBesicovitch.Projection

theorem corner_mass_lower_bound {c d L N V η D : ℝ}
    (hd : 0 ≤ d) (hL : 0 < L) (hN : 1 ≤ N) (hV : 0 ≤ V) (hη : 0 ≤ η)
    {J i : ℕ} (hJ : 0 < J) (hi : i ≤ J)
    (hVlower : c * L ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤ V)
    (hηlower : d * L * N ^ (-1 : ℝ) ≤ η)
    (hD : (V * N ^ (-stoppingAlpha J i)) * η / 2 ≤ D) :
    (c * d / 2) * L ^ (3 : ℝ) * N ^ (-2 - 2 / (J : ℝ)) ≤ D := by
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  have htime : N ^ (-2 / (J : ℝ)) ≤ N ^ (-stoppingAlpha J i) := by
    apply Real.rpow_le_rpow_of_exponent_le hN
    simpa only [neg_div] using neg_le_neg (stoppingAlpha_le_two_div hJ hi)
  have hprod := mul_le_mul hVlower hηlower (by positivity) hV
  have h := mul_le_mul hprod htime (Real.rpow_nonneg hNpos.le _) (mul_nonneg hV hη)
  have hLpow : L ^ (2 : ℝ) * L = L ^ (3 : ℝ) := by
    calc
      _ = L ^ (2 : ℝ) * L ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = L ^ ((2 : ℝ) + 1) := (Real.rpow_add hL _ _).symm
      _ = _ := by norm_num
  have hNpow : N ^ (-1 : ℝ) * N ^ (-1 : ℝ) * N ^ (-2 / (J : ℝ)) =
      N ^ (-2 - 2 / (J : ℝ)) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    ring
  calc
    _ = ((c * L ^ (2 : ℝ) * N ^ (-1 : ℝ)) * (d * L * N ^ (-1 : ℝ)) *
        N ^ (-2 / (J : ℝ))) / 2 := by
      rw [show (c * L ^ (2 : ℝ) * N ^ (-1 : ℝ)) * (d * L * N ^ (-1 : ℝ)) *
          N ^ (-2 / (J : ℝ)) =
        (c * d) * (L ^ (2 : ℝ) * L) *
          (N ^ (-1 : ℝ) * N ^ (-1 : ℝ) * N ^ (-2 / (J : ℝ))) by ring, hLpow, hNpow]
      ring
    _ ≤ (V * η * N ^ (-stoppingAlpha J i)) / 2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = (V * N ^ (-stoppingAlpha J i)) * η / 2 := by ring
    _ ≤ _ := hD

theorem parent_threshold_upper_bound {c L N V ρ : ℝ} (hN : 0 < N)
    (hVupper : V ≤ c * L ^ (2 : ℝ) * N ^ (-1 : ℝ)) :
    N * (V * N ^ (-2 + ρ)) ≤ c * L ^ (2 : ℝ) * N ^ (-2 + ρ) := by
  calc
    _ ≤ N * ((c * L ^ (2 : ℝ) * N ^ (-1 : ℝ)) * N ^ (-2 + ρ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hVupper (Real.rpow_nonneg hN.le _)) hN.le
    _ = _ := by rw [Real.rpow_neg_one]; field_simp

end NKBesicovitch.Projection
