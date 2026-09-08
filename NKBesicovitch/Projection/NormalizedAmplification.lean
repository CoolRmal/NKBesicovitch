/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.BalancedMassBounds
public import NKBesicovitch.Projection.ThresholdBounds
public import NKBesicovitch.Projection.CornerAmplification

/-!
# Assembling the normalized numerical corner argument

The balanced pair and companion masses, retained corner mass, inner-code
image bound, and outer projection inequality imply the finite-depth line
mass estimate. The resulting constant depends only on the displayed fixed
coefficients, never on the line mass or projection size.
-/

public section

namespace NKBesicovitch.Projection

theorem normalized_corner_bound {q c₀ c₁ d K C L N V η D R r : ℝ}
    (hq : 1 < q) (hc₀ : 0 < c₀) (hc₁ : 0 ≤ c₁) (hd : 0 < d)
    (hK : 0 < K) (hC : 0 ≤ C) (hL : 0 < L) (hN : 1 ≤ N)
    (hV : 0 < V) (hη : 0 ≤ η) (hR : 0 < R) (hr : 0 < r)
    {J i : ℕ} (hJ : 0 < J) (hi : i ≤ J)
    (hVlower : c₀ * L ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤ V)
    (hVupper : V ≤ c₁ * L ^ (2 : ℝ) * N ^ (-1 : ℝ))
    (hηlower : d * L * N ^ (-1 : ℝ) ≤ η)
    (hD : (V * N ^ (-stoppingAlpha J i)) * η / 2 ≤ D)
    (himage : R ≤ K * V * (V * N ^ (-2 + stoppingRho J i - 200 / J)) ^ (-q))
    (houter : (D / (2 * r * N * R)) ^ q ≤ C * (N * (V * N ^ (-2 + stoppingRho J i)))) :
    let A := (c₀ * d / 2) / (2 * r * (K * c₀ ^ (1 - q)))
    L ≤ (C * c₁ / A ^ q) ^ (1 / (q + 2 * q ^ 2 - 2)) *
      N ^ ((2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) /
        (q + 2 * q ^ 2 - 2)) := by
  let A := (c₀ * d / 2) / (2 * r * (K * c₀ ^ (1 - q)))
  have hA : 0 < A := by dsimp only [A]; positivity
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  have hmass := corner_mass_lower_bound hd.le hL hN hV.le hη hJ hi hVlower hηlower hD
  have hsize := inner_code_size_bound hq hK.le hc₀ hL hNpos hV hVlower himage
  have hthreshold := outer_threshold_lower_bound (by positivity) (by positivity)
    hL hNpos hR hr hmass hsize
  have hupper : (D / (2 * r * N * R)) ^ q ≤
      (C * c₁) * L ^ 2 * N ^ (-2 + stoppingRho J i) := by
    have h := houter.trans
      (mul_le_mul_of_nonneg_left (parent_threshold_upper_bound hNpos hVupper) hC)
    simpa only [Real.rpow_two, mul_assoc] using h
  exact corner_amplification hq hA (mul_nonneg hC hc₁) hL hN (stoppingRho_nonneg hJ hi)
    hthreshold hupper

end NKBesicovitch.Projection
