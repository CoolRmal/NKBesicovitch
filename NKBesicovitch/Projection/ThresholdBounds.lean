/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.MonomialBounds

/-!
# Bounds entering the outer-threshold calculation

The balanced pair mass controls the inner-code image size. Dividing the
corner-mass lower bound by that image-size upper bound gives the precise
outer-threshold powers used in finite-depth exponent amplification.
-/

public section

namespace NKBesicovitch.Projection

theorem inner_code_size_bound {q K c L N V R ρ J : ℝ}
    (hq : 1 < q) (hK : 0 ≤ K) (hc : 0 < c) (hL : 0 < L) (hN : 0 < N) (hV : 0 < V)
    (hVlower : c * L ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤ V)
    (hR : R ≤ K * V * (V * N ^ (-2 + ρ - 200 / J)) ^ (-q)) :
    R ≤ (K * c ^ (1 - q)) * L ^ (2 - 2 * q) *
      N ^ (3 * q - 1 - ρ * q + 200 * q / J) := by
  have hVpow := Real.rpow_le_rpow_of_nonpos (by positivity) hVlower
    (sub_nonpos.mpr hq.le)
  have hVp : V * V ^ (-q) = V ^ (1 - q) := by
    conv_lhs => lhs; rw [← Real.rpow_one V]
    rw [← Real.rpow_add hV]
    congr 1
  have hNp : N ^ (-1 * (1 - q)) * N ^ ((-2 + ρ - 200 / J) * -q) =
      N ^ (3 * q - 1 - ρ * q + 200 * q / J) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  calc
    _ ≤ K * V * (V * N ^ (-2 + ρ - 200 / J)) ^ (-q) := hR
    _ = K * (V * V ^ (-q)) * N ^ ((-2 + ρ - 200 / J) * -q) := by
      rw [Real.mul_rpow hV.le (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le]
      ring
    _ = K * V ^ (1 - q) * N ^ ((-2 + ρ - 200 / J) * -q) := by rw [hVp]
    _ ≤ K * (c * L ^ (2 : ℝ) * N ^ (-1 : ℝ)) ^ (1 - q) *
        N ^ ((-2 + ρ - 200 / J) * -q) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVpow hK) (Real.rpow_nonneg hN.le _)
    _ = (K * c ^ (1 - q)) * L ^ (2 - 2 * q) *
        (N ^ (-1 * (1 - q)) * N ^ ((-2 + ρ - 200 / J) * -q)) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hN.le _),
        Real.mul_rpow hc.le (Real.rpow_nonneg hL.le _),
        ← Real.rpow_mul hL.le, ← Real.rpow_mul hN.le, show 2 * (1 - q) = 2 - 2 * q by ring]
      ring
    _ = _ := by rw [hNp]

theorem outer_threshold_lower_bound {q A B L N D R r ρ J : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hL : 0 < L) (hN : 0 < N) (hR : 0 < R) (hr : 0 < r)
    (hD : A * L ^ (3 : ℝ) * N ^ (-2 - 2 / J) ≤ D)
    (himage : R ≤ B * L ^ (2 - 2 * q) * N ^ (3 * q - 1 - ρ * q + 200 * q / J)) :
    (A / (2 * r * B)) * L ^ (1 + 2 * q) *
      N ^ (-2 - 3 * q + ρ * q - (200 * q + 2) / J) ≤ D / (2 * r * N * R) := by
  have hNpow : N * N ^ (3 * q - 1 - ρ * q + 200 * q / J) =
      N ^ (3 * q - ρ * q + 200 * q / J) := by
    conv_lhs => lhs; rw [← Real.rpow_one N]
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hden : 2 * r * N * R ≤
      (2 * r * B) * L ^ (2 - 2 * q) * N ^ (3 * q - ρ * q + 200 * q / J) := by
    calc
      _ ≤ 2 * r * N * (B * L ^ (2 - 2 * q) *
          N ^ (3 * q - 1 - ρ * q + 200 * q / J)) :=
        mul_le_mul_of_nonneg_left himage (by positivity)
      _ = (2 * r * B) * L ^ (2 - 2 * q) *
          (N * N ^ (3 * q - 1 - ρ * q + 200 * q / J)) := by ring
      _ = _ := by rw [hNpow]
  have h := monomial_ratio_lower_bound hA (by positivity) hL hN (by positivity) hD hden
  have hLexp : 3 - (2 - 2 * q) = 1 + 2 * q := by ring
  have hNexp : (-2 - 2 / J) - (3 * q - ρ * q + 200 * q / J) =
      -2 - 3 * q + ρ * q - (200 * q + 2) / J := by ring
  rwa [hLexp, hNexp] at h

end NKBesicovitch.Projection
