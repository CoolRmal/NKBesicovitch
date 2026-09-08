/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.MonomialBounds
public import NKBesicovitch.Projection.Iteration

/-!
# Exponent amplification for the finite-depth corner argument

The lower outer-threshold bound and its parent-density upper bound yield
the power `q + 2q² - 2` of line mass. The stopping density exponent contributes
a favorable term. Dropping it and taking a positive real root gives the
finite-depth exponent whose main term is the corner update.
-/

public section

namespace NKBesicovitch.Projection

theorem corner_mass_power_bound {q A D L N τ ρ J : ℝ}
    (hq : 0 ≤ q) (hA : 0 < A) (hL : 0 < L) (hN : 0 < N)
    (hlower : A * L ^ (1 + 2 * q) *
      N ^ (-2 - 3 * q + ρ * q - (200 * q + 2) / J) ≤ τ)
    (hupper : τ ^ q ≤ D * L ^ 2 * N ^ (-2 + ρ)) :
    L ^ (q + 2 * q ^ 2 - 2) ≤ (D / A ^ q) *
      N ^ (2 * q + 3 * q ^ 2 - 2 - ρ * (q ^ 2 - 1) + (200 * q ^ 2 + 2 * q) / J) := by
  have hu : τ ^ q ≤ D * L ^ (2 : ℝ) * N ^ (-2 + ρ) := by
    simpa only [Real.rpow_two] using hupper
  have h := monomial_bound_of_auxiliary_power hq hA hL hN hlower hu
  have hLexp : (1 + 2 * q) * q - 2 = q + 2 * q ^ 2 - 2 := by ring
  have hNexp : (-2 + ρ) - (-2 - 3 * q + ρ * q - (200 * q + 2) / J) * q =
      2 * q + 3 * q ^ 2 - 2 - ρ * (q ^ 2 - 1) + (200 * q ^ 2 + 2 * q) / J := by ring
  rwa [hLexp, hNexp] at h

theorem corner_mass_power_bound_uniform {q A D L N τ ρ J : ℝ}
    (hq : 1 < q) (hA : 0 < A) (hD : 0 ≤ D) (hL : 0 < L) (hN : 1 ≤ N) (hρ : 0 ≤ ρ)
    (hlower : A * L ^ (1 + 2 * q) *
      N ^ (-2 - 3 * q + ρ * q - (200 * q + 2) / J) ≤ τ)
    (hupper : τ ^ q ≤ D * L ^ 2 * N ^ (-2 + ρ)) :
    L ^ (q + 2 * q ^ 2 - 2) ≤ (D / A ^ q) *
      N ^ (2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) := by
  have hq0 : 0 ≤ q := (lt_trans zero_lt_one hq).le
  refine (corner_mass_power_bound hq0 hA hL (lt_of_lt_of_le zero_lt_one hN) hlower hupper).trans ?_
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN ?_)
    (div_nonneg hD (Real.rpow_nonneg hA.le _))
  have hsq : 0 ≤ q ^ 2 - 1 := by nlinarith
  exact add_le_add (sub_le_self _ (mul_nonneg hρ hsq)) le_rfl

theorem corner_power_exponent_pos {q : ℝ} (hq : 1 < q) : 0 < q + 2 * q ^ 2 - 2 := by
  nlinarith [sq_nonneg (q - 1)]

theorem corner_take_root {q K L N J : ℝ} (hq : 1 < q)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (hpower : L ^ (q + 2 * q ^ 2 - 2) ≤
      K * N ^ (2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J)) :
    L ≤ K ^ (1 / (q + 2 * q ^ 2 - 2)) *
      N ^ ((2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) /
        (q + 2 * q ^ 2 - 2)) := by
  have h := (Real.le_rpow_inv_iff_of_pos hL
    (mul_nonneg hK (Real.rpow_nonneg hN _)) (corner_power_exponent_pos hq)).mpr hpower
  rw [Real.mul_rpow hK (Real.rpow_nonneg hN _), ← Real.rpow_mul hN] at h
  simpa only [div_eq_mul_inv, one_mul] using h

theorem corner_amplification {q A D L N τ ρ J : ℝ}
    (hq : 1 < q) (hA : 0 < A) (hD : 0 ≤ D) (hL : 0 < L) (hN : 1 ≤ N) (hρ : 0 ≤ ρ)
    (hlower : A * L ^ (1 + 2 * q) *
      N ^ (-2 - 3 * q + ρ * q - (200 * q + 2) / J) ≤ τ)
    (hupper : τ ^ q ≤ D * L ^ 2 * N ^ (-2 + ρ)) :
    L ≤ (D / A ^ q) ^ (1 / (q + 2 * q ^ 2 - 2)) *
      N ^ ((2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) /
        (q + 2 * q ^ 2 - 2)) :=
  corner_take_root hq (div_nonneg hD (Real.rpow_nonneg hA.le _)) hL.le
    (zero_le_one.trans hN) (corner_mass_power_bound_uniform hq hA hD hL hN hρ hlower hupper)

/-- The main term in the finite-depth exponent is exactly the rational corner update. -/
theorem corner_exponent_main_term {β : ℝ} (hβ : 1 < β) :
    let q := β / (β - 1)
    (2 * q + 3 * q ^ 2 - 2) / (q + 2 * q ^ 2 - 2) = cornerUpdate β := by
  have hb : β - 1 ≠ 0 := (sub_pos.mpr hβ).ne'
  have hd : β ^ 2 + 3 * β - 2 ≠ 0 := by nlinarith [sq_nonneg β]
  dsimp only
  unfold cornerUpdate
  field_simp
  ring

end NKBesicovitch.Projection
