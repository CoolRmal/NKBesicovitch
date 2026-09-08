/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Parameters for finite-depth corner stopping

The density exponent decreases from `100` to `0`; the loss exponent
increases by `1 / J²` at each level. This gap lets the total child deletion
fit inside half the mass promised by the selected parent.
-/

@[expose] public section

namespace NKBesicovitch.Projection

/-- Exponent controlling the density threshold at level `i` of a depth-`J` tree. -/
noncomputable def stoppingRho (J i : ℕ) : ℝ := 100 * (1 - (i : ℝ) / J)

/-- Exponent controlling the allowed deletion at level `i` of a depth-`J` tree. -/
noncomputable def stoppingAlpha (J i : ℕ) : ℝ := 1 / J + (i : ℝ) / (J : ℝ) ^ 2

theorem stoppingRho_zero (J : ℕ) : stoppingRho J 0 = 100 := by simp [stoppingRho]

theorem stoppingRho_self {J : ℕ} (hJ : 0 < J) : stoppingRho J J = 0 := by
  simp [stoppingRho, (Nat.cast_pos.mpr hJ : (0 : ℝ) < J).ne']

theorem stoppingRho_succ (J i : ℕ) :
    stoppingRho J (i + 1) = stoppingRho J i - 100 / J := by
  simp only [stoppingRho, Nat.cast_add, Nat.cast_one]
  ring

theorem stoppingRho_nonneg {J i : ℕ} (hJ : 0 < J) (hi : i ≤ J) : 0 ≤ stoppingRho J i := by
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr
    ((div_le_one (Nat.cast_pos.mpr hJ : (0 : ℝ) < J)).mpr (Nat.cast_le.mpr hi)))

theorem stoppingAlpha_succ (J i : ℕ) :
    stoppingAlpha J (i + 1) = stoppingAlpha J i + 1 / (J : ℝ) ^ 2 := by
  simp only [stoppingAlpha, Nat.cast_add, Nat.cast_one]
  ring

theorem stoppingAlpha_pos {J : ℕ} (hJ : 0 < J) (i : ℕ) : 0 < stoppingAlpha J i := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  unfold stoppingAlpha
  positivity

theorem stoppingAlpha_le_two_div {J i : ℕ} (hJ : 0 < J) (hi : i ≤ J) :
    stoppingAlpha J i ≤ 2 / J := by
  have hJ' : (J : ℝ) ≠ 0 := (Nat.cast_pos.mpr hJ : (0 : ℝ) < J).ne'
  calc
    _ ≤ 1 / J + (J : ℝ) / (J : ℝ) ^ 2 :=
      add_le_add le_rfl (div_le_div_of_nonneg_right (Nat.cast_le.mpr hi) (sq_nonneg _))
    _ = _ := by field_simp; ring

theorem stopping_density_mul_image {V N ρ : ℝ} (hN : 0 < N) :
    (V * N ^ (-2 + ρ)) * N ^ (2 - ρ) = V := by
  rw [mul_assoc, ← Real.rpow_add hN, show (-2 + ρ) + (2 - ρ) = 0 by ring,
    Real.rpow_zero, mul_one]

theorem inner_threshold_mul_image {V N : ℝ} (hN : 0 < N) (J i : ℕ) :
    (V * N ^ (-2 + stoppingRho J i - 200 / J)) *
      N ^ (2 - stoppingRho J (i + 1)) = V * N ^ (-100 / (J : ℝ)) := by
  rw [stoppingRho_succ, mul_assoc, ← Real.rpow_add hN]
  congr 2
  ring

theorem stopping_loss_gap {N : ℝ} (hN : 0 < N) (J i : ℕ) :
    N ^ (-stoppingAlpha J (i + 1)) * N ^ (1 / (J : ℝ) ^ 2) =
      N ^ (-stoppingAlpha J i) := by
  rw [← Real.rpow_add hN, stoppingAlpha_succ]
  congr 1
  ring

theorem density_cut_loss_le_child_loss {N : ℝ} (hN : 1 ≤ N)
    {J i : ℕ} (hJ : 0 < J) (hi : i < J) :
    N ^ (-100 / (J : ℝ)) ≤ N ^ (-stoppingAlpha J (i + 1)) := by
  apply Real.rpow_le_rpow_of_exponent_le hN
  have ha := stoppingAlpha_le_two_div hJ (Nat.succ_le_of_lt hi)
  change stoppingAlpha J (i + 1) ≤ 2 / J at ha
  have hd : (2 : ℝ) / J ≤ 100 / J :=
    div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg J)
  simpa only [neg_div] using neg_le_neg (ha.trans hd)

/-- The exact large-projection condition that pays for all three child refinements. -/
theorem child_pruning_budget {N V r k : ℝ} (hN : 1 ≤ N) (hV : 0 ≤ V)
    (hr : 0 ≤ r) (hk : 0 ≤ k) {J i : ℕ} (hJ : 0 < J) (hi : i < J)
    (hlarge : 4 * (1 + 2 * k) * r ≤ N ^ (1 / (J : ℝ) ^ 2)) :
    (1 + 2 * k) * (r * (V * N ^ (-stoppingAlpha J (i + 1))) +
      r * (V * N ^ (-100 / (J : ℝ)))) ≤ V * N ^ (-stoppingAlpha J i) / 2 := by
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  have hcut := density_cut_loss_le_child_loss hN hJ hi
  have hcoeff : 2 * (1 + 2 * k) * r ≤ N ^ (1 / (J : ℝ) ^ 2) / 2 := by linarith
  calc
    _ ≤ (1 + 2 * k) * (r * (V * N ^ (-stoppingAlpha J (i + 1))) +
        r * (V * N ^ (-stoppingAlpha J (i + 1)))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcut hV) hr)) (by positivity)
    _ = (2 * (1 + 2 * k) * r) * (V * N ^ (-stoppingAlpha J (i + 1))) := by ring
    _ ≤ (N ^ (1 / (J : ℝ) ^ 2) / 2) * (V * N ^ (-stoppingAlpha J (i + 1))) :=
      mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hV (Real.rpow_nonneg hNpos.le _))
    _ = V * (N ^ (-stoppingAlpha J (i + 1)) * N ^ (1 / (J : ℝ) ^ 2)) / 2 := by ring
    _ = _ := by rw [stopping_loss_gap hNpos]

theorem child_pruning_threshold {r k N : ℝ} {J : ℕ} (hJ : 0 < J)
    (hN : (max 1 (4 * (1 + 2 * k) * r)) ^ (J : ℝ) ^ 2 ≤ N) :
    4 * (1 + 2 * k) * r ≤ N ^ (1 / (J : ℝ) ^ 2) := by
  let B := max 1 (4 * (1 + 2 * k) * r)
  have hB : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hJpos : (0 : ℝ) < (J : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr hJ)
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hBpos.le _) hN
    (div_nonneg zero_le_one hJpos.le)
  rw [one_div, Real.rpow_rpow_inv hBpos.le hJpos.ne'] at hpow
  have hLB : 4 * (1 + 2 * k) * r ≤ B := le_max_right _ _
  simpa only [one_div] using hLB.trans hpow

theorem exists_child_pruning_threshold (r k : ℝ) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N, N₀ ≤ N →
      4 * (1 + 2 * k) * r ≤ N ^ (1 / (J : ℝ) ^ 2) :=
  ⟨(max 1 (4 * (1 + 2 * k) * r)) ^ (J : ℝ) ^ 2,
    Real.one_le_rpow (le_max_left _ _) (sq_nonneg _), fun _ hN ↦
      child_pruning_threshold hJ hN⟩

end NKBesicovitch.Projection
