/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerAmplification

/-!
# Choosing the finite corner depth

Every exponent strictly above the ideal corner update admits a positive
finite depth, after which the explicit finite-depth error fits in the
chosen margin. This is a numerical choice; the geometric estimate still
requires the admissible finite height pattern and its analytic inputs.
-/

public section

namespace NKBesicovitch.Projection

theorem exists_corner_depth {q β' : ℝ} (hq : 1 < q)
    (hgap : (2 * q + 3 * q ^ 2 - 2) / (q + 2 * q ^ 2 - 2) < β') :
    ∃ J : ℕ, 0 < J ∧ ∀ j : ℕ, J ≤ j →
      (2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / j) /
        (q + 2 * q ^ 2 - 2) < β' := by
  let A := q + 2 * q ^ 2 - 2
  let B := 2 * q + 3 * q ^ 2 - 2
  let T := 200 * q ^ 2 + 2 * q
  have hA : 0 < A := corner_power_exponent_pos hq
  have hε : 0 < β' - B / A := sub_pos.mpr hgap
  obtain ⟨J, hJ⟩ := exists_nat_gt (max 0 (T / (A * (β' - B / A))))
  have hJpos : (0 : ℝ) < J := (le_max_left _ _).trans_lt hJ
  refine ⟨J, Nat.cast_pos.mp hJpos, fun j hj ↦ ?_⟩
  have hjpos : (0 : ℝ) < j := hJpos.trans_le (Nat.cast_le.mpr hj)
  have ht : T / (A * (β' - B / A)) < j :=
    ((le_max_right _ _).trans_lt hJ).trans_le (Nat.cast_le.mpr hj)
  have hsmall : T / (A * j) < β' - B / A := by
    apply (div_lt_iff₀ (mul_pos hA hjpos)).mpr
    have h := (div_lt_iff₀ (mul_pos hA hε)).mp ht
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  change (B + T / j) / A < β'
  rw [add_div, div_div, mul_comm (j : ℝ) A]
  linarith

theorem exists_depth_for_corner_update {β β' : ℝ} (hβ : 1 < β)
    (hgap : cornerUpdate β < β') :
    let q := β / (β - 1)
    ∃ J : ℕ, 0 < J ∧ ∀ j : ℕ, J ≤ j →
      (2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / j) /
        (q + 2 * q ^ 2 - 2) < β' := by
  have hq : 1 < β / (β - 1) := (one_lt_div (sub_pos.mpr hβ)).mpr (by linarith)
  apply exists_corner_depth hq
  simpa only [corner_exponent_main_term hβ] using hgap

end NKBesicovitch.Projection
