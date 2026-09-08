/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.Seed
public import NKBesicovitch.Induction.Lift

/-!
# Finite iteration of the plate deficit

Starting with zero-dimensional disks in codimension `c > 0`, every lift
divides the deficit by the same fixed `2 < ρ < criticalExponent`. After
`j` lifts the deficit is `c/ρ^j`, and the input exponent remains finite
and at least two. The requested strict dimension range therefore supplies
a lower-dimensional estimate with deficit less than one, ready for the
remaining Fourier terminal step.
-/

public section

open Set

namespace NKBesicovitch.Induction

/-- Iterate the proved lift while keeping the codimension fixed. -/
theorem exists_hasPlateEstimate_codimension (c j : ℕ) (hc : 0 < c)
    {ρ : ℝ} (hρ : ρ ∈ Ioo 2 criticalExponent) :
    ∃ p : ℝ, 2 ≤ p ∧ HasPlateEstimate (show j ≤ c + j by omega) ((c : ℝ) / ρ ^ j) p := by
  induction j with
  | zero =>
    refine ⟨2, le_rfl, ?_⟩
    simpa only [Nat.add_zero, pow_zero, div_one] using
      (hasPlateEstimate_seed (Nat.zero_le c) (by norm_num : (1 : ℝ) ≤ 2))
  | succ j ih =>
    obtain ⟨a, ha, hprev⟩ := ih
    obtain ⟨p, hp, hnext⟩ := HasPlateEstimate.exists_lift (by omega : 0 < c + j)
      (show j ≤ c + j by omega) (by linarith : 0 < a) hρ hprev
    refine ⟨p, hp, ?_⟩
    simpa only [Nat.add_assoc, Nat.succ_eq_add_one, pow_succ, div_div] using hnext

/-- The strict target range produces the subunit deficit needed by the Fourier finish. -/
theorem exists_hasPlateEstimate_deficit_lt_one {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (hdim : (n : ℝ) < criticalExponent ^ (k - 1) + (k : ℝ)) :
    ∃ α p : ℝ, 0 < α ∧ α < 1 ∧ 2 ≤ p ∧
      HasPlateEstimate (show k - 1 ≤ n - 1 by omega) α p := by
  obtain ⟨ρ, hρ, hrange⟩ := exists_ratio_lt_criticalExponent hdim
  have hc : 0 < n - k := by omega
  have hρ0 : 0 < ρ := by linarith [hρ.1]
  obtain ⟨p, hp, hplate⟩ := exists_hasPlateEstimate_codimension (n - k) (k - 1) hc hρ
  have hspace : n - k + (k - 1) = n - 1 := by omega
  refine ⟨(n - k : ℕ) / ρ ^ (k - 1), p,
    div_pos (by exact_mod_cast hc) (pow_pos hρ0 _), ?_, hp, ?_⟩
  · rw [div_lt_one (pow_pos hρ0 _), Nat.cast_sub hkn.le]
    linarith
  · simpa only [hspace] using hplate

end NKBesicovitch.Induction
