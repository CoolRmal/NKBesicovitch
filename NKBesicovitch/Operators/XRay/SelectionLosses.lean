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
# Collecting the finite powers lost in simultaneous selection

For `β ≤ 2` and `0 < t ≤ 1`, replacing the factor `t⁻ᵝ` by `t⁻²`
gives one integer loss exponent. This harmless weakening is useful when
the restricted estimate is converted into a mixed-norm bound.
-/

public section

namespace NKBesicovitch.XRay

theorem collect_selection_losses {A B : ℕ} {c C t F Y V β : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t) (ht₁ : t ≤ 1)
    (hY : 0 ≤ Y) (hV : 0 ≤ V) (hβ : β ≤ 2)
    (h : c * t ^ A * F ≤ (C * t⁻¹ ^ B) * Y * (V / t) ^ β) :
    t ^ (A + B + 2) * F ≤ (C / c) * Y * V ^ β := by
  have hpower : (V / t) ^ β ≤ V ^ β * t⁻¹ ^ 2 := by
    rw [div_eq_mul_inv, Real.mul_rpow hV (inv_nonneg.mpr ht.le)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hV _)
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le ((one_le_inv₀ ht).mpr ht₁) hβ
  have hu := h.trans (mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ C * t⁻¹ ^ B * Y))
  have hmul := mul_le_mul_of_nonneg_left hu (pow_nonneg ht.le (B + 2))
  have hleft : t ^ (B + 2) * (c * t ^ A * F) = c * (t ^ (A + B + 2) * F) := by
    rw [show A + B + 2 = A + (B + 2) by omega, pow_add]
    ring
  have hright : t ^ (B + 2) * ((C * t⁻¹ ^ B) * Y * (V ^ β * t⁻¹ ^ 2)) =
      C * Y * V ^ β := by
    rw [pow_add, inv_pow, inv_pow]
    field_simp
  rw [hleft, hright] at hmul
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm c] using hmul

end NKBesicovitch.XRay
