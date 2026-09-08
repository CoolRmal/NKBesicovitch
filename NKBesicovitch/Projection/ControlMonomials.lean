/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring

/-!
# The common monomial in the controlled inner and outer estimates

Both coefficient formulas reduce to the same positive monomial in the
input constant and the inverse separation radius.
-/

@[expose] public section

namespace NKBesicovitch.Projection

/-- The shared coefficient of the controlled inner-code and outer estimates. -/
noncomputable def controlCoefficient (m : ℕ) (β r C : ℝ) : ℝ :=
  (2 * C) ^ (1 / (β - 1)) * (r⁻¹) ^ ((m : ℝ) * ((β + 1) / (β - 1)))

theorem controlCoefficient_pos (m : ℕ) (β : ℝ) {r C : ℝ} (hr : 0 < r) (hC : 0 < C) :
    0 < controlCoefficient m β r C := by
  unfold controlCoefficient
  positivity

theorem inner_controlCoefficient_eq (m : ℕ) (β : ℝ) {r C : ℝ} (hr : 0 < r) (hC : 0 < C) :
    (2 * r⁻¹ ^ m * C) ^ (1 / (β - 1)) / (r ^ m) ^ (β / (β - 1)) =
      controlCoefficient m β r C := by
  unfold controlCoefficient
  rw [show 2 * r⁻¹ ^ m * C = (2 * C) * r⁻¹ ^ m by ring,
    Real.mul_rpow (by positivity) (by positivity)]
  rw [div_eq_mul_inv, ← Real.inv_rpow (pow_nonneg hr.le _) _, ← inv_pow]
  simp_rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hr.le)]
  rw [mul_assoc, ← Real.rpow_add (inv_pos.mpr hr)]
  congr 2
  ring

theorem outer_controlCoefficient_eq (m : ℕ) (β : ℝ) {r C : ℝ} (hr : 0 < r) (hC : 0 < C) :
    ((2 * (r⁻¹ ^ m) ^ 2 * C) * (r⁻¹ ^ m) ^ (β - 1)) ^ (1 / (β - 1)) =
      controlCoefficient m β r C := by
  unfold controlCoefficient
  rw [show (2 * (r⁻¹ ^ m) ^ 2 * C) * (r⁻¹ ^ m) ^ (β - 1) =
      (2 * C) * ((r⁻¹ ^ m) ^ 2 * (r⁻¹ ^ m) ^ (β - 1)) by ring,
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_natCast (r⁻¹ ^ m) 2,
    ← Real.rpow_add (pow_pos (inv_pos.mpr hr) m)]
  simp_rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hr.le)]
  congr 2
  ring

end NKBesicovitch.Projection
