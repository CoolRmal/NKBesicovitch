/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CodeCoordinates
public import NKBesicovitch.Projection.TwoSlice
public import Mathlib.Tactic.Positivity

/-!
# Jacobian bounds from separated heights

The code and pair Jacobians are controlled by inverse powers of the
height separation. The inner projection Jacobian has a positive lower
bound when the base gap is at most one and the dual gap is separated.
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch.Projection

theorem codeJacobian_toReal_le_of_separated (m : ℕ) {a b r : ℝ} (hr : 0 < r)
    (hab : r ≤ dist a b) : (codeJacobian m a b).toReal ≤ r⁻¹ ^ m := by
  rw [codeJacobian, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, abs_pow,
    ← Real.dist_eq b a, dist_comm b a, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr dist_nonneg)
    ((inv_le_inv₀ (hr.trans_le hab) hr).mpr hab) m

theorem volume_toReal_le_two_slice_of_separated {m : ℕ} {a b r N : ℝ}
    (hr : 0 < r) (hab : r ≤ dist a b) (hN : 0 ≤ N) (G : Set (Line m))
    (ha : volume (atHeight a '' G) ≤ ENNReal.ofReal N)
    (hb : volume (atHeight b '' G) ≤ ENNReal.ofReal N) :
    (volume G).toReal ≤ r⁻¹ ^ m * N ^ 2 := by
  have hne : a ≠ b := dist_pos.mp (hr.trans_le hab)
  have hmass : volume G ≤ codeJacobian m a b * (ENNReal.ofReal N * ENNReal.ofReal N) :=
    (volume_le_two_slice hne G).trans
      (mul_le_mul le_rfl (mul_le_mul ha hb bot_le bot_le) bot_le bot_le)
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (codeJacobian_ne_top m a b)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) hmass
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hN] at h
  simpa only [pow_two] using h.trans (mul_le_mul_of_nonneg_right
    (codeJacobian_toReal_le_of_separated m hr hab) (mul_self_nonneg N))

theorem pairJacobian_toReal_le_of_separated (m : ℕ) {a b c r : ℝ} (hr : 0 < r)
    (hab : r ≤ dist a b) (hac : r ≤ dist a c) :
    (pairJacobian m a b c).toReal ≤ r⁻¹ ^ (2 * m) := by
  change (codeJacobian m a b * codeJacobian m a c).toReal ≤ _
  rw [ENNReal.toReal_mul]
  calc
    _ ≤ r⁻¹ ^ m * r⁻¹ ^ m := mul_le_mul
      (codeJacobian_toReal_le_of_separated m hr hab)
      (codeJacobian_toReal_le_of_separated m hr hac) ENNReal.toReal_nonneg (by positivity)
    _ = _ := by rw [two_mul, pow_add]

theorem innerJacobian_toReal_ge_of_separated (m : ℕ) {a b d r : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hab : a ≠ b)
    (hr : 0 ≤ r) (hd : r ≤ dist b d) :
    r ^ m ≤ (ENNReal.ofReal |(((a - b) / (d - b)) ^ m)⁻¹|).toReal := by
  rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, abs_pow, abs_div, ← inv_pow, inv_div]
  have hgap : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hgap1 : |a - b| ≤ 1 := Real.dist_le_of_mem_Icc_01 ha hb
  have hdual : r ≤ |d - b| := by simpa only [Real.dist_eq, abs_sub_comm] using hd
  exact pow_le_pow_left₀ hr (hdual.trans (le_div_self (abs_nonneg _) hgap hgap1)) m

end NKBesicovitch.Projection
