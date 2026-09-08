/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerAlgebra

/-!
# Eliminating auxiliary variables between monomial bounds

These real-power identities are used to combine the inner and outer corner
estimates. Positive bases and coefficients justify division and subtraction
of exponents, including negative exponents.
-/

public section

namespace NKBesicovitch.Projection

theorem rpow_conjugate_le_of_rpow_le {β C T B : ℝ} (hβ : 1 < β)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hB : 0 ≤ B) (hpower : T ^ β ≤ C * B ^ (β - 1)) :
    T ^ (β / (β - 1)) ≤ C ^ (1 / (β - 1)) * B := by
  have hβpos : 0 < β - 1 := sub_pos.mpr hβ
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hT _) hpower (inv_nonneg.mpr hβpos.le)
  rw [← Real.rpow_mul hT, Real.mul_rpow hC (Real.rpow_nonneg hB _),
    ← Real.rpow_mul hB, mul_inv_cancel₀ hβpos.ne', Real.rpow_one] at h
  simpa only [div_eq_mul_inv, one_mul] using h

theorem monomial_bound_of_auxiliary_power {q A D L N T l n u v : ℝ}
    (hq : 0 ≤ q) (hA : 0 < A) (hL : 0 < L) (hN : 0 < N)
    (hlower : A * L ^ l * N ^ n ≤ T) (hupper : T ^ q ≤ D * L ^ u * N ^ v) :
    L ^ (l * q - u) ≤ (D / A ^ q) * N ^ (v - n * q) := by
  have h := (Real.rpow_le_rpow (by positivity) hlower hq).trans hupper
  rw [Real.mul_rpow (mul_pos hA (Real.rpow_pos_of_pos hL _)).le (Real.rpow_nonneg hN.le _),
    Real.mul_rpow hA.le (Real.rpow_nonneg hL.le _), ← Real.rpow_mul hL.le,
    ← Real.rpow_mul hN.le] at h
  have hAq := Real.rpow_pos_of_pos hA q
  have hNq := Real.rpow_pos_of_pos hN (n * q)
  have hLu := Real.rpow_pos_of_pos hL u
  have hdiv : L ^ (l * q) ≤ (D * L ^ u * N ^ v) / (A ^ q * N ^ (n * q)) := by
    apply (le_div_iff₀ (mul_pos hAq hNq)).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  rw [Real.rpow_sub hL, Real.rpow_sub hN]
  calc
    _ ≤ ((D * L ^ u * N ^ v) / (A ^ q * N ^ (n * q))) / L ^ u :=
      div_le_div_of_nonneg_right hdiv hLu.le
    _ = _ := by field_simp

theorem monomial_ratio_lower_bound {A B L N D R l n u v : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hL : 0 < L) (hN : 0 < N) (hR : 0 < R)
    (hD : A * L ^ l * N ^ n ≤ D) (hupper : R ≤ B * L ^ u * N ^ v) :
    (A / B) * L ^ (l - u) * N ^ (n - v) ≤ D / R := by
  have hLu := Real.rpow_pos_of_pos hL u
  have hNv := Real.rpow_pos_of_pos hN v
  have he : (A / B) * L ^ (l - u) * N ^ (n - v) =
      (A * L ^ l * N ^ n) / (B * L ^ u * N ^ v) := by
    rw [Real.rpow_sub hL, Real.rpow_sub hN]
    field_simp
  rw [he]
  exact (div_le_div_of_nonneg_left (by positivity) hR hupper).trans
    (div_le_div_of_nonneg_right hD hR.le)

theorem inverse_density_threshold {β A a ℓ V : ℝ} (hA : 0 < A) (ha : 0 < a) (hℓ : 0 < ℓ) :
    V / (((a * ℓ) ^ β / A) ^ (1 / (β - 1))) =
      (A ^ (1 / (β - 1)) / a ^ (β / (β - 1))) * V * ℓ ^ (-(β / (β - 1))) := by
  have hAp := Real.rpow_pos_of_pos hA (1 / (β - 1))
  have hap := Real.rpow_pos_of_pos ha (β / (β - 1))
  have hℓp := Real.rpow_pos_of_pos hℓ (β / (β - 1))
  rw [Real.div_rpow (Real.rpow_nonneg (mul_pos ha hℓ).le _) hA.le,
    ← Real.rpow_mul (mul_pos ha hℓ).le,
    show β * (1 / (β - 1)) = β / (β - 1) by ring,
    Real.mul_rpow ha.le hℓ.le, Real.rpow_neg hℓ.le]
  field_simp

end NKBesicovitch.Projection
