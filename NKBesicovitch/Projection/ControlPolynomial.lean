/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.ControlledStopping
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Integer-power bounds for the controlled stopping constant

Substituting a polynomial input constant and radius `x/100` reduces the
stopping coefficient to one real monomial in `100/x`. Increasing its
exponent to a positive integer gives the polynomial bound required by
the selectable-scheme interface.
-/

@[expose] public section

namespace NKBesicovitch.Projection

theorem controlCoefficient_scaled (m n : ℕ) (β : ℝ) {x A : ℝ}
    (hx : 0 < x) (hA : 0 < A) :
    controlCoefficient m β (x / 100) (A * (100 / x) ^ n) =
      (2 * A) ^ (1 / (β - 1)) * (100 / x) ^
        ((n : ℝ) * (1 / (β - 1)) + (m : ℝ) * ((β + 1) / (β - 1))) := by
  unfold controlCoefficient
  rw [inv_div, show 2 * (A * (100 / x) ^ n) = (2 * A) * (100 / x) ^ n by ring,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (100 / x) n,
    ← Real.rpow_mul (by positivity), mul_assoc, ← Real.rpow_add (by positivity)]

private theorem stopping_monomial_aux (q e : ℝ) {B l c₀ c₁ d : ℝ} (hB : 0 < B) (hl : 0 < l)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hd : 0 < d) :
    (B * c₁ / ((c₀ * d / 2) / (2 * l * (B * c₀ ^ (1 - q)))) ^ q) ^ e =
      (c₁ * (4 * l * c₀ ^ (1 - q) / (c₀ * d)) ^ q) ^ e * B ^ ((q + 1) * e) := by
  rw [div_eq_mul_inv, ← Real.inv_rpow (by positivity) q, inv_div]
  have hratio : 2 * l * (B * c₀ ^ (1 - q)) / (c₀ * d / 2) =
      (4 * l * c₀ ^ (1 - q) / (c₀ * d)) * B := by ring
  rw [hratio, Real.mul_rpow (by positivity) hB.le]
  rw [show B * c₁ * ((4 * l * c₀ ^ (1 - q) / (c₀ * d)) ^ q * B ^ q) =
      (c₁ * (4 * l * c₀ ^ (1 - q) / (c₀ * d)) ^ q) * (B ^ q * B) by ring]
  rw [← Real.rpow_add_one hB.ne', Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hB.le]

theorem exists_integer_power_bound_monomial {K : ℝ} (hK : 0 < K) (e : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n : ℕ, 0 < n ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      K * (100 / x) ^ e ≤ C * x⁻¹ ^ n := by
  obtain ⟨n, hn⟩ := exists_nat_gt e
  refine ⟨K * 100 ^ (n + 1), by positivity, n + 1, Nat.succ_pos n, fun x hx hx1 ↦ ?_⟩
  have hy : 1 ≤ 100 / x := (le_div_iff₀ hx).mpr (by linarith)
  have he : e ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hpow : (100 / x) ^ e ≤ (100 / x) ^ (n + 1) := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hy he
  simpa only [div_eq_mul_inv, mul_pow, mul_assoc] using mul_le_mul_of_nonneg_left hpow hK.le

/-- A uniform integer-power bound for the stopping coefficient after the scheme substitution. -/
theorem exists_polynomial_bound_controlledStoppingConstant (m n : ℕ) {L : ℕ} (hL : 0 < L)
    (β : ℝ) {A c₀ c₁ d : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      controlledStoppingConstant m L β (x / 100) (A * (100 / x) ^ n) c₀ c₁ d ≤
        C * x⁻¹ ^ N := by
  let q := β / (β - 1)
  let p := (q + 1) * (1 / (q + 2 * q ^ 2 - 2))
  let E := (n : ℝ) * (1 / (β - 1)) + (m : ℝ) * ((β + 1) / (β - 1))
  let K := (c₁ * (4 * L * c₀ ^ (1 - q) / (c₀ * d)) ^ q) ^
    (1 / (q + 2 * q ^ 2 - 2)) * ((2 * A) ^ (1 / (β - 1))) ^ p
  have hl : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨C, hC, N, hN, hbound⟩ := exists_integer_power_bound_monomial hK (E * p)
  refine ⟨C, hC, N, hN, fun x hx hx1 ↦ ?_⟩
  have hB := controlCoefficient_pos m β (by positivity : 0 < x / 100)
    (by positivity : 0 < A * (100 / x) ^ n)
  have heq : controlledStoppingConstant m L β (x / 100) (A * (100 / x) ^ n) c₀ c₁ d =
      K * (100 / x) ^ (E * p) := by
    unfold controlledStoppingConstant
    rw [stopping_monomial_aux _ _ hB hl hc₀ hc₁ hd, controlCoefficient_scaled m n β hx hA]
    conv_lhs =>
      arg 2
      rw [Real.mul_rpow (by positivity) (by positivity)]
      arg 2
      rw [← Real.rpow_mul (by positivity)]
    dsimp only [K, E, p, q]
    simp only [mul_assoc]
  exact heq.le.trans (hbound x hx hx1)

end NKBesicovitch.Projection
