/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.TreeControlledBound

/-!
# Polynomial constants for the full tree estimate

The common stopping coefficient and the bounded-size two-slice coefficient
are both bounded by one fixed integer power of the inverse time measure.
The resulting estimate is uniform over all trees satisfying the same
separation, label, input-constant, and total-height-count bounds.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

private theorem exists_tree_coefficient_bound (m n L J : ℕ) (β : ℝ)
    (hL : 0 < L) {A H : ℝ} (hA : 0 < A) (hH : 0 < H) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 0 < B ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      max 1 (max (controlledStoppingConstant m L β (x / 100)
        (A * (100 / x) ^ n) (1 / (4 * H)) (1 / 2) (1 / (2 * H)))
        ((x / 100)⁻¹ ^ m * (controlledStoppingThreshold m L J (x / 100) H) ^ 2)) ≤
      C * x⁻¹ ^ B := by
  obtain ⟨C₁, hC₁, B₁, hB₁, hstop⟩ := exists_polynomial_bound_controlledStoppingConstant
    m n hL β hA (by positivity : 0 < 1 / (4 * H)) (by norm_num : (0 : ℝ) < 1 / 2)
      (by positivity : 0 < 1 / (2 * H))
  obtain ⟨C₂, hC₂, B₂, _, hthreshold⟩ :=
    exists_polynomial_bound_controlledStoppingThreshold m L J hH
  let C := max 1 (max C₁ (100 ^ m * C₂ ^ 2))
  let B := B₁ + (m + 2 * B₂)
  have hC₀ : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  refine ⟨C, zero_lt_one.trans_le (le_max_left _ _), B, by omega, fun x hx hx₁ ↦ ?_⟩
  have hxinv : 1 ≤ x⁻¹ := (one_le_inv₀ hx).mpr hx₁
  have hCpow : C ≤ C * x⁻¹ ^ B := le_mul_of_one_le_right hC₀ (one_le_pow₀ hxinv)
  refine max_le ((le_max_left _ _).trans hCpow) (max_le ?_ ?_)
  · exact (hstop x hx hx₁).trans (mul_le_mul
      ((le_max_left _ _).trans (le_max_right _ _))
      (pow_le_pow_right₀ hxinv (by omega : B₁ ≤ B)) (by positivity) hC₀)
  · have ht₀ : 0 ≤ controlledStoppingThreshold m L J (x / 100) H :=
      zero_le_one.trans (le_max_left _ _)
    calc
      _ ≤ (100 / x) ^ m * (C₂ * x⁻¹ ^ B₂) ^ 2 := by
        rw [inv_div]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ ht₀ (hthreshold x hx hx₁) 2) (by positivity)
      _ = (100 ^ m * C₂ ^ 2) * x⁻¹ ^ (m + 2 * B₂) := by
        rw [div_eq_mul_inv, mul_pow, mul_pow, pow_add, mul_comm 2 B₂, pow_mul]
        ring
      _ ≤ _ := mul_le_mul ((le_max_right _ _).trans (le_max_right _ _))
        (pow_le_pow_right₀ hxinv (by omega : m + 2 * B₂ ≤ B)) (by positivity) hC₀

theorem exists_polynomial_normalized_tree_bound {m L J : ℕ} [Nonempty (Fin m)]
    (n : ℕ) {β A H : ℝ} (hβ : 1 < β) (hβ2 : β ≤ 2) (hL : 0 < L) (hJ : 0 < J)
    (hA : 0 < A) (hH : 0 < H) :
    let q := β / (β - 1)
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 0 < B ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ∀ T : CornerTree m β J, (T.times.card : ℝ) ≤ H →
        (∀ v h, (T.pattern v h).IsControlled (x / 100) (A * (100 / x) ^ n) L) →
        ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
          (parallelMultiplicity G).toReal ≤ 1 → ∀ N : ℝ, 1 ≤ N →
            (∀ t ∈ T.times, volume (atHeight t '' G) ≤ ENNReal.ofReal N) →
            (volume G).toReal ≤ (C * x⁻¹ ^ B) * N ^
              ((2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) / (q + 2 * q ^ 2 - 2)) := by
  obtain ⟨C, hC, B, hB, hbound⟩ := exists_tree_coefficient_bound m n L J β hL hA hH
  refine ⟨C, hC, B, hB, fun x hx hx₁ T hcard hcontrol G hG hGb hM N hN hπ ↦ ?_⟩
  have hstop := fun v h ↦ (hcontrol v h).stoppingNodeBound
    hβ hβ2 (by positivity : 0 < 1 / (4 * H)) (by norm_num : (0 : ℝ) < 1 / 2)
      (by positivity : 0 < 1 / (2 * H))
  exact (T.normalized_bound_of_controlled hJ hβ hcard hcontrol hstop hG hGb hM hN hπ).trans
    (mul_le_mul_of_nonneg_right (hbound x hx hx₁) (Real.rpow_nonneg (by linarith) _))

end NKBesicovitch.Projection
