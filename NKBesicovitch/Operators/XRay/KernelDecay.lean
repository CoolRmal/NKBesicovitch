/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.FrameDilation

/-!
# Uniform decay of projected Schwartz kernels

Schwartz decay and orthogonality give integrable decay in the line parameter
while retaining any prescribed polynomial decay in the transverse displacement.
The constants are uniform over all ambient rotations.
-/

public section

open MeasureTheory Submodule Metric
open scoped SchwartzMap NNReal RealInnerProductSpace

namespace NKBesicovitch.XRay

variable {n m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- A bound with separate transverse decay and an integrable line-parameter factor. -/
theorem exists_norm_frameLineIntegrand_le (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ u : Rotations n, ∀ x : EuclideanSpace ℝ (Fin m), ∀ t : ℝ,
      ‖ψ (Unitary.linearIsometryEquiv u
        (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)))‖ ≤
          (C : ℝ) * ((1 + ‖x‖) ^ N)⁻¹ * (1 + t ^ 2)⁻¹ := by
  let C : ℝ≥0 := .mk (2 ^ (N + 2) * (Finset.Iic (N + 2, 0)).sup
    (fun ij : ℕ × ℕ ↦ SchwartzMap.seminorm ℝ ij.1 ij.2) ψ) (by positivity)
  refine ⟨C, fun u x t ↦ ?_⟩
  let z := Unitary.linearIsometryEquiv u
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t))
  have hn : ‖z‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 := by
    dsimp [z]
    rw [(Unitary.linearIsometryEquiv u).norm_map]
    simpa only [real_inner_self_eq_norm_sq, pow_two] using
      inner_normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b x x t t
  have hx : ‖x‖ ≤ ‖z‖ := by nlinarith [norm_nonneg x, norm_nonneg z, sq_nonneg t]
  have ht : 1 + t ^ 2 ≤ (1 + ‖z‖) ^ 2 := by nlinarith [sq_nonneg ‖x‖, norm_nonneg z]
  have hw : (1 + ‖x‖) ^ N * (1 + t ^ 2) ≤ (1 + ‖z‖) ^ (N + 2) := by
    calc
      _ ≤ (1 + ‖z‖) ^ N * (1 + ‖z‖) ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) N) ht
          (by positivity) (by positivity)
      _ = _ := (pow_add _ _ _).symm
  have hψ : (1 + ‖z‖) ^ (N + 2) * ‖ψ z‖ ≤ C := by
    simpa only [C, NNReal.coe_mk, norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N + 2, 0)) le_rfl le_rfl ψ z
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
    le_div_iff₀ (by positivity)]
  calc
    _ = ((1 + ‖x‖) ^ N * (1 + t ^ 2)) * ‖ψ z‖ := by ring
    _ ≤ (1 + ‖z‖) ^ (N + 2) * ‖ψ z‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ ≤ C := hψ

/-- Absolute projected kernels have arbitrary polynomial decay uniformly over directions. -/
theorem exists_integral_norm_frameLineIntegrand_le
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ u : Rotations n, ∀ x : EuclideanSpace ℝ (Fin m),
      (∫ t : ℝ, ‖ψ (Unitary.linearIsometryEquiv u
        (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)))‖) ≤
          (C : ℝ) * ((1 + ‖x‖) ^ N)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_norm_frameLineIntegrand_le v b ψ N
  refine ⟨C * Real.toNNReal Real.pi, fun u x ↦ ?_⟩
  calc
    _ ≤ ∫ t : ℝ, (C : ℝ) * ((1 + ‖x‖) ^ N)⁻¹ * (1 + t ^ 2)⁻¹ :=
      integral_mono (integrable_frameLineIntegrand v b ψ u x).norm
        (integrable_inv_one_add_sq.const_mul _) (hC u x)
    _ = _ := by
      rw [integral_const_mul, integral_univ_inv_one_add_sq]
      simp only [NNReal.coe_mul, Real.coe_toNNReal Real.pi Real.pi_pos.le]
      ring

variable (w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (c : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (w : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- Dilated absolute projected kernels obey the expected `a^m (1 + a |x|)⁻ᴺ` bound. -/
theorem exists_integral_norm_frameLineIntegrand_dilation_le
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ a : ℝ, ∀ ha : 0 < a, ∀ u : Rotations (m + 1),
      ∀ x : EuclideanSpace ℝ (Fin m),
        (∫ t : ℝ, ‖normalizedDilation a ha ψ (Unitary.linearIsometryEquiv u
          (normalCoordinatesWithBasis (norm_eq_of_mem_sphere w) c (x, t)))‖) ≤
            (C : ℝ) * a ^ m * ((1 + a * ‖x‖) ^ N)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_integral_norm_frameLineIntegrand_le w c ψ N
  refine ⟨C, fun a ha u x ↦ ?_⟩
  have hscale : a ^ (m + 1) * a⁻¹ = a ^ m := by
    rw [pow_succ, mul_assoc, mul_inv_cancel₀ ha.ne', mul_one]
  rw [integral_norm_frameLineIntegrand_normalizedDilation, hscale]
  simpa only [norm_smul, Real.norm_of_nonneg ha.le, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left (hC u (a • x)) (pow_nonneg ha.le m)

/-- Outside the unit transverse ball, kernel tails decay by any prescribed frequency power. -/
theorem exists_integral_norm_frameLineIntegrand_dilation_tail
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) (L N : ℕ) :
    ∃ C : ℝ≥0, ∀ a : ℝ, ∀ ha : 0 < a, 1 ≤ a → ∀ u : Rotations (m + 1),
      ∀ x : EuclideanSpace ℝ (Fin m), 1 ≤ ‖x‖ →
        (∫ t : ℝ, ‖normalizedDilation a ha ψ (Unitary.linearIsometryEquiv u
          (normalCoordinatesWithBasis (norm_eq_of_mem_sphere w) c (x, t)))‖) ≤
            (C : ℝ) * (a ^ L)⁻¹ * ((1 + ‖x‖) ^ N)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_integral_norm_frameLineIntegrand_dilation_le w c ψ (m + L + N)
  refine ⟨C, fun a ha ha₁ u x hx ↦ (hC a ha u x).trans ?_⟩
  have hden : a ^ (m + L) * (1 + ‖x‖) ^ N ≤ (1 + a * ‖x‖) ^ (m + L + N) := by
    rw [pow_add (1 + a * ‖x‖) (m + L) N]
    exact mul_le_mul (pow_le_pow_left₀ ha.le (by nlinarith) (m + L))
      (pow_le_pow_left₀ (by positivity) (by nlinarith) N) (by positivity) (by positivity)
  calc
    _ = ((C : ℝ) * a ^ m) / (1 + a * ‖x‖) ^ (m + L + N) := by rw [div_eq_mul_inv]
    _ ≤ ((C : ℝ) * a ^ m) / (a ^ (m + L) * (1 + ‖x‖) ^ N) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      rw [pow_add]
      field_simp [ha.ne', (by positivity : 1 + ‖x‖ ≠ 0)]

end NKBesicovitch.XRay
