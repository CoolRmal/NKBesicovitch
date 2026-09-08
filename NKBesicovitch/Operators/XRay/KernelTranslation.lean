/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.KernelDecay

/-!
# Translation of an absolute projected kernel

An ambient translation changes only the transverse displacement of a full
line integral. Its longitudinal component disappears by translation
invariance of one-dimensional Lebesgue measure.
-/

public section

open MeasureTheory Submodule Metric
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch.XRay

variable {n m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- Only the normal projection of an ambient translation affects the integrated kernel. -/
theorem lintegral_sub_frame (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (u : Rotations n)
    (x : EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin n)) :
    (∫⁻ t : ℝ, f (Unitary.linearIsometryEquiv u
      (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)) - z)) =
        ∫⁻ t : ℝ, f (Unitary.linearIsometryEquiv u
          (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b
            (x - ((normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b).symm
              ((Unitary.linearIsometryEquiv u).symm z)).1, t))) := by
  let e := normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b
  let q := e.symm ((Unitary.linearIsometryEquiv u).symm z)
  have hz : Unitary.linearIsometryEquiv u (e q) = z := by
    simp only [q, ContinuousLinearEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have he (t : ℝ) : Unitary.linearIsometryEquiv u (e (x, t)) - z =
      Unitary.linearIsometryEquiv u (e (x - q.1, t - q.2)) := by
    calc
      _ = Unitary.linearIsometryEquiv u (e (x, t)) - Unitary.linearIsometryEquiv u (e q) :=
        by rw [hz]
      _ = Unitary.linearIsometryEquiv u (e ((x, t) - q)) := by rw [map_sub, map_sub]
      _ = _ := rfl
  change (∫⁻ t : ℝ, f (Unitary.linearIsometryEquiv u (e (x, t)) - z)) =
    ∫⁻ t : ℝ, f (Unitary.linearIsometryEquiv u (e (x - q.1, t)))
  simp_rw [he]
  exact lintegral_sub_right_eq_self (fun t : ℝ ↦ f (Unitary.linearIsometryEquiv u
    (e (x - q.1, t)))) q.2

/-- Bounded translations preserve arbitrary spatial decay of absolute projected kernels. -/
theorem exists_lintegral_enorm_sub_frame_le (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (N : ℕ) (R : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ u : Rotations n, ∀ x : EuclideanSpace ℝ (Fin m),
      ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ ≤ R →
        (∫⁻ t : ℝ, ‖ψ (Unitary.linearIsometryEquiv u
          (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)) - z)‖ₑ) ≤
            ENNReal.ofReal ((C : ℝ) * ((1 + ‖x‖) ^ N)⁻¹) := by
  obtain ⟨C, hC⟩ := exists_integral_norm_frameLineIntegrand_le v b ψ N
  refine ⟨C * (1 + R) ^ N, fun u x z hz ↦ ?_⟩
  let q := ((normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b).symm
    ((Unitary.linearIsometryEquiv u).symm z)).1
  have hq : ‖q‖ ≤ R :=
    (norm_normalCoordinatesWithBasis_symm_fst_le (norm_eq_of_mem_sphere v) b _).trans
      (by simpa only [LinearIsometryEquiv.norm_map] using hz)
  have htri : ‖x‖ ≤ ‖x - q‖ + ‖q‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - q) q
  have hw : ((1 + ‖x - q‖) ^ N)⁻¹ ≤ (1 + (R : ℝ)) ^ N * ((1 + ‖x‖) ^ N)⁻¹ := by
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity)
      (by nlinarith [mul_nonneg R.coe_nonneg (norm_nonneg (x - q))] :
        1 + ‖x‖ ≤ (1 + (R : ℝ)) * (1 + ‖x - q‖)) N
  rw [lintegral_sub_frame v b (fun y ↦ ‖ψ y‖ₑ) u x z]
  change (∫⁻ t : ℝ, ‖ψ (Unitary.linearIsometryEquiv u
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x - q, t)))‖ₑ) ≤ _
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_frameLineIntegrand v b ψ u (x - q))]
  apply ENNReal.ofReal_le_ofReal
  apply (hC u (x - q)).trans
  simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one, mul_assoc] using
    mul_le_mul_of_nonneg_left hw C.coe_nonneg

end NKBesicovitch.XRay
