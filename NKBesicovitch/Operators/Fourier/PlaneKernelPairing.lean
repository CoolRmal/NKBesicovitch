/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Fourier.PlaneKernel
public import NKBesicovitch.Operators.Fourier.ReproducingKernel
public import NKBesicovitch.Operators.Fourier.PolynomialSupport

/-!
# Reproducing formulas paired with full planes

Tonelli moves a positive convolution through the polynomially weighted plane
integral. Applied to a reproducing formula for the weighted input, this bounds
the full absolute plane integral by a pairing with the positive plane kernel.
-/

public section

open MeasureTheory SchwartzMap Set Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lintegral_mul_weightedPlaneKernel (V : Submodule ℝ E) (a : ℝ) (A N : ℕ)
    (x : E) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z * weightedPlaneKernel V a A N x z) =
      ENNReal.ofReal (a ^ Module.finrank ℝ E) * ∫⁻ w : V,
        ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹) *
          ∫⁻ z, f z * ENNReal.ofReal (((1 + ‖a • (x + w - z)‖ ^ 2) ^ N)⁻¹) := by
  simp only [weightedPlaneKernel]
  have he (z : E) : f z * (∫⁻ w : V,
      ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹) *
        ENNReal.ofReal (((1 + ‖a • (x + w - z)‖ ^ 2) ^ N)⁻¹)) =
      ∫⁻ w : V, f z * (ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹) *
        ENNReal.ofReal (((1 + ‖a • (x + w - z)‖ ^ 2) ^ N)⁻¹)) :=
    (lintegral_const_mul (f z) (by fun_prop)).symm
  simp_rw [mul_left_comm (f _) (ENNReal.ofReal (a ^ Module.finrank ℝ E)), he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap (by fun_prop)]
  congr 1
  apply lintegral_congr
  intro w
  simp_rw [mul_left_comm (f _) (ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹))]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma enorm_inv_weight_smulLeftCLM_aux (f : 𝓢(E, ℂ)) (A : ℕ) (z : E) :
    ‖f z‖ₑ = ENNReal.ofReal (((1 + ‖z‖ ^ 2) ^ A)⁻¹) *
      ‖smulLeftCLM ℂ (fun y : E ↦ (1 + ‖y‖ ^ 2) ^ A) f z‖ₑ := by
  rw [smulLeftCLM_apply_apply (by fun_prop :
    (fun y : E ↦ (1 + ‖y‖ ^ 2) ^ A).HasTemperateGrowth), enorm_smul,
    Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

/-- A reproducing formula bounds a full plane integral by the associated positive kernel pairing. -/
theorem lintegral_plane_le_weightedPlaneKernel (φ f : 𝓢(E, ℂ)) {R a : ℝ} (ha : 0 < a)
    (hφ : ∀ ξ : E, ‖ξ‖ ≤ R → 𝓕 φ ξ = 1)
    (hf : tsupport (𝓕 f : 𝓢(E, ℂ)) ⊆ closedBall 0 (a * R)) {N : ℕ} {C : ℝ≥0}
    (hC : ∀ z, ‖normalizedDilation a ha φ z‖ ≤
      C * a ^ Module.finrank ℝ E * ((1 + ‖a • z‖ ^ 2) ^ N)⁻¹)
    (V : Submodule ℝ E) (A : ℕ) (x : E) :
    (∫⁻ w : V, ‖f (x + w)‖ₑ) ≤ C * ∫⁻ z,
      ‖smulLeftCLM ℂ (fun y : E ↦ (1 + ‖y‖ ^ 2) ^ A) f z‖ₑ *
        weightedPlaneKernel V a A N x z := by
  let g := smulLeftCLM ℂ (fun y : E ↦ (1 + ‖y‖ ^ 2) ^ A) f
  have hg := (tsupport_fourier_smulLeftCLM_one_add_norm_sq_pow_subset f A).trans hf
  simp_rw [enorm_inv_weight_smulLeftCLM_aux f A]
  change (∫⁻ w : V, ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹) * ‖g (x + w)‖ₑ) ≤ _
  calc
    _ ≤ ∫⁻ w : V, ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹) *
        (C * ENNReal.ofReal (a ^ Module.finrank ℝ E) *
          ∫⁻ z, ‖g z‖ₑ * ENNReal.ofReal (((1 + ‖a • (x + w - z)‖ ^ 2) ^ N)⁻¹)) :=
      lintegral_mono fun w ↦ mul_le_mul_right
        (enorm_le_polynomial_convolution φ g ha hφ hg hC (x + w)) _
    _ = C * ENNReal.ofReal (a ^ Module.finrank ℝ E) * ∫⁻ w : V,
        ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹) *
          ∫⁻ z, ‖g z‖ₑ * ENNReal.ofReal (((1 + ‖a • (x + w - z)‖ ^ 2) ^ N)⁻¹) := by
      rw [← lintegral_const_mul' _ _ (by finiteness)]
      apply lintegral_congr
      intro w
      ac_rfl
    _ = _ := by
      rw [lintegral_mul_weightedPlaneKernel V a A N x g.continuous.measurable.enorm]
      exact mul_assoc _ _ _

end NKBesicovitch
