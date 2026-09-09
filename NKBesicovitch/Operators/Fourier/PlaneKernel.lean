/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.PolynomialWeight
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Weighted positive kernels on affine planes

Integrating a normalized polynomial kernel against a decaying plane weight
gives a positive kernel for the bandlimited comparison. Its value changes by
a bounded factor when the center moves by a unit tangential displacement and
a displacement at most the reciprocal dilation scale in the ambient space.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A polynomially weighted plane integral of a normalized positive smoothing kernel. -/
noncomputable def weightedPlaneKernel (V : Submodule ℝ E) (a : ℝ) (A N : ℕ) (x z : E) : ℝ≥0∞ :=
  ENNReal.ofReal (a ^ Module.finrank ℝ E) * ∫⁻ w : V,
    ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹) *
      ENNReal.ofReal (((1 + ‖a • (x + w - z)‖ ^ 2) ^ N)⁻¹)

theorem measurable_weightedPlaneKernel (V : Submodule ℝ E) (a : ℝ) (A N : ℕ) (x : E) :
    Measurable (weightedPlaneKernel V a A N x) := by
  apply Measurable.const_mul
  exact (by fun_prop : Measurable (fun p : E × V ↦
    ENNReal.ofReal (((1 + ‖x + p.2‖ ^ 2) ^ A)⁻¹) *
      ENNReal.ofReal (((1 + ‖a • (x + p.2 - p.1)‖ ^ 2) ^ N)⁻¹))).lintegral_prod_right

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma inv_weight_le_aux (x y : E) (A : ℕ) (h : ‖x - y‖ ≤ 1) :
    ((1 + ‖x‖ ^ 2) ^ A)⁻¹ ≤ 4 ^ A * ((1 + ‖y‖ ^ 2) ^ A)⁻¹ := by
  have hw := inv_one_add_norm_sq_pow_add_le (x - y) y A
  rw [sub_add_cancel] at hw
  apply hw.trans
  calc
    _ ≤ (2 ^ A * 2 ^ A) * ((1 + ‖y‖ ^ 2) ^ A)⁻¹ := by gcongr; nlinarith [norm_nonneg (x - y)]
    _ = _ := by rw [← mul_pow]; norm_num

private lemma weightedPlaneKernel_sub_eq_aux (V : Submodule ℝ E) (a : ℝ) (A N : ℕ)
    (x z : E) (w₀ : V) (e : E) :
    weightedPlaneKernel V a A N x (z - (w₀ + e)) =
      ENNReal.ofReal (a ^ Module.finrank ℝ E) * ∫⁻ w : V,
        ENNReal.ofReal (((1 + ‖x + w - w₀‖ ^ 2) ^ A)⁻¹) *
          ENNReal.ofReal (((1 + ‖a • (x + w - z + e)‖ ^ 2) ^ N)⁻¹) := by
  unfold weightedPlaneKernel
  congr 1
  rw [← lintegral_sub_right_eq_self (fun w : V ↦
    ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹) *
      ENNReal.ofReal (((1 + ‖a • (x + w - (z - (w₀ + e)))‖ ^ 2) ^ N)⁻¹)) w₀]
  apply lintegral_congr
  intro w
  have h₁ : x + (w - w₀ : V) = x + w - w₀ := by simp only [Submodule.coe_sub]; abel
  have h₂ : x + (w - w₀ : V) - (z - (w₀ + e)) = x + w - z + e := by
    simp only [Submodule.coe_sub]
    abel
  rw [h₂, h₁]

/-- The positive plane kernel is comparable under tangential and smoothing-scale shifts. -/
theorem weightedPlaneKernel_sub_le (V : Submodule ℝ E) (a : ℝ) (A N : ℕ)
    (x z : E) (w₀ : V) (hw₀ : ‖w₀‖ ≤ 1) (e : E) (he : ‖a • e‖ ≤ 1) :
    weightedPlaneKernel V a A N x z ≤
      (4 : ℝ≥0∞) ^ (A + N) * weightedPlaneKernel V a A N x (z - (w₀ + e)) := by
  rw [weightedPlaneKernel_sub_eq_aux, weightedPlaneKernel, mul_left_comm]
  apply mul_le_mul_right
  rw [← lintegral_const_mul' _ _ (by finiteness)]
  apply lintegral_mono
  intro w
  have h₁ := inv_weight_le_aux (x + w) (x + w - w₀) A (by simpa using hw₀)
  have h₂ := inv_weight_le_aux (a • (x + w - z)) (a • (x + w - z + e)) N (by
    simpa only [smul_add, sub_add_cancel_left, norm_neg] using he)
  have h := mul_le_mul' (ENNReal.ofReal_le_ofReal h₁) (ENNReal.ofReal_le_ofReal h₂)
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ (4 : ℝ) ^ A),
    ENNReal.ofReal_mul (by positivity : 0 ≤ (4 : ℝ) ^ N),
    ENNReal.ofReal_pow (by norm_num : 0 ≤ (4 : ℝ)),
    ENNReal.ofReal_ofNat, pow_add, mul_mul_mul_comm] using h

end NKBesicovitch
