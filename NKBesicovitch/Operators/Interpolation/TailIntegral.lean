/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Integrating squared input tails

Layer-cake integration against the measure weighted by `‖f‖²` evaluates
the squared-tail integral for every exponent `p > 2`. A scaled output
version of the same formula matches the threshold in the endpoint estimate.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The weighted squared-tail integral is exactly the `p`-moment divided by `p - 2`. -/
theorem lintegral_sq_tail_mul_rpow {f : X → ℂ} (hf : Measurable f) {p : ℝ} (hp : 2 < p) :
    (∫⁻ t in Ioi (0 : ℝ), (∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ 2 ∂μ) *
      ENNReal.ofReal (t ^ (p - 3))) =
        (ENNReal.ofReal (p - 2))⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have hpower (x : X) : ‖f x‖ₑ ^ 2 * ENNReal.ofReal (‖f x‖ ^ (p - 2)) = ‖f x‖ₑ ^ p := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith), ofReal_norm,
      ← ENNReal.rpow_two, ← ENNReal.rpow_add_of_nonneg 2 (p - 2) (by norm_num) (by linarith)]
    congr 1
    ring
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul (μ.withDensity fun x ↦ ‖f x‖ₑ ^ 2)
    (ae_of_all _ fun x ↦ norm_nonneg (f x)) hf.norm.aemeasurable (by linarith : 0 < p - 2)
  rw [lintegral_withDensity_eq_lintegral_mul μ (hf.enorm.pow_const 2) (by fun_prop)] at h
  simp_rw [Pi.mul_apply, hpower,
    withDensity_apply _ (measurableSet_lt measurable_const hf.norm)] at h
  have hsub : p - 2 - 1 = p - 3 := by ring
  rw [hsub] at h
  rw [h, ← mul_assoc, ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < p - 2)).ne' ENNReal.ofReal_ne_top, one_mul]

/-- Scaling the layer-cake threshold by a positive constant scales the moment by its `p`th power. -/
theorem lintegral_enorm_rpow_eq_scaled_tail {f : X → ℂ} (hf : AEStronglyMeasurable f μ)
    {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) =
      ENNReal.ofReal c ^ p * ENNReal.ofReal p *
        ∫⁻ t in Ioi (0 : ℝ), μ {x | c * t < ‖f x‖} * ENNReal.ofReal (t ^ (p - 1)) := by
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ fun x ↦ div_nonneg (norm_nonneg (f x)) hc.le)
    (hf.norm.aemeasurable.div_const c) hp
  simp_rw [lt_div_iff₀ hc, mul_comm _ c,
    ← ENNReal.ofReal_rpow_of_nonneg (div_nonneg (norm_nonneg _) hc.le) hp.le,
    ENNReal.ofReal_div_of_pos hc, ofReal_norm, div_eq_mul_inv,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.inv_rpow] at h
  rw [lintegral_mul_const'' _ (hf.enorm.pow_const p)] at h
  have hzero : ENNReal.ofReal c ^ p ≠ 0 := by positivity
  have htop : ENNReal.ofReal c ^ p ≠ ∞ := by finiteness
  rw [mul_assoc, ← h, mul_left_comm (ENNReal.ofReal c ^ p),
    ENNReal.mul_inv_cancel hzero htop, mul_one]

end NKBesicovitch
