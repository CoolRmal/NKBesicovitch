/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Moments of scaled input superlevels

The layer-cake formula evaluates the input levels in restricted-weak to
strong interpolation. Scaling the threshold by `c > 0` contributes `c^(-p)`.
The extended-real version explicitly excludes infinite point values before
using `toReal`; bounded truncations satisfy this condition.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {X : Type*} [MeasurableSpace X]

/-- Layer-cake for finite-valued extended nonnegative inputs. -/
theorem lintegral_ennreal_rpow_eq_lintegral_meas_lt_mul (μ : Measure X) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hfin : ∀ x, f x ≠ ∞) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, f x ^ p ∂μ) = ENNReal.ofReal p *
      ∫⁻ t in Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} * ENNReal.ofReal (t ^ (p - 1)) := by
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg (a := f x)) hf.ennreal_toReal.aemeasurable hp
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
    ENNReal.ofReal_toReal (hfin _)] at h
  rw [h]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (hfin _)]

theorem lintegral_scaled_superlevels_mul_rpow (μ : Measure X) {f : X → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    ENNReal.ofReal p * (∫⁻ t in Ioi (0 : ℝ),
      μ {x | c * t ≤ f x} * ENNReal.ofReal (t ^ (p - 1))) =
        ENNReal.ofReal c ^ (-p) * ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  have h := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (ae_of_all _ fun x ↦ div_nonneg (hf0 x) hc.le) (hf.div_const c).aemeasurable hp
  simp only [le_div_iff₀ hc, mul_comm _ c] at h
  rw [← h]
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hf0 _) hc.le) hp.le,
    ENNReal.ofReal_div_of_pos hc, div_eq_mul_inv,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.inv_rpow]
  rw [lintegral_mul_const _ (hf.ennreal_ofReal.pow_const p), ENNReal.rpow_neg, mul_comm]

/-- Scaled layer-cake for finite-valued nonnegative inputs, with no integrability requirement. -/
theorem lintegral_scaled_ennreal_superlevels_mul_rpow (μ : Measure X) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hfin : ∀ x, f x ≠ ∞) {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    ENNReal.ofReal p * (∫⁻ t in Ioi (0 : ℝ),
      μ {x | ENNReal.ofReal (c * t) ≤ f x} * ENNReal.ofReal (t ^ (p - 1))) =
        ENNReal.ofReal c ^ (-p) * ∫⁻ x, f x ^ p ∂μ := by
  simpa only [ENNReal.ofReal_toReal (hfin _), ENNReal.ofReal_le_iff_le_toReal (hfin _)] using
    lintegral_scaled_superlevels_mul_rpow μ hf.ennreal_toReal
      (fun x ↦ ENNReal.toReal_nonneg) hp hc

end NKBesicovitch
