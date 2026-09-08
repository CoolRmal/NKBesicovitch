/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Interpolation.TailIntegral

/-!
# From squared-tail bounds to moment bounds

An output distribution bounded by `K t⁻²` times the squared input tail
gives a `p`-moment estimate for every `p > 2`. All constants are explicit;
neither the input nor the output moment is assumed finite.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NKBesicovitch

private theorem inv_sq_mul_rpow (t : ℝ) (ht : 0 < t) (p : ℝ) :
    (ENNReal.ofReal t)⁻¹ ^ 2 * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (t ^ (p - 3)) := by
  simp only [← ENNReal.ofReal_rpow_of_pos ht]
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top]
  congr 1
  ring

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Integrating a squared-tail distribution bound yields the full `p`-moment bound. -/
theorem lintegral_enorm_rpow_le_of_sq_tail (μ : Measure X) (ν : Measure Y)
    {f : X → ℂ} (hf : Measurable f) {g : Y → ℂ} (hg : AEStronglyMeasurable g ν)
    {p c : ℝ} (hp : 2 < p) (hc : 0 < c) (K : ℝ≥0)
    (htail : ∀ t : ℝ, 0 < t → ν {y | c * t < ‖g y‖} ≤
      K * (ENNReal.ofReal t)⁻¹ ^ 2 * ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ 2 ∂μ) :
    (∫⁻ y, ‖g y‖ₑ ^ p ∂ν) ≤
      ENNReal.ofReal c ^ p * ENNReal.ofReal p * K * (ENNReal.ofReal (p - 2))⁻¹ *
        ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  rw [lintegral_enorm_rpow_eq_scaled_tail ν hg (by linarith) hc]
  have hint : (∫⁻ t in Ioi (0 : ℝ), ν {y | c * t < ‖g y‖} *
      ENNReal.ofReal (t ^ (p - 1))) ≤
      ∫⁻ t in Ioi (0 : ℝ), K * ((∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ 2 ∂μ) *
        ENNReal.ofReal (t ^ (p - 3))) := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    calc
      _ ≤ (K * (ENNReal.ofReal t)⁻¹ ^ 2 *
          ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ 2 ∂μ) * ENNReal.ofReal (t ^ (p - 1)) :=
        mul_le_mul' (htail t ht) le_rfl
      _ = K * ((∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ 2 ∂μ) *
          ((ENNReal.ofReal t)⁻¹ ^ 2 * ENNReal.ofReal (t ^ (p - 1)))) := by ac_rfl
      _ = _ := by rw [inv_sq_mul_rpow t ht p]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_sq_tail_mul_rpow μ hf hp] at hint
  simpa only [mul_assoc] using mul_le_mul' (le_refl (ENNReal.ofReal c ^ p * ENNReal.ofReal p)) hint

end NKBesicovitch
