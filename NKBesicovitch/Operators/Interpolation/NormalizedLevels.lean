/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Superlevel measures for inputs with normalized Lp norm

An `L^p` norm at most one bounds the integral of the `p`th power by one.
Markov's inequality then gives the precise superlevel decay used in the
large-input dyadic sum. The threshold is positive and finite.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ≥0∞}

theorem lintegral_rpow_le_one_of_eLpNorm_le_one {p : ℝ} (hp : 0 < p)
    (hnorm : eLpNorm f (ENNReal.ofReal p) μ ≤ 1) : (∫⁻ x, f x ^ p ∂μ) ≤ 1 := by
  have h := ENNReal.rpow_le_rpow hnorm hp.le
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top, enorm_eq_self, ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne', ENNReal.rpow_one, ENNReal.one_rpow] using h

theorem measure_superlevel_le_of_normalized_eLpNorm (hf : Measurable f) {p t : ℝ}
    (hp : 0 < p) (ht : 0 < t) (hnorm : eLpNorm f (ENNReal.ofReal p) μ ≤ 1) :
    μ {x | ENNReal.ofReal t ≤ f x} ≤ ENNReal.ofReal t ^ (-p) := by
  have hpos : 0 < ENNReal.ofReal t ^ p := by positivity
  have hfin := ENNReal.rpow_ne_top_of_nonneg hp.le (x := ENNReal.ofReal t) ENNReal.ofReal_ne_top
  have h := meas_ge_le_lintegral_div (μ := μ) (hf.pow_const p).aemeasurable hpos.ne' hfin
  simp only [ENNReal.rpow_le_rpow_iff hp] at h
  calc
    _ ≤ (∫⁻ x, f x ^ p ∂μ) / ENNReal.ofReal t ^ p := h
    _ ≤ 1 / ENNReal.ofReal t ^ p :=
      ENNReal.div_le_div_right (lintegral_rpow_le_one_of_eLpNorm_le_one hp hnorm) _
    _ = _ := by rw [one_div, ENNReal.rpow_neg]

end NKBesicovitch
