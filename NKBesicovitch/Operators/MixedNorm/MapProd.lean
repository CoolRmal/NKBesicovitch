/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.MixedNorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Upper norm bounds under maps and product integration

The inequalities for lower Lebesgue integrals suffice for upper norm
estimates without measurability assumptions on the integrand. In the
induction this avoids assuming that an uncountable plate supremum is
measurable before bounding it by the lower-dimensional estimate.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p : ℝ≥0∞}

theorem eLpNorm_map_le (g : X → Y) (f : Y → ℝ≥0∞) (hp : p ≠ 0) (hpfin : p ≠ ∞) :
    eLpNorm f p (μ.map g) ≤ eLpNorm (f ∘ g) p μ := by
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpfin, enorm_eq_self,
    Function.comp_apply]
  exact ENNReal.rpow_le_rpow (lintegral_map_le (fun y ↦ f y ^ p.toReal) g) (by positivity)

theorem eLpNorm_prod_le_iterated (f : X × Y → ℝ≥0∞)
    (hp : p ≠ 0) (hpfin : p ≠ ∞) :
    eLpNorm f p (μ.prod ν) ≤ eLpNorm (fun x ↦ eLpNorm (fun y ↦ f (x, y)) p ν) p μ := by
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp hpfin
  have hpow (x : X) : eLpNorm (fun y ↦ f (x, y)) p ν ^ p.toReal =
      ∫⁻ y, f (x, y) ^ p.toReal ∂ν := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpfin, ← ENNReal.rpow_mul,
      one_div_mul_cancel hpos.ne', ENNReal.rpow_one]
    simp only [enorm_eq_self]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpfin,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpfin]
  simp only [enorm_eq_self, hpow]
  exact ENNReal.rpow_le_rpow (lintegral_prod_le (fun z ↦ f z ^ p.toReal)) (by positivity)

end NKBesicovitch
