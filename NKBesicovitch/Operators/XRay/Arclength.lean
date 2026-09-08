/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.FunProp

/-!
# Arclength and the vertical line parameter

Normalizing a nonzero direction multiplies the full line integral by
its norm. The identity uses nonnegative extended integrals and remains
valid when either side is infinite.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

theorem lintegral_normalize_direction {f : E → ℝ≥0∞} (hf : Measurable f)
    {w : E} (hw : w ≠ 0) (x : E) :
    (∫⁻ s : ℝ, f (x + s • (‖w‖⁻¹ • w))) =
      ENNReal.ofReal ‖w‖ * ∫⁻ t : ℝ, f (x + t • w) := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hm : Measurable (fun t : ℝ ↦ f (x + t • w)) := hf.comp (by fun_prop)
  have h := lintegral_map (μ := volume) hm (g := fun s : ℝ ↦ ‖w‖⁻¹ * s) (by fun_prop)
  rw [Real.map_volume_mul_left (inv_ne_zero hn), inv_inv, abs_norm,
    lintegral_smul_measure] at h
  simpa only [smul_smul, smul_eq_mul, mul_comm] using h.symm

end NKBesicovitch.XRay
