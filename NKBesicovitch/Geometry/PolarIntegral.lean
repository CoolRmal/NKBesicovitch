/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polar integration for nonnegative functions

Mathlib's measure-preserving sphere-radius coordinates give the polar
formula as an iterated nonnegative integral. The positive-radius measure
keeps the origin outside the calculation, including for singular radial weights.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem lintegral_polar (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) = ∫⁻ w : sphere (0 : E) 1,
      ∫⁻ r : Ioi (0 : ℝ), f ((r : ℝ) • (w : E))
        ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) ∂μ.toSphere := by
  let g : sphere (0 : E) 1 × Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun z ↦ f ((z.2 : ℝ) • (z.1 : E))
  have hg : Measurable g := hf.comp (by fun_prop)
  have he := μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp hg
  have hx : (∫⁻ x : ({(0 : E)}ᶜ : Set E), f (x : E) ∂μ.comap Subtype.val) =
      ∫⁻ x, f x ∂μ := by
    rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
  have hc (x : ({(0 : E)}ᶜ : Set E)) : g (homeomorphUnitSphereProd E x) = f x := by
    change f (((homeomorphUnitSphereProd E).symm (homeomorphUnitSphereProd E x) : E)) = f x
    rw [Homeomorph.symm_apply_apply]
  simp only [hc] at he
  rw [hx, lintegral_prod _ hg.aemeasurable] at he
  exact he

/-- Removing one radial power accounts for the dimension drop of a hyperplane. -/
theorem lintegral_volumeIoiPow_inv {m : ℕ} (hm : 0 < m)
    {f : Ioi (0 : ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ r, (ENNReal.ofReal (r : ℝ))⁻¹ * f r ∂Measure.volumeIoiPow m) =
      ∫⁻ r, f r ∂Measure.volumeIoiPow (m - 1) := by
  simp only [Measure.volumeIoiPow]
  rw [lintegral_withDensity_eq_lintegral_mul _
    (measurable_subtype_coe.pow_const m).ennreal_ofReal
    (g := fun r ↦ (ENNReal.ofReal (r : ℝ))⁻¹ * f r) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_subtype_coe.pow_const (m - 1)).ennreal_ofReal hf]
  apply lintegral_congr
  intro r
  simp only [Pi.mul_apply, ENNReal.ofReal_pow r.property.le, ← mul_assoc]
  congr 1
  calc
    _ = (ENNReal.ofReal (r : ℝ) ^ (m - 1) * ENNReal.ofReal (r : ℝ)) *
        (ENNReal.ofReal (r : ℝ))⁻¹ := by rw [← pow_succ, Nat.sub_add_cancel hm]
    _ = _ := by rw [mul_assoc, ENNReal.mul_inv_cancel
      (ENNReal.ofReal_pos.mpr r.property).ne' ENNReal.ofReal_ne_top, mul_one]

end NKBesicovitch
