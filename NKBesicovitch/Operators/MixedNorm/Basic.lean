/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Mixed norms of nonnegative functions

The inner norm integrates the first coordinate. The outer norm integrates
the second coordinate, which is the direction variable for line families.
Both norms use Mathlib's extended-valued `eLpNorm`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NKBesicovitch

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {q r : ℝ≥0∞} {f g : X × Y → ℝ≥0∞}

/-- The `L^q` norm in the second variable of the `L^r` norm in the first variable. -/
noncomputable def mixedNorm (f : X × Y → ℝ≥0∞) (q r : ℝ≥0∞)
    (μ : Measure X) (ν : Measure Y) : ℝ≥0∞ :=
  eLpNorm (fun y ↦ eLpNorm (fun x ↦ f (x, y)) r μ) q ν

theorem mixedNorm_indicator_snd {A : Set Y} (hA : MeasurableSet A) :
    mixedNorm ((Prod.snd ⁻¹' A).indicator f) q r μ ν =
      mixedNorm f q r μ (ν.restrict A) := by
  unfold mixedNorm
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hA]
  congr 1
  funext y
  by_cases hy : y ∈ A
  · simp only [indicator_of_mem hy, mem_preimage, hy, indicator_of_mem]
  · have hx (x : X) : (x, y) ∉ Prod.snd ⁻¹' A := hy
    simp only [indicator_of_notMem hy, indicator_of_notMem (hx _)]
    exact eLpNorm_zero

theorem mixedNorm_mono (h : f ≤ g) : mixedNorm f q r μ ν ≤ mixedNorm g q r μ ν := by
  apply eLpNorm_mono_enorm
  intro y
  simp only [enorm_eq_self]
  exact eLpNorm_mono_enorm (fun x ↦ by simpa only [enorm_eq_self] using h (x, y))

theorem mixedNorm_mono_fiber_ae (h : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, f (x, y) ≤ g (x, y)) :
    mixedNorm f q r μ ν ≤ mixedNorm g q r μ ν := by
  apply eLpNorm_mono_enorm_ae
  filter_upwards [h] with y hy
  simp only [enorm_eq_self]
  exact eLpNorm_mono_enorm_ae (by simpa only [enorm_eq_self] using hy)

theorem mixedNorm_le_const_mul_of_fiber_ae {c : ℝ≥0}
    (h : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, f (x, y) ≤ c * g (x, y)) :
    mixedNorm f q r μ ν ≤ c * mixedNorm g q r μ ν := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
  filter_upwards [h] with y hy
  simp only [enorm_eq_self]
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
    (by simpa only [enorm_eq_self] using hy) r

theorem mixedNorm_const_mul_le (c : ℝ≥0) (f : X × Y → ℝ≥0∞) :
    mixedNorm (fun p ↦ c * f p) q r μ ν ≤ c * mixedNorm f q r μ ν :=
  mixedNorm_le_const_mul_of_fiber_ae (ae_of_all _ fun _ ↦ ae_of_all _ fun _ ↦ le_rfl)

theorem measurable_eLpNorm_fiber [SFinite μ] (hf : Measurable f) (hr : r ≠ 0)
    (hrfin : r ≠ ∞) : Measurable (fun y ↦ eLpNorm (fun x ↦ f (x, y)) r μ) := by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr hrfin, enorm_eq_self]
  exact (hf.pow_const r.toReal).lintegral_prod_left'.pow_const _

theorem mixedNorm_add_le [SFinite μ] (hf : Measurable f) (hg : Measurable g)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hrfin : r ≠ ∞) :
    mixedNorm (f + g) q r μ ν ≤ mixedNorm f q r μ ν + mixedNorm g q r μ ν := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  calc
    _ ≤ eLpNorm (fun y ↦ eLpNorm (fun x ↦ f (x, y)) r μ +
        eLpNorm (fun x ↦ g (x, y)) r μ) q ν := by
      apply eLpNorm_mono_enorm
      intro y
      simp only [enorm_eq_self]
      exact eLpNorm_add_le (hf.comp measurable_prodMk_right).aestronglyMeasurable
        (hg.comp measurable_prodMk_right).aestronglyMeasurable hr
    _ ≤ _ := eLpNorm_add_le (measurable_eLpNorm_fiber hf hr0 hrfin).aestronglyMeasurable
      (measurable_eLpNorm_fiber hg hr0 hrfin).aestronglyMeasurable hq

/-- The outer power of an indicator mixed norm is an integral of fiber measures. -/
theorem mixedNorm_indicator_rpow {F : Set (X × Y)} (hF : MeasurableSet F)
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    mixedNorm (F.indicator (fun _ ↦ (1 : ℝ≥0∞))) (ENNReal.ofReal q)
      (ENNReal.ofReal r) μ ν ^ q =
        ∫⁻ y, μ ((fun x ↦ (x, y)) ⁻¹' F) ^ (q / r) ∂ν := by
  have hinner (y : Y) :
      eLpNorm (fun x ↦ F.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x, y)) (ENNReal.ofReal r) μ =
        μ ((fun x ↦ (x, y)) ⁻¹' F) ^ (1 / r) := by
    simp_rw [← indicator_comp_right (fun x ↦ (x, y))]
    change eLpNorm (((fun x ↦ (x, y)) ⁻¹' F).indicator (fun _ ↦ (1 : ℝ≥0∞))) _ _ = _
    simp only [eLpNorm_indicator_const (hF.preimage measurable_prodMk_right)
      (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top,
      enorm_eq_self, ENNReal.toReal_ofReal hr.le, one_mul]
  simp only [mixedNorm, hinner,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hq).ne'
      ENNReal.ofReal_ne_top, enorm_eq_self, ENNReal.toReal_ofReal hq.le,
    ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
  congr 1
  funext y
  congr 1
  ring

end NKBesicovitch
