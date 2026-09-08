/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.MixedNorm.Basic
public import Mathlib.Tactic.Linarith

/-!
# Indicator mixed norms from bounds on fiber measures

A positive lower bound on every nonzero fiber controls the concave
power integral by the total measure. Zero fibers are allowed explicitly.
An upper fiber bound and a finite direction set give the complementary
elementary estimate used for interpolation.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}

theorem lintegral_rpow_le_of_gap {f : Y → ℝ≥0∞} {a s : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hs1 : s ≤ 1) (hfin : ∀ y, f y ≠ ∞)
    (hgap : ∀ y, f y = 0 ∨ ENNReal.ofReal a ≤ f y) :
    (∫⁻ y, f y ^ s ∂ν) ≤ ENNReal.ofReal (a ^ (s - 1)) * ∫⁻ y, f y ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro y
  change f y ^ s ≤ ENNReal.ofReal (a ^ (s - 1)) * f y
  obtain hzero | hlower := hgap y
  · simp [hzero, hs]
  have hlower' : a ≤ (f y).toReal := by
    simpa only [ENNReal.toReal_ofReal ha.le] using ENNReal.toReal_mono (hfin y) hlower
  have hpos := ha.trans_le hlower'
  have hpow : (f y).toReal ^ s ≤ a ^ (s - 1) * (f y).toReal := by
    calc
      _ = (f y).toReal ^ (s - 1) * (f y).toReal := by
        rw [← Real.rpow_add_one hpos.ne']
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos ha hlower' (by linarith)) ENNReal.toReal_nonneg
  conv_lhs => rw [← ENNReal.ofReal_toReal (hfin y)]
  rw [ENNReal.ofReal_rpow_of_pos hpos]
  conv_rhs => arg 2; rw [← ENNReal.ofReal_toReal (hfin y)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hpow

theorem mixedNorm_indicator_rpow_le_of_fiber_gap [SFinite μ] [SFinite ν]
    {F : Set (X × Y)} (hF : MeasurableSet F) {q r a : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hqr : q / r ≤ 1) (ha : 0 < a)
    (hfin : ∀ y, μ ((fun x ↦ (x, y)) ⁻¹' F) ≠ ∞)
    (hgap : ∀ y, μ ((fun x ↦ (x, y)) ⁻¹' F) = 0 ∨
      ENNReal.ofReal a ≤ μ ((fun x ↦ (x, y)) ⁻¹' F)) :
    mixedNorm (F.indicator (fun _ ↦ (1 : ℝ≥0∞))) (ENNReal.ofReal q)
      (ENNReal.ofReal r) μ ν ^ q ≤ ENNReal.ofReal (a ^ (q / r - 1)) * μ.prod ν F := by
  rw [mixedNorm_indicator_rpow hF hq hr, Measure.prod_apply_symm hF]
  exact lintegral_rpow_le_of_gap ha (div_pos hq hr) hqr hfin hgap

theorem mixedNorm_indicator_rpow_le_of_fiber_upper
    {F : Set (X × Y)} (hF : MeasurableSet F) {Ξ : Set Y} (hΞ : MeasurableSet Ξ)
    (hsub : ∀ p ∈ F, p.2 ∈ Ξ) {q r : ℝ} (hq : 0 < q) (hr : 0 < r) {B : ℝ≥0∞}
    (hupper : ∀ y, μ ((fun x ↦ (x, y)) ⁻¹' F) ≤ B) :
    mixedNorm (F.indicator (fun _ ↦ (1 : ℝ≥0∞))) (ENNReal.ofReal q)
      (ENNReal.ofReal r) μ ν ^ q ≤ B ^ (q / r) * ν Ξ := by
  rw [mixedNorm_indicator_rpow hF hq hr, ← lintegral_indicator_const hΞ]
  apply lintegral_mono
  intro y
  by_cases hy : y ∈ Ξ
  · rw [indicator_of_mem hy]
    exact ENNReal.rpow_le_rpow (hupper y) (div_pos hq hr).le
  · have hempty : (fun x ↦ (x, y)) ⁻¹' F = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy (hsub (x, y) hx)
    simp [hempty, hy, div_pos hq hr]

end NKBesicovitch
