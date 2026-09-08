/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.Plates
public import NKBesicovitch.Operators.PlateLocalizationMeasurability
public import NKBesicovitch.Grassmannian.Measure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Averaging localized plate maxima over ball centers

For thickness at most one, a unit plate centered at `a` lies in every
radius-three ball centered within distance one of `a`. Integrating over
those centers bounds the global maximal function by its localized versions.
The bound does not depend on the thickness or the direction.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch

variable {n k : ℕ} {δ p : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

theorem plateAverage_le_plateMaximal_ball (hδ : δ ≤ 1) (V : Grassmannian n k)
    (a : EuclideanSpace ℝ (Fin n)) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ ball a 1) :
    (∫⁻ x in plate δ V.val a, f x) / volume (plate δ V.val a) ≤
      plateMaximal δ ((ball y 3).indicator f) V := by
  have hsub : plate δ V.val a ⊆ ball y 3 := by
    intro x hx
    have hxa := plate_subset_ball δ V.val a hx
    have hay : dist a y < 1 := by simpa only [mem_ball, dist_comm] using hy
    have ht := dist_triangle x a y
    change dist x y < 3
    change dist x a < δ + 1 at hxa
    linarith
  have he : (∫⁻ x in plate δ V.val a, f x) =
      ∫⁻ x in plate δ V.val a, (ball y 3).indicator f x :=
    setLIntegral_congr_fun isOpen_thickening.measurableSet
      (fun x hx ↦ (indicator_of_mem (hsub hx) f).symm)
  rw [he]
  exact le_iSup (fun a ↦ (∫⁻ x in plate δ V.val a, (ball y 3).indicator f x) /
    volume (plate δ V.val a)) a

theorem plateMaximal_rpow_le_lintegral_ball (hδ : δ ≤ 1) (hp : 0 < p)
    (V : Grassmannian n k) :
    plateMaximal δ f V ^ p ≤
      (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ∫⁻ y, plateMaximal δ ((ball y 3).indicator f) V ^ p := by
  rw [← ENNReal.le_rpow_inv_iff hp]
  apply iSup_le
  intro a
  rw [ENNReal.le_rpow_inv_iff hp]
  have h := lintegral_mono_ae (μ := volume.restrict (ball a 1))
    ((ae_restrict_mem isOpen_ball.measurableSet).mono fun y hy ↦
      ENNReal.rpow_le_rpow (plateAverage_le_plateMaximal_ball (f := f) hδ V a hy) hp.le)
  rw [setLIntegral_const, volume.addHaar_ball_center a] at h
  have htotal := h.trans (setLIntegral_le_lintegral _ _)
  rw [mul_comm, ← div_eq_mul_inv]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (measure_ball_pos volume _ zero_lt_one).ne')
    (Or.inl measure_ball_lt_top.ne)).2 htotal

theorem eLpNorm_plateMaximal_rpow_le_lintegral_ball (hkn : k ≤ n) (hδ : δ ≤ 1)
    {p : ℝ≥0} (hp : 0 < p) (hf : Measurable f) :
    eLpNorm (plateMaximal δ f) p (Grassmannian.probability hkn) ^ (p : ℝ) ≤
      (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ∫⁻ y, eLpNorm (plateMaximal δ ((ball y 3).indicator f)) p
          (Grassmannian.probability hkn) ^ (p : ℝ) := by
  let V : Grassmannian n k := Classical.choice (Grassmannian.nonempty_iff.mpr hkn)
  have he (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hg : Measurable g) :
      eLpNorm (plateMaximal δ g) p (Grassmannian.probability hkn) ^ (p : ℝ) =
        ∫⁻ u, plateMaximal δ g (Grassmannian.rotate u V) ^ (p : ℝ)
          ∂Rotations.probability n := by
    rw [eLpNorm_nnreal_pow_eq_lintegral hp.ne']
    simp only [enorm_eq_self]
    exact Grassmannian.lintegral_probability hkn V ((measurable_plateMaximal δ hg).pow_const _)
  rw [he f hf]
  simp_rw [he _ (hf.indicator isOpen_ball.measurableSet)]
  apply (lintegral_mono fun u ↦ plateMaximal_rpow_le_lintegral_ball
    (f := f) hδ (show 0 < (p : ℝ) from hp) (Grassmannian.rotate u V)).trans_eq
  rw [lintegral_const_mul' _ _
    (ENNReal.inv_ne_top.mpr (measure_ball_pos volume _ zero_lt_one).ne')]
  congr 1
  exact lintegral_lintegral_swap
    ((measurable_plateMaximal_ball_orbit δ 3 V hf).pow_const (p : ℝ)).aemeasurable

end NKBesicovitch
