/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.DiskMeasurability
public import NKBesicovitch.Grassmannian.Measure
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Smooth localization of disk maxima

A cutoff equal to one on the radius-two ball preserves a unit disk whenever
its center lies within distance one of the disk center. Averaging over cutoff
centers gives a global disk bound by the localized maxima. Joint lower
semicontinuity justifies exchanging the direction and center integrals.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch

variable {n k : ℕ}

theorem diskMaximal_add_right (y : EuclideanSpace ℝ (Fin n)) (V : Grassmannian n k)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    diskMaximal (fun x ↦ f (x + y)) V = diskMaximal f V := by
  unfold diskMaximal diskAverage
  have he (a : EuclideanSpace ℝ (Fin n)) (w : V.val) : a + w + y = (a + y) + w := by abel
  simp_rw [he]
  exact (Homeomorph.addRight y).surjective.iSup_comp
    (fun a ↦ (∫⁻ w in closedBall (0 : V.val) 1, f (a + w)) /
      volume (closedBall (0 : V.val) 1))

theorem diskAverage_ofReal_le_diskMaximal_bump (θ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hθ : 2 ≤ θ.rIn) (f : EuclideanSpace ℝ (Fin n) → ℝ) (V : Grassmannian n k)
    (a : EuclideanSpace ℝ (Fin n)) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ ball a 1) :
    diskAverage (fun x ↦ ENNReal.ofReal (f x)) V a ≤
      diskMaximal (fun x ↦ ENNReal.ofReal (θ (x - y) * f x)) V := by
  have he (w : V.val) (hw : w ∈ closedBall (0 : V.val) 1) : θ (a + w - y) = 1 := by
    apply θ.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff]
    have hw' : ‖(w : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
    have hay : ‖a - y‖ < 1 := by simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hy
    have hn := norm_add_le (a - y) (w : EuclideanSpace ℝ (Fin n))
    rw [show a - y + (w : EuclideanSpace ℝ (Fin n)) = a + w - y by abel] at hn
    linarith
  have hd : diskAverage (fun x ↦ ENNReal.ofReal (f x)) V a =
      diskAverage (fun x ↦ ENNReal.ofReal (θ (x - y) * f x)) V a := by
    unfold diskAverage
    congr 1
    apply setLIntegral_congr_fun measurableSet_closedBall
    intro w hw
    dsimp only
    rw [he w hw, one_mul]
  rw [hd]
  exact le_iSup (fun a ↦ diskAverage (fun x ↦ ENNReal.ofReal (θ (x - y) * f x)) V a) a

theorem diskMaximal_ofReal_rpow_le_lintegral_bump
    (θ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (hθ : 2 ≤ θ.rIn)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {p : ℝ} (hp : 0 < p) (V : Grassmannian n k) :
    diskMaximal (fun x ↦ ENNReal.ofReal (f x)) V ^ p ≤
      (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ∫⁻ y, diskMaximal (fun x ↦ ENNReal.ofReal (θ (x - y) * f x)) V ^ p := by
  rw [← ENNReal.le_rpow_inv_iff hp]
  apply iSup_le
  intro a
  rw [ENNReal.le_rpow_inv_iff hp]
  have h := lintegral_mono_ae (μ := volume.restrict (ball a 1))
    ((ae_restrict_mem isOpen_ball.measurableSet).mono fun y hy ↦
      ENNReal.rpow_le_rpow (diskAverage_ofReal_le_diskMaximal_bump θ hθ f V a hy) hp.le)
  rw [setLIntegral_const, volume.addHaar_ball_center a] at h
  rw [mul_comm, ← div_eq_mul_inv]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (measure_ball_pos volume _ zero_lt_one).ne')
    (Or.inl measure_ball_lt_top.ne)).2 (h.trans (setLIntegral_le_lintegral _ _))

/-- Averaging smooth localizations controls the global disk norm. -/
theorem eLpNorm_diskMaximal_ofReal_rpow_le_lintegral_bump (hkn : k ≤ n)
    (θ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (hθ : 2 ≤ θ.rIn)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) {p : ℝ≥0} (hp : 0 < p) :
    eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (f x))) p (Grassmannian.probability hkn) ^
      (p : ℝ) ≤ (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ∫⁻ y, eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (θ (x - y) * f x))) p
          (Grassmannian.probability hkn) ^ (p : ℝ) := by
  simp_rw [eLpNorm_nnreal_pow_eq_lintegral hp.ne', enorm_eq_self]
  apply (lintegral_mono fun V ↦ diskMaximal_ofReal_rpow_le_lintegral_bump
    θ hθ f (show 0 < (p : ℝ) from hp) V).trans_eq
  rw [lintegral_const_mul' _ _
    (ENNReal.inv_ne_top.mpr (measure_ball_pos volume _ zero_lt_one).ne')]
  congr 1
  have hm := (lowerSemicontinuous_diskMaximal_family (f :=
    fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
      ENNReal.ofReal (θ (z.2 - z.1) * f z.2))
    (ENNReal.continuous_ofReal.comp ((θ.continuous.comp (continuous_snd.sub continuous_fst)).mul
      (hf.comp continuous_snd))).lowerSemicontinuous (k := k)).measurable
  exact (lintegral_lintegral_swap (hm.pow_const (p : ℝ)).aemeasurable).symm

end NKBesicovitch
