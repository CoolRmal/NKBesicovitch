/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.SmoothLocalization

/-!
# Extending supported Schwartz disk estimates

A radius-three smooth cutoff equals one on the radius-two ball. Averaging
its translates extends a supported positive Schwartz estimate to every
positive Schwartz input, at a norm cost of `3^(n/p)`.
-/

public section

open MeasureTheory Set Metric
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch

variable {n k : ℕ}

theorem eLpNorm_diskMaximal_schwartz_rpow_le_of_local (hkn : k ≤ n)
    {p : ℝ≥0} (hp : 0 < p) (C : ℝ≥0)
    (hbound : ∀ g : 𝓢(EuclideanSpace ℝ (Fin n), ℝ), (∀ x, 0 ≤ g x) →
      Function.support (g : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ closedBall 0 (3 : ℝ) →
        eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (g x))) p (Grassmannian.probability hkn) ≤
          C * eLpNorm g p volume)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) (hf : ∀ x, 0 ≤ f x) :
    eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (f x))) p (Grassmannian.probability hkn) ^
      (p : ℝ) ≤ (3 : ℝ≥0∞) ^ n * (C : ℝ≥0∞) ^ (p : ℝ) * eLpNorm f p volume ^ (p : ℝ) := by
  let θ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨2, 3, by norm_num, by norm_num⟩
  have h := lintegral_mono (μ := volume) fun y ↦ ENNReal.rpow_le_rpow
    (eLpNorm_diskMaximal_bump_le hkn θ C hbound f hf y) (show 0 ≤ (p : ℝ) from hp.le)
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ (p : ℝ) from hp.le)] at h
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg
    (show 0 ≤ (p : ℝ) from hp.le) ENNReal.coe_ne_top)] at h
  have hb := h.trans (mul_le_mul_right
    (lintegral_eLpNorm_bump_mul_rpow_le θ f.continuous.measurable hp) _)
  apply (eLpNorm_diskMaximal_ofReal_rpow_le_lintegral_bump hkn θ (by norm_num)
    f.continuous hp).trans ((mul_le_mul_right hb _).trans_eq ?_)
  have hv : volume (ball (0 : EuclideanSpace ℝ (Fin n)) θ.rOut) =
      (3 : ℝ≥0∞) ^ n * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [volume.addHaar_ball_of_pos _ (by norm_num : (0 : ℝ) < θ.rOut)]
    norm_num [θ, ENNReal.ofReal_pow]
  rw [hv]
  calc
    _ = ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) *
          ((3 : ℝ≥0∞) ^ n * (C : ℝ≥0∞) ^ (p : ℝ) * eLpNorm f p volume ^ (p : ℝ)) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel (measure_ball_pos volume _ zero_lt_one).ne'
      measure_ball_lt_top.ne, one_mul]

/-- A positive Schwartz disk bound on the radius-three ball gives a global bound. -/
theorem eLpNorm_diskMaximal_schwartz_le_of_local (hkn : k ≤ n)
    {p : ℝ≥0} (hp : 0 < p) (C : ℝ≥0)
    (hbound : ∀ g : 𝓢(EuclideanSpace ℝ (Fin n), ℝ), (∀ x, 0 ≤ g x) →
      Function.support (g : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ closedBall 0 (3 : ℝ) →
        eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (g x))) p (Grassmannian.probability hkn) ≤
          C * eLpNorm g p volume)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) (hf : ∀ x, 0 ≤ f x) :
    eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (f x))) p (Grassmannian.probability hkn) ≤
      ((3 : ℝ≥0) ^ ((n : ℝ) / (p : ℝ)) * C : ℝ≥0) * eLpNorm f p volume := by
  have hp0 : 0 < (p : ℝ) := hp
  have h := ENNReal.rpow_le_rpow
    (eLpNorm_diskMaximal_schwartz_rpow_le_of_local hkn hp C hbound f hf) (inv_nonneg.mpr hp0.le)
  rw [ENNReal.rpow_rpow_inv hp0.ne'] at h
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp0.le),
    ENNReal.rpow_rpow_inv hp0.ne'] at h
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h
  simpa only [div_eq_mul_inv, ENNReal.coe_mul,
    ENNReal.coe_rpow_of_ne_zero (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using h

end NKBesicovitch
