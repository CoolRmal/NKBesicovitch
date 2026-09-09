/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.DiskLocalization
public import NKBesicovitch.Operators.BallLocalization
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Schwartz cutoffs and their averaged input norms

Smooth bump localization followed by recentering stays in the positive
Schwartz domain with fixed support. The averaged input norm is bounded
by the corresponding moving-ball norm, using that the bump lies in `[0,1]`.
-/

public section

open MeasureTheory Set Metric
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch

variable {n k : ℕ}

/-- A supported positive Schwartz disk estimate applies to every translated smooth cutoff. -/
theorem eLpNorm_diskMaximal_bump_le (hkn : k ≤ n)
    (θ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (C : ℝ≥0) {p : ℝ≥0∞}
    (hbound : ∀ g : 𝓢(EuclideanSpace ℝ (Fin n), ℝ), (∀ x, 0 ≤ g x) →
      Function.support (g : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ closedBall 0 θ.rOut →
        eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (g x))) p (Grassmannian.probability hkn) ≤
          C * eLpNorm g p volume)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) (hf : ∀ x, 0 ≤ f x)
    (y : EuclideanSpace ℝ (Fin n)) :
    eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (θ (x - y) * f x))) p
      (Grassmannian.probability hkn) ≤ C * eLpNorm (fun x ↦ θ (x - y) * f x) p volume := by
  let g : 𝓢(EuclideanSpace ℝ (Fin n), ℝ) :=
    (θ.hasCompactSupport.mul_right (f' := fun x ↦ f (x + y))).toSchwartzMap
      (θ.contDiff.mul ((f.smooth ⊤).comp (by fun_prop)))
  have hg (x) : g x = θ x * f (x + y) := rfl
  have hs : Function.support (g : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ closedBall 0 θ.rOut := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    by_contra! hn
    exact hx (by rw [hg, θ.zero_of_le_dist (by simpa only [dist_zero_right] using hn.le), zero_mul])
  have h := hbound g (fun x ↦ mul_nonneg θ.nonneg (hf (x + y))) hs
  have hm : diskMaximal (fun x ↦ ENNReal.ofReal (g x)) =
      diskMaximal (fun x ↦ ENNReal.ofReal (θ (x - y) * f x)) (k := k) := by
    funext V
    simpa only [hg, add_sub_cancel_right] using
      diskMaximal_add_right y V (fun x ↦ ENNReal.ofReal (θ (x - y) * f x))
  have hn : eLpNorm g p volume = eLpNorm (fun x ↦ θ (x - y) * f x) p volume := by
    have hc : Continuous (fun x ↦ θ (x - y) * f x) :=
      (θ.continuous.comp (continuous_id.sub continuous_const)).mul f.continuous
    have he : (g : EuclideanSpace ℝ (Fin n) → ℝ) = fun x ↦ θ x * f (x + y) := funext hg
    simpa only [Function.comp_def, he, add_sub_cancel_right] using
      eLpNorm_comp_measurePreserving hc.measurable.aestronglyMeasurable
        (measurePreserving_add_right volume y) (p := p)
  rwa [hm, hn] at h

/-- A bump bounded by one gives at most the norm of restriction to its support ball. -/
theorem eLpNorm_bump_mul_le_ball (θ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ θ (x - y) * f x) p volume ≤
      eLpNorm ((ball y θ.rOut).indicator (fun x ↦ ‖f x‖ₑ)) p volume := by
  apply eLpNorm_mono_enorm
  intro x
  simp only [enorm_eq_self]
  by_cases hx : x ∈ ball y θ.rOut
  · rw [indicator_of_mem hx, ← ofReal_norm, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, Real.norm_of_nonneg θ.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) θ.le_one
  · have hθ : θ (x - y) = 0 := θ.zero_of_le_dist (by
      simpa only [mem_ball, not_lt, dist_eq_norm, sub_zero] using hx)
    rw [hθ, zero_mul, enorm_zero, indicator_of_notMem hx]

/-- Averaging smooth localizations costs at most the volume of the bump's support ball. -/
theorem lintegral_eLpNorm_bump_mul_rpow_le
    (θ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {p : ℝ≥0} (hp : 0 < p) :
    (∫⁻ y, eLpNorm (fun x ↦ θ (x - y) * f x) p volume ^ (p : ℝ)) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) θ.rOut) * eLpNorm f p volume ^ (p : ℝ) := by
  have h := lintegral_mono (μ := volume) fun y ↦ ENNReal.rpow_le_rpow
    (eLpNorm_bump_mul_le_ball θ f y p)
    (show 0 ≤ (p : ℝ) from hp.le)
  rw [lintegral_eLpNorm_ball_rpow θ.rOut hf.enorm hp, eLpNorm_enorm] at h
  exact h

end NKBesicovitch
