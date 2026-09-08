/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.Estimates
public import NKBesicovitch.Operators.PlateLocalization
public import NKBesicovitch.Operators.PlateTranslation
public import NKBesicovitch.Operators.BallLocalization

/-!
# Extending local plate estimates to arbitrary inputs

Translation invariance applies the centered local estimate to every
moving radius-three ball. Averaging over their centers costs the ratio
of the radius-three and radius-one ball volumes, namely `3^n`, at the
level of the `p`th power. Thus the global bound has the same thickness
deficit and an extra norm factor `3^(n/p)`, uniformly for `0 < δ ≤ 1`.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

variable {n k : ℕ} {δ : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

theorem eLpNorm_plateMaximal_ball_le (hkn : k ≤ n) {p : ℝ≥0∞} (A : ℝ≥0)
    (hbound : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable g →
      Function.support g ⊆ closedBall 0 (3 : ℝ) →
        eLpNorm (plateMaximal δ g) p (Grassmannian.probability hkn) ≤ A * eLpNorm g p volume)
    (hf : Measurable f) (y : EuclideanSpace ℝ (Fin n)) :
    eLpNorm (plateMaximal δ ((ball y 3).indicator f)) p (Grassmannian.probability hkn) ≤
      A * eLpNorm ((ball y 3).indicator f) p volume := by
  let g := (ball y 3).indicator f
  have hg : Measurable g := hf.indicator isOpen_ball.measurableSet
  have hs : Function.support (fun x ↦ g (x + y)) ⊆ closedBall 0 (3 : ℝ) := by
    intro x hx
    have hm : x + y ∈ ball y 3 := by
      by_contra hnot
      exact hx (indicator_of_notMem hnot f)
    have hn : ‖x‖ < 3 := by simpa [mem_ball, dist_eq_norm] using hm
    exact mem_closedBall_zero_iff.mpr hn.le
  have h := hbound (fun x ↦ g (x + y))
    (hg.comp (continuous_id.add_const y).measurable) hs
  have he : eLpNorm (fun x ↦ g (x + y)) p volume = eLpNorm g p volume :=
    eLpNorm_comp_measurePreserving (g := g) (p := p) hg.aestronglyMeasurable
      (measurePreserving_add_right volume y)
  have hm : plateMaximal (k := k) δ (fun x ↦ g (x + y)) = plateMaximal δ g :=
    funext fun V ↦ plateMaximal_add_right y V δ g
  rw [hm, he] at h
  exact h

theorem eLpNorm_plateMaximal_rpow_le_of_local (hkn : k ≤ n) (hδ : δ ≤ 1)
    {p : ℝ≥0} (hp : 0 < p) (A : ℝ≥0)
    (hbound : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable g →
      Function.support g ⊆ closedBall 0 (3 : ℝ) →
        eLpNorm (plateMaximal δ g) p (Grassmannian.probability hkn) ≤ A * eLpNorm g p volume)
    (hf : Measurable f) :
    eLpNorm (plateMaximal δ f) p (Grassmannian.probability hkn) ^ (p : ℝ) ≤
      (3 : ℝ≥0∞) ^ n * (A : ℝ≥0∞) ^ (p : ℝ) * eLpNorm f p volume ^ (p : ℝ) := by
  have h := lintegral_mono (μ := volume) fun y ↦ ENNReal.rpow_le_rpow
    (eLpNorm_plateMaximal_ball_le hkn A hbound hf y) (show 0 ≤ (p : ℝ) from hp.le)
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ (p : ℝ) from hp.le)] at h
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg
    (show 0 ≤ (p : ℝ) from hp.le) ENNReal.coe_ne_top), lintegral_eLpNorm_ball_rpow 3 hf hp] at h
  apply (eLpNorm_plateMaximal_rpow_le_lintegral_ball hkn hδ hp hf).trans
    ((mul_le_mul_right h _).trans_eq ?_)
  have hv : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 3) =
      (3 : ℝ≥0∞) ^ n * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [volume.addHaar_ball_of_pos _ (by norm_num : (0 : ℝ) < 3)]
    norm_num [ENNReal.ofReal_pow]
  rw [hv]
  calc
    _ = ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) *
          ((3 : ℝ≥0∞) ^ n * (A : ℝ≥0∞) ^ (p : ℝ) * eLpNorm f p volume ^ (p : ℝ)) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel (measure_ball_pos volume _ zero_lt_one).ne'
      measure_ball_lt_top.ne, one_mul]

theorem eLpNorm_plateMaximal_le_of_local (hkn : k ≤ n) (hδ : δ ≤ 1)
    {p : ℝ≥0} (hp : 0 < p) (A : ℝ≥0)
    (hbound : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable g →
      Function.support g ⊆ closedBall 0 (3 : ℝ) →
        eLpNorm (plateMaximal δ g) p (Grassmannian.probability hkn) ≤ A * eLpNorm g p volume)
    (hf : Measurable f) :
    eLpNorm (plateMaximal δ f) p (Grassmannian.probability hkn) ≤
      ((3 : ℝ≥0) ^ ((n : ℝ) / (p : ℝ)) * A : ℝ≥0) * eLpNorm f p volume := by
  have hp0 : 0 < (p : ℝ) := hp
  have h := ENNReal.rpow_le_rpow (eLpNorm_plateMaximal_rpow_le_of_local hkn hδ hp A hbound hf)
    (inv_nonneg.mpr hp0.le)
  rw [ENNReal.rpow_rpow_inv hp0.ne'] at h
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp0.le),
    ENNReal.rpow_rpow_inv hp0.ne'] at h
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h
  simpa only [div_eq_mul_inv, ENNReal.coe_mul,
    ENNReal.coe_rpow_of_ne_zero (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using h

/-- A local plate estimate extends to all Borel nonnegative inputs with the same deficit. -/
theorem HasPlateEstimate.global_bound {hkn : k ≤ n} {α p : ℝ} (hp : 0 < p)
    (h : HasPlateEstimate hkn α p) :
    ∃ C : ℝ≥0, ∀ δ : ℝ≥0, 0 < δ → δ ≤ 1 →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable f →
        eLpNorm (plateMaximal δ f) (ENNReal.ofReal p) (Grassmannian.probability hkn) ≤
          (C * δ ^ (-α / p) : ℝ≥0) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := h 3
  refine ⟨(3 : ℝ≥0) ^ ((n : ℝ) / p) * C, ?_⟩
  intro δ hδ hδ1 f hf
  let q : ℝ≥0 := .mk p hp.le
  have hq : 0 < q := hp
  have he : ENNReal.ofReal p = (q : ℝ≥0∞) := ENNReal.ofReal_eq_coe_nnreal hp.le
  rw [he]
  have hb : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable g →
      Function.support g ⊆ closedBall 0 (3 : ℝ) →
        eLpNorm (plateMaximal δ g) q (Grassmannian.probability hkn) ≤
          (C * δ ^ (-α / p) : ℝ≥0) * eLpNorm g q volume := by
    simpa only [he, NNReal.coe_ofNat] using hC δ hδ
  simpa only [q, NNReal.coe_mk, mul_assoc] using
    eLpNorm_plateMaximal_le_of_local hkn (show (δ : ℝ) ≤ 1 from hδ1) hq _ hb hf

end NKBesicovitch.Induction
