/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.Estimates
public import NKBesicovitch.Operators.PlatePower
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The ambient-dimension seed for the plate induction

Every thickened disk contains a ball of the same positive radius. Hölder
and the volume scaling of balls give deficit `n` at every exponent `p ≥ 1`.
In particular this starts the induction with zero-dimensional disks in
ambient dimension equal to the final codimension.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

variable {n k : ℕ} {δ p : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

theorem plateMaximal_rpow_le_ball_volume (hδ : 0 < δ) (hp : 1 ≤ p)
    (hf : Measurable f) (V : Grassmannian n k) :
    plateMaximal δ f V ^ p ≤
      (volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ * ∫⁻ x, f x ^ p := by
  rw [← ENNReal.le_rpow_inv_iff (zero_lt_one.trans_le hp)]
  apply iSup_le
  intro a
  rw [ENNReal.le_rpow_inv_iff (zero_lt_one.trans_le hp)]
  apply (plateAverage_rpow_le hδ hp V.val a hf).trans
  have hvol : volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) ≤ volume (plate δ V.val a) := by
    rw [← volume.addHaar_ball_center a]
    exact measure_mono (ball_subset_thickening (by simp [unitDisk] : a ∈ unitDisk V.val a) δ)
  rw [div_eq_mul_inv, mul_comm]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr hvol) (setLIntegral_le_lintegral _ _)

theorem plateMaximal_le_ball_volume (hδ : 0 < δ) (hp : 1 ≤ p)
    (hf : Measurable f) (V : Grassmannian n k) :
    plateMaximal δ f V ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) ^ (-p⁻¹) *
        eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 := zero_lt_one.trans_le hp
  have h := ENNReal.rpow_le_rpow (plateMaximal_rpow_le_ball_volume hδ hp hf V)
    (inv_nonneg.mpr hp0.le)
  rw [ENNReal.rpow_rpow_inv hp0.ne', ENNReal.mul_rpow_of_nonneg _ _
    (inv_nonneg.mpr hp0.le), ← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul, neg_one_mul] at h
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, enorm_eq_self, one_div] using h

/-- The trivial estimate supplies the seed deficit in every ambient dimension. -/
theorem hasPlateEstimate_seed (hkn : k ≤ n) (hp : 1 ≤ p) : HasPlateEstimate hkn n p := by
  let D := volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (-p⁻¹)
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero
    (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  intro R
  refine ⟨D.toNNReal, fun δ hδ f hf _ ↦ ?_⟩
  have hδr : 0 < (δ : ℝ) := hδ
  have hpoint (V : Grassmannian n k) : plateMaximal δ f V ≤
      (D.toNNReal * δ ^ (-(n : ℝ) / p) : ℝ≥0) * eLpNorm f (ENNReal.ofReal p) volume := by
    apply (plateMaximal_le_ball_volume hδr hp hf V).trans_eq
    rw [volume.addHaar_ball_of_pos _ hδr, ENNReal.ofReal_pow hδr.le]
    simp only [finrank_euclideanSpace_fin, ENNReal.ofReal_coe_nnreal]
    rw [ENNReal.mul_rpow_of_ne_top (by finiteness) measure_ball_lt_top.ne,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ENNReal.coe_mul,
      ENNReal.coe_toNNReal hD, ENNReal.coe_rpow_of_ne_zero hδ.ne']
    simp only [D, div_eq_mul_inv, mul_neg, mul_comm]
  have h := eLpNorm_le_of_ae_enorm_bound (p := ENNReal.ofReal p)
    (f := plateMaximal δ f) (μ := Grassmannian.probability hkn) (ae_of_all _ fun V ↦ by
      simpa only [enorm_eq_self] using hpoint V)
  simpa only [measure_univ, ENNReal.one_rpow, smul_eq_mul, mul_one] using h

end NKBesicovitch.Induction
