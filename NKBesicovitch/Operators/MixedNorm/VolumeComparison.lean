/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Comparing volume under a linear contraction

A linear homeomorphism between finite-dimensional real inner product
spaces that does not increase norms does not increase the volume of
images. Haar uniqueness reduces the comparison to the unit ball, whose
volume is unchanged by a linear isometry between the two spaces.
-/

public section

open MeasureTheory MeasureTheory.Measure Metric
open scoped ENNReal NNReal

namespace NKBesicovitch

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]

private theorem volume_unitBall_eq (e : E ≃L[ℝ] F) :
    volume (ball (0 : E) 1) = volume (ball (0 : F) 1) := by
  let i : E ≃ₗᵢ[ℝ] F := (stdOrthonormalBasis ℝ E).repr.trans
    (((stdOrthonormalBasis ℝ F).reindex (finCongr e.toLinearEquiv.finrank_eq.symm)).repr.symm)
  simpa only [i.preimage_ball, map_zero] using
    i.measurePreserving.measure_preimage
      (s := ball (0 : F) 1) measurableSet_ball.nullMeasurableSet

theorem volume_le_map_of_norm_le (e : E ≃L[ℝ] F) (h : ∀ x, ‖e x‖ ≤ ‖x‖) :
    (volume : Measure F) ≤ (volume : Measure E).map e := by
  let c := ((volume : Measure E).map e).addHaarScalarFactor (volume : Measure F)
  have hscalar : (volume : Measure E).map e = c • (volume : Measure F) :=
    isAddLeftInvariant_eq_smul _ _
  have hball : volume (ball (0 : F) 1) ≤ ((volume : Measure E).map e) (ball 0 1) := by
    rw [Measure.map_apply e.continuous.measurable measurableSet_ball, ← volume_unitBall_eq e]
    apply measure_mono
    intro x hx
    simp only [Set.mem_preimage, mem_ball, dist_zero_right] at hx ⊢
    exact (h x).trans_lt hx
  have hc : (1 : ℝ≥0∞) ≤ c := by
    rw [hscalar, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hball
    apply (ENNReal.mul_le_mul_iff_right
      (measure_ball_pos volume (0 : F) zero_lt_one).ne' measure_ball_lt_top.ne).mp
    simpa only [mul_one, one_mul, mul_comm] using hball
  rw [hscalar]
  apply Measure.le_iff.mpr
  intro s _
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  simpa only [one_mul] using mul_le_mul_left hc (volume s)

theorem eLpNorm_le_comp_of_norm_le (e : E ≃L[ℝ] F) (h : ∀ x, ‖e x‖ ≤ ‖x‖)
    {f : F → ℝ≥0∞} (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm f p volume ≤ eLpNorm (f ∘ e) p volume :=
  (eLpNorm_mono_measure f (volume_le_map_of_norm_le e h)).trans_eq
    (eLpNorm_map_measure hf.aestronglyMeasurable e.continuous.measurable.aemeasurable)

end NKBesicovitch
