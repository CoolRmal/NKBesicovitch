/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.UniformFibers
public import NKBesicovitch.Operators.Interpolation.BlockBounds

/-!
# Interpolated estimates for comparable-fiber pieces

Combining the geometric bound with the elementary direction-measure bound
introduces decay in the transform threshold and in the parallel-fiber scale.
The input-volume exponent loses only the freely chosen factor `θ`.
-/

public section

open MeasureTheory Set NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

theorem interpolate_mixedNorm_fiberBlock {m K : ℕ} {β C V a r θ : ℝ}
    (hK : 0 < K) (hβ : 1 < β) (hC : 0 ≤ C) (hV : 0 ≤ V)
    {F : Set (Line m)} (hF : MeasurableSet F)
    {Ξ : Set (EuclideanSpace ℝ (Fin m))} (hΞ : MeasurableSet Ξ)
    (hsub : ∀ g ∈ F, g.2 ∈ Ξ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hgeometry : ENNReal.ofReal (r ^ K) *
      mixedNorm ((fiberBlock F a).indicator (fun _ ↦ (1 : ℝ≥0∞)))
        (ENNReal.ofReal K) (ENNReal.ofReal ((K : ℝ) / (β - 1))) volume volume ^ (K : ℝ) ≤
          ENNReal.ofReal (C * V ^ β)) :
    ENNReal.ofReal r * mixedNorm ((fiberBlock F a).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      (ENNReal.ofReal K) (ENNReal.ofReal ((K : ℝ) / (β - 1))) volume volume ≤
        ENNReal.ofReal C ^ (θ / K) * ENNReal.ofReal V ^ (β * θ / K) *
          ENNReal.ofReal r ^ (1 - θ) * ENNReal.ofReal a ^ ((β - 1) * (1 - θ) / K) *
            volume Ξ ^ ((1 - θ) / K) := by
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hden : 0 < β - 1 := by linarith
  have hquot : (K : ℝ) / ((K : ℝ) / (β - 1)) = β - 1 := by field_simp
  have helementary := mixedNorm_indicator_rpow_le_of_fiber_upper (ν := volume)
    (measurableSet_fiberBlock hF a) hΞ (fun g hg ↦ hsub g hg.1) hKr (div_pos hKr hden)
    (volume_fiberBlock_fiber_le F a)
  rw [hquot] at helementary
  have hgeometry' : (ENNReal.ofReal r *
      mixedNorm ((fiberBlock F a).indicator (fun _ ↦ (1 : ℝ≥0∞)))
        (ENNReal.ofReal K) (ENNReal.ofReal ((K : ℝ) / (β - 1))) volume volume) ^ (K : ℝ) ≤
          ENNReal.ofReal C * ENNReal.ofReal V ^ β := by
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ hKr.le, ENNReal.rpow_natCast,
      ← ENNReal.ofReal_pow hr, ENNReal.ofReal_mul hC,
      ENNReal.ofReal_rpow_of_nonneg hV (zero_lt_one.trans hβ).le] using hgeometry
  apply interpolate_block_bounds hKr hθ hθ1 hgeometry'
  rw [ENNReal.mul_rpow_of_nonneg _ _ hKr.le]
  exact (mul_le_mul_right helementary (ENNReal.ofReal r ^ (K : ℝ))).trans_eq (mul_assoc _ _ _).symm

end NKBesicovitch.XRay
