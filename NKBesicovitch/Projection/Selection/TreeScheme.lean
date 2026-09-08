/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.FiniteTreeParameters
public import NKBesicovitch.Projection.Selection.TreeEstimate
public import NKBesicovitch.Projection.CornerDepth

/-!
# The selectable corner improvement

A positive finite depth whose exponent fits the target produces another
selectable projection scheme. The new scheme selects all root and tree
parameters jointly, with polynomial volume and coordinate bounds. Thus
every strict exponent above the corner update is attainable by selection
inside each positive-measure Borel subset of the unit interval.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

private theorem polynomial_constant_mono {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {C K : ℝ} {B A : ℕ} (hC : 0 ≤ C) (hCK : C ≤ K) (hBA : B ≤ A) :
    C * (volume I).toReal⁻¹ ^ B ≤ K * (volume I).toReal⁻¹ ^ A := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  have hx₁ : (volume I).toReal ≤ 1 := by
    simpa only [measureReal_def, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one] using measureReal_mono (μ := volume) hIunit (by simp)
  exact mul_le_mul hCK (pow_le_pow_right₀ ((one_le_inv₀ hx).mpr hx₁) hBA)
    (by positivity) (hC.trans hCK)

namespace SelectableProjectionScheme

variable {m D L J : ℕ} [Nonempty (Fin m)] {β γ : ℝ}
  (S : SelectableProjectionScheme m β D L)

include S

theorem exists_scheme_of_depth (hβ : 1 < β) (hβ2 : β ≤ 2) (hJ : 0 < J)
    (hγ : let q := β / (β - 1)
      (2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) / (q + 2 * q ^ 2 - 2) ≤ γ) :
    Nonempty (SelectableProjectionScheme m γ
      (3 + Fintype.card (TreeCoordinate D L J)) (Fintype.card (TreeTimeLabel L J))) := by
  obtain ⟨c, hc, hvolume⟩ := S.exists_root_volume_constant J
  obtain ⟨K, hK, hcoordinates⟩ := S.exists_finiteTree_coordinate_constant
  obtain ⟨C, hC, B, hB, hestimate⟩ := S.exists_tree_projection_constants_of_le hβ hβ2 hJ hγ
  refine ⟨{
    label_pos := Fintype.card_pos
    time := S.finiteTreeTime J
    measurable_time := S.measurable_finiteTreeTime J
    select := fun I ↦ S.finiteTreeParameters I J
    measurable_select := S.measurableSet_finiteTreeParameters_family J
    volumeExponent := 3 + (4 + (8 + 6 * L) * S.volumeExponent) * treeNodeCount L J
    volumeExponent_pos := by omega
    boundExponent := max (8 * S.boundExponent) B
    boundExponent_pos := hB.trans_le (le_max_right _ _)
    lowerConstant := c
    lowerConstant_pos := hc
    upperConstant := max K C
    one_le_upperConstant := hK.trans (le_max_left _ _)
    volume_lower := ?_
    coordinates_bound := ?_
    time_mem := fun I hI hIunit hIpos σ hσ i ↦ S.finiteTreeTime_mem hI hIunit hIpos J hσ i
    estimate := ?_ }⟩
  · intro I hI hIunit hIpos
    rw [S.volume_finiteTreeParameters]
    exact hvolume I hI hIunit hIpos
  · intro I hI hIunit hIpos σ hσ j
    exact (hcoordinates I hI hIunit hIpos J σ hσ j).trans
      (polynomial_constant_mono hIunit hIpos (zero_le_one.trans hK)
        (le_max_left _ _) (le_max_left _ _))
  · intro I hI hIunit hIpos σ hσ G hG hGb
    rw [S.image_finiteTreeTime]
    exact (hestimate I hI hIunit hIpos _ hσ.1 _ hσ.2 G hG hGb).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (polynomial_constant_mono hIunit hIpos hC.le (le_max_right _ _) (le_max_right _ _))
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)) (Real.rpow_nonneg ENNReal.toReal_nonneg _))

theorem corner_improvement (hβ : 1 < β) (hβ2 : β ≤ 2) (hγ : cornerUpdate β < γ) :
    ∃ D' L' : ℕ, Nonempty (SelectableProjectionScheme m γ D' L') := by
  obtain ⟨J, hJ, hdepth⟩ := exists_depth_for_corner_update hβ hγ
  exact ⟨_, _, S.exists_scheme_of_depth hβ hβ2 hJ (hdepth J le_rfl).le⟩

end SelectableProjectionScheme

end NKBesicovitch.Projection.Selection
