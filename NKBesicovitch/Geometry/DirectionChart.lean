/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.NormalCoordinates
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Tactic.Linarith

/-!
# Slope coordinates for an open hemisphere

A slope in the hyperplane perpendicular to a unit normal `v` determines
the unit direction of `ξ + v`. Its normal component is strictly positive,
and division by that component recovers the slope. The direction map is
continuous and is a measurable embedding in finite dimension.
-/

@[expose] public section

open MeasureTheory Submodule Metric
open scoped InnerProductSpace

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : E}

theorem one_le_norm_add_normal (hv : ‖v‖ = 1) (ξ : (ℝ ∙ v)ᗮ) : 1 ≤ ‖(ξ : E) + v‖ := by
  have h := norm_normalCoordinates_sq hv ξ 1
  rw [normalCoordinates_apply, one_smul, one_pow] at h
  nlinarith [norm_nonneg ((ξ : E) + v), sq_nonneg ‖ξ‖]

/-- The direction with positive normal component and prescribed transverse slope. -/
noncomputable def normalDirection (hv : ‖v‖ = 1) (ξ : (ℝ ∙ v)ᗮ) : sphere (0 : E) 1 :=
  ⟨‖(ξ : E) + v‖⁻¹ • ((ξ : E) + v), by
    have hpos : 0 < ‖(ξ : E) + v‖ := zero_lt_one.trans_le (one_le_norm_add_normal hv ξ)
    simpa only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (norm_nonneg _)] using inv_mul_cancel₀ hpos.ne'⟩

theorem coe_normalDirection (hv : ‖v‖ = 1) (ξ : (ℝ ∙ v)ᗮ) :
    (normalDirection hv ξ : E) = ‖(ξ : E) + v‖⁻¹ • ((ξ : E) + v) := rfl

theorem inner_normalDirection (hv : ‖v‖ = 1) (ξ : (ℝ ∙ v)ᗮ) :
    ⟪v, (normalDirection hv ξ : E)⟫_ℝ = ‖(ξ : E) + v‖⁻¹ := by
  simp only [coe_normalDirection, inner_smul_right, inner_add_right,
    mem_orthogonal_singleton_iff_inner_right.mp ξ.2, real_inner_self_eq_norm_sq, hv]
  simp

theorem inner_normalDirection_pos (hv : ‖v‖ = 1) (ξ : (ℝ ∙ v)ᗮ) :
    0 < ⟪v, (normalDirection hv ξ : E)⟫_ℝ := by
  rw [inner_normalDirection]
  exact inv_pos.mpr (zero_lt_one.trans_le (one_le_norm_add_normal hv ξ))

theorem slope_normalDirection (hv : ‖v‖ = 1) (ξ : (ℝ ∙ v)ᗮ) :
    (⟪v, (normalDirection hv ξ : E)⟫_ℝ)⁻¹ •
      (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (normalDirection hv ξ) = ξ := by
  have hpos : 0 < ‖(ξ : E) + v‖ := zero_lt_one.trans_le (one_le_norm_add_normal hv ξ)
  rw [inner_normalDirection, inv_inv, coe_normalDirection, map_smul, map_add,
    orthogonalProjectionOnto_mem_subspace_eq_self,
    orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, add_zero,
    smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

theorem normalDirection_injective (hv : ‖v‖ = 1) : Function.Injective (normalDirection hv) := by
  intro ξ η h
  have h' := congrArg (fun w : sphere (0 : E) 1 ↦
    (⟪v, (w : E)⟫_ℝ)⁻¹ • (ℝ ∙ v)ᗮ.orthogonalProjectionOnto w) h
  simpa only [slope_normalDirection] using h'

theorem continuous_normalDirection (hv : ‖v‖ = 1) : Continuous (normalDirection hv) := by
  apply Continuous.subtype_mk
  apply Continuous.smul
  · exact (continuous_subtype_val.add continuous_const).norm.inv₀
      (fun ξ ↦ (zero_lt_one.trans_le (one_le_norm_add_normal hv ξ)).ne')
  · exact continuous_subtype_val.add continuous_const

theorem normalDirection_slope (hv : ‖v‖ = 1) (w : sphere (0 : E) 1)
    (hw : 0 < ⟪v, (w : E)⟫_ℝ) :
    normalDirection hv ((⟪v, (w : E)⟫_ℝ)⁻¹ • (ℝ ∙ v)ᗮ.orthogonalProjectionOnto w) = w := by
  have heq : ((⟪v, (w : E)⟫_ℝ)⁻¹ • (ℝ ∙ v)ᗮ.orthogonalProjectionOnto w : E) + v =
      (⟪v, (w : E)⟫_ℝ)⁻¹ • (w : E) := by
    rw [coe_orthogonalProjectionOnto_apply, starProjection_orthogonal_val,
      starProjection_unit_singleton ℝ hv, smul_sub, smul_smul, inv_mul_cancel₀ hw.ne',
      one_smul, sub_add_cancel]
  apply Subtype.ext
  rw [coe_normalDirection, Submodule.coe_smul, heq, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hw,
    norm_eq_of_mem_sphere w, mul_one, inv_inv, smul_smul, mul_inv_cancel₀ hw.ne', one_smul]

theorem range_normalDirection (hv : ‖v‖ = 1) :
    Set.range (normalDirection hv) = {w : sphere (0 : E) 1 | 0 < ⟪v, (w : E)⟫_ℝ} := by
  ext w
  constructor
  · rintro ⟨ξ, rfl⟩
    exact inner_normalDirection_pos hv ξ
  · intro hw
    exact ⟨_, normalDirection_slope hv w hw⟩

theorem norm_add_normal_le_of_inner_lower (hv : ‖v‖ = 1) {c : ℝ} (hc : 0 < c)
    {ξ : (ℝ ∙ v)ᗮ} (hξ : c ≤ ⟪v, (normalDirection hv ξ : E)⟫_ℝ) :
    ‖(ξ : E) + v‖ ≤ 1 / c := by
  have hn : 0 < ‖(ξ : E) + v‖ := zero_lt_one.trans_le (one_le_norm_add_normal hv ξ)
  rw [inner_normalDirection, ← one_div] at hξ
  have hmul := (le_div_iff₀ hn).mp hξ
  exact (le_div_iff₀ hc).mpr (by nlinarith)

theorem norm_slope_le_of_inner_lower (hv : ‖v‖ = 1) {c : ℝ} (hc : 0 < c)
    {ξ : (ℝ ∙ v)ᗮ} (hξ : c ≤ ⟪v, (normalDirection hv ξ : E)⟫_ℝ) : ‖ξ‖ ≤ 1 / c := by
  have hsq := norm_normalCoordinates_sq hv ξ 1
  rw [normalCoordinates_apply, one_smul, one_pow] at hsq
  have hle : ‖ξ‖ ≤ ‖(ξ : E) + v‖ := by nlinarith [norm_nonneg ((ξ : E) + v)]
  exact hle.trans (norm_add_normal_le_of_inner_lower hv hc hξ)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem measurableEmbedding_normalDirection (hv : ‖v‖ = 1) :
    MeasurableEmbedding (normalDirection hv) :=
  (continuous_normalDirection hv).measurableEmbedding (normalDirection_injective hv)

end NKBesicovitch
