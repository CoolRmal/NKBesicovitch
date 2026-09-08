/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.NormalLift
public import NKBesicovitch.Operators.Defs
public import Mathlib.Tactic.Linarith

/-!
# Plates in normal coordinates

Projection to the transverse coordinates takes a disk in the lifted
plane into its lower-dimensional disk and is a contraction. Therefore
the lifted plate lies inside the cylinder over the lower-dimensional
plate. Conversely, contracting the lower plate by one half permits a
unit-length interval in the normal direction inside the lifted plate.
-/

public section

open MeasureTheory Submodule Set Metric NKBesicovitch.Grassmannian
open scoped InnerProductSpace Pointwise

namespace NKBesicovitch.Induction

variable {n m k : ℕ} {v : EuclideanSpace ℝ (Fin n)}

theorem fst_mem_unitDisk_of_normalCoordinates_mem (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    {a z : EuclideanSpace ℝ (Fin m) × ℝ}
    (hz : normalCoordinatesWithBasis hv b z ∈
      unitDisk (normalLift hv b V).val (normalCoordinatesWithBasis hv b a)) :
    z.1 ∈ unitDisk V.val a.1 := by
  have hmem := hz.1
  rw [← map_sub] at hmem
  have hV : z.1 - a.1 ∈ V.val :=
    (normalCoordinates_mem_normalLift_iff hv b V _ _).mp hmem
  refine ⟨hV, ?_⟩
  have hnorm := norm_normalCoordinatesWithBasis_symm_fst_le hv b
    (normalCoordinatesWithBasis hv b (z - a))
  rw [ContinuousLinearEquiv.symm_apply_apply, map_sub] at hnorm
  exact hnorm.trans hz.2

theorem preimage_plate_normalCoordinates_subset (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    (a : EuclideanSpace ℝ (Fin m) × ℝ) (δ : ℝ) :
    normalCoordinatesWithBasis hv b ⁻¹'
        plate δ (normalLift hv b V).val (normalCoordinatesWithBasis hv b a) ⊆
      plate δ V.val a.1 ×ˢ univ := by
  intro z hz
  obtain ⟨y, hy, hdist⟩ := mem_thickening_iff.mp hz
  obtain ⟨w, rfl⟩ := (normalCoordinatesWithBasis hv b).surjective y
  refine ⟨mem_thickening_iff.mpr ⟨w.1,
    fst_mem_unitDisk_of_normalCoordinates_mem hv b V hy, ?_⟩, mem_univ _⟩
  have h := (lipschitz_normalCoordinatesWithBasis_symm_fst hv b).dist_le_mul
    (normalCoordinatesWithBasis hv b z) (normalCoordinatesWithBasis hv b w)
  simp only [ContinuousLinearEquiv.symm_apply_apply, NNReal.coe_one, one_mul] at h
  exact h.trans_lt hdist

theorem normalCoordinates_half_disk_mem (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ unitDisk V.val 0)
    {t : ℝ} (ht : t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    normalCoordinatesWithBasis hv b ((1 / 2 : ℝ) • x, t) ∈
      unitDisk (normalLift hv b V).val 0 := by
  simp only [unitDisk, mem_ofPred_eq, sub_zero] at hx ⊢
  refine ⟨(normalCoordinates_mem_normalLift_iff hv b V _ _).mpr (V.val.smul_mem _ hx.1), ?_⟩
  have hsq := inner_normalCoordinatesWithBasis hv b ((1 / 2 : ℝ) • x)
    ((1 / 2 : ℝ) • x) t t
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hsq
  nlinarith [hx.2, norm_nonneg x, ht.1, ht.2,
    mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2),
    norm_nonneg (normalCoordinatesWithBasis hv b ((1 / 2 : ℝ) • x, t))]

theorem normalCoordinates_half_plate_mem (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    {δ : ℝ} (hδ : 0 < δ) {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ plate δ V.val 0)
    {t : ℝ} (ht : t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    normalCoordinatesWithBasis hv b ((1 / 2 : ℝ) • x, t) ∈
      plate δ (normalLift hv b V).val 0 := by
  obtain ⟨y, hy, hdist⟩ := mem_thickening_iff.mp hx
  refine mem_thickening_iff.mpr ⟨_, normalCoordinates_half_disk_mem hv b V hy ht, ?_⟩
  rw [dist_eq_norm, ← map_sub]
  simp only [Prod.mk_sub_mk, sub_self, ← smul_sub, normalCoordinatesWithBasis_apply,
    zero_smul, add_zero, Submodule.norm_coe, LinearIsometryEquiv.norm_map, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [dist_eq_norm] at hdist
  linarith

end NKBesicovitch.Induction
