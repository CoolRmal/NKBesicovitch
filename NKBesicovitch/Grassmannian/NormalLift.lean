/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.Topology
public import NKBesicovitch.Geometry.NormalCoordinates
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Adjoining a perpendicular unit direction

An orthonormal identification with the normal hyperplane lifts a
`k`-plane to a `(k+1)`-plane containing the normal line. The projection
formula shows that this construction is continuous on the Grassmannian.
-/

@[expose] public section

open Submodule
open scoped InnerProductSpace

namespace NKBesicovitch.Grassmannian

variable {n m k : ℕ} {v : EuclideanSpace ℝ (Fin n)}

/-- Adjoin the unit normal line to a plane in orthonormal transverse coordinates. -/
noncomputable def normalLift (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k) :
    Grassmannian n (k + 1) := by
  let e := normalCoordinatesWithBasis hv b
  let L := e.toLinearMap.comp (V.val.subtype.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
  refine ⟨LinearMap.range L, ?_⟩
  have hL : Function.Injective L := by
    intro x y h
    have hxy := e.injective h
    change ((x.1 : EuclideanSpace ℝ (Fin m)), x.2) =
      ((y.1 : EuclideanSpace ℝ (Fin m)), y.2) at hxy
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hxy))
      (congrArg (fun z : EuclideanSpace ℝ (Fin m) × ℝ ↦ z.2) hxy)
  rw [LinearMap.finrank_range_of_inj hL, Module.finrank_prod, V.property, Module.finrank_self]

theorem mem_normalLift_iff (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    (z : EuclideanSpace ℝ (Fin n)) :
    z ∈ (normalLift hv b V).val ↔
      ∃ x ∈ V.val, ∃ t : ℝ, normalCoordinatesWithBasis hv b (x, t) = z := by
  constructor
  · rintro ⟨⟨x, t⟩, h⟩
    exact ⟨x, x.2, t, h⟩
  · rintro ⟨x, hx, t, h⟩
    exact ⟨(⟨x, hx⟩, t), h⟩

theorem normalCoordinates_mem_normalLift_iff (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    (x : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    normalCoordinatesWithBasis hv b (x, t) ∈ (normalLift hv b V).val ↔ x ∈ V.val := by
  rw [mem_normalLift_iff]
  constructor
  · rintro ⟨y, hy, s, h⟩
    have hxy : y = x := congrArg Prod.fst ((normalCoordinatesWithBasis hv b).injective h)
    exact hxy ▸ hy
  · intro hx
    exact ⟨x, hx, t, rfl⟩

theorem projection_normalLift_apply (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    (x : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    (normalLift hv b V).projection (normalCoordinatesWithBasis hv b (x, t)) =
      normalCoordinatesWithBasis hv b (V.projection x, t) := by
  apply eq_starProjection_of_mem_of_inner_eq_zero
  · exact (mem_normalLift_iff hv b V _).mpr ⟨V.projection x, Submodule.coe_mem _, t, rfl⟩
  · intro z hz
    obtain ⟨y, hy, s, rfl⟩ := (mem_normalLift_iff hv b V z).mp hz
    rw [← map_sub]
    simp only [Prod.mk_sub_mk, sub_self]
    rw [inner_normalCoordinatesWithBasis, zero_mul, add_zero]
    exact V.val.starProjection_inner_eq_zero x y hy

theorem projection_normalLift (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k) :
    (normalLift hv b V).projection = (normalCoordinatesWithBasis hv b).toContinuousLinearMap.comp
      ((V.projection.prodMap (ContinuousLinearMap.id ℝ ℝ)).comp
        (normalCoordinatesWithBasis hv b).symm.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro z
  obtain ⟨⟨x, t⟩, rfl⟩ := (normalCoordinatesWithBasis hv b).surjective z
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap',
    Prod.map_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearMap.id_apply] using projection_normalLift_apply hv b V x t

theorem continuous_normalLift (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) : Continuous (normalLift hv b (k := k)) := by
  apply continuous_induced_rng.mpr
  simp only [Function.comp_def, projection_normalLift]
  exact continuous_const.clm_comp
    ((Continuous.prod_mapL ℝ continuous_projection continuous_const).clm_comp
      continuous_const)

end NKBesicovitch.Grassmannian
