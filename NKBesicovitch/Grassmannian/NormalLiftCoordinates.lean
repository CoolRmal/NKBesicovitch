/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.NormalLift

/-!
# Intrinsic Euclidean coordinates on lifted planes

The lifted plane is the orthogonal product of the original plane and the
adjoined unit line. Its intrinsic Lebesgue measure is therefore the product
of the lower-dimensional plane measure and arclength.
-/

@[expose] public section

open MeasureTheory

namespace NKBesicovitch.Grassmannian

variable {n m k : ℕ} {v : EuclideanSpace ℝ (Fin n)}

/-- Orthogonal product coordinates on a plane obtained by adjoining a unit normal. -/
noncomputable def normalLiftCoordinates (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k) :
    WithLp 2 (V.val × ℝ) ≃ₗᵢ[ℝ] (normalLift hv b V).val := by
  let L : WithLp 2 (V.val × ℝ) →ₗ[ℝ] (normalLift hv b V).val :=
    { toFun z := ⟨normalCoordinatesWithBasis hv b (z.ofLp.1, z.ofLp.2),
        (normalCoordinates_mem_normalLift_iff hv b V _ _).mpr z.ofLp.1.2⟩
      map_add' z w := by
        apply Subtype.ext
        simp only [WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, Submodule.coe_add,
          ← Prod.mk_add_mk, map_add, Submodule.coe_add]
      map_smul' r z := by
        apply Subtype.ext
        change normalCoordinatesWithBasis hv b
          (r • ((z.ofLp.1 : EuclideanSpace ℝ (Fin m)), z.ofLp.2)) =
          r • normalCoordinatesWithBasis hv b (z.ofLp.1, z.ofLp.2)
        exact map_smul (normalCoordinatesWithBasis hv b) r _ }
  let i : WithLp 2 (V.val × ℝ) →ₗᵢ[ℝ] (normalLift hv b V).val :=
    { toLinearMap := L
      norm_map' z := by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [WithLp.prod_norm_sq_eq_of_L2]
        change ‖normalCoordinatesWithBasis hv b (z.ofLp.1, z.ofLp.2)‖ ^ 2 =
          ‖z.ofLp.1‖ ^ 2 + ‖z.ofLp.2‖ ^ 2
        have h := norm_normalCoordinates_sq hv (b (z.ofLp.1 : EuclideanSpace ℝ (Fin m)))
          z.ofLp.2
        simpa only [Submodule.norm_coe, normalCoordinatesWithBasis_apply,
          normalCoordinates_apply, b.norm_map,
          Real.norm_eq_abs, sq_abs] using h }
  apply LinearIsometryEquiv.ofSurjective i
  intro z
  obtain ⟨x, hx, t, h⟩ := (mem_normalLift_iff hv b V z).mp z.2
  exact ⟨WithLp.toLp 2 (⟨x, hx⟩, t), Subtype.ext h⟩

theorem normalLiftCoordinates_apply (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    (z : WithLp 2 (V.val × ℝ)) :
    (normalLiftCoordinates hv b V z : EuclideanSpace ℝ (Fin n)) =
      normalCoordinatesWithBasis hv b (z.ofLp.1, z.ofLp.2) := rfl

end NKBesicovitch.Grassmannian
