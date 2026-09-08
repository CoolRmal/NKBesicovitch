/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Coordinates relative to a unit normal

The map `(x,t) ↦ x + t • v`, with `x` perpendicular to a unit vector `v`,
identifies the product of the normal hyperplane and the real line with
the ambient space. It preserves Lebesgue volume. The product carries
its usual product norm; its Euclidean norm is used only inside the
construction of the coordinate equivalence.
-/

@[expose] public section

open MeasureTheory Submodule
open scoped InnerProductSpace

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : E}

/-- Horizontal displacement and signed height relative to a unit normal. -/
noncomputable def normalCoordinates (hv : ‖v‖ = 1) : ((ℝ ∙ v)ᗮ × ℝ) ≃L[ℝ] E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ ∙ v)ᗮ ℝ).symm.trans
    (((LinearIsometryEquiv.withLpProdComm 2 ℝ (ℝ ∙ v)ᗮ ℝ).trans
      ((LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.toSpanUnitSingleton v hv)
        (LinearIsometryEquiv.refl ℝ (ℝ ∙ v)ᗮ)).trans
          (ℝ ∙ v).orthogonalDecomposition.symm)).toContinuousLinearEquiv)

theorem normalCoordinates_apply (hv : ‖v‖ = 1) (x : (ℝ ∙ v)ᗮ) (t : ℝ) :
    normalCoordinates hv (x, t) = (x : E) + t • v := by
  simp [normalCoordinates, add_comm]

theorem inner_normalCoordinates (hv : ‖v‖ = 1) (x : (ℝ ∙ v)ᗮ) (t : ℝ) :
    ⟪v, normalCoordinates hv (x, t)⟫_ℝ = t := by
  rw [normalCoordinates_apply, inner_add_right, inner_smul_right,
    mem_orthogonal_singleton_iff_inner_right.mp x.2, real_inner_self_eq_norm_sq, hv]
  simp

theorem normalCoordinates_symm_snd (hv : ‖v‖ = 1) (y : E) :
    ((normalCoordinates hv).symm y).2 = ⟪v, y⟫_ℝ := by
  obtain ⟨⟨x, t⟩, rfl⟩ := (normalCoordinates hv).surjective y
  rw [ContinuousLinearEquiv.symm_apply_apply, inner_normalCoordinates]

theorem normalCoordinates_symm_fst (hv : ‖v‖ = 1) (y : E) :
    ((normalCoordinates hv).symm y).1 = (ℝ ∙ v)ᗮ.orthogonalProjectionOnto y := by
  obtain ⟨⟨x, t⟩, rfl⟩ := (normalCoordinates hv).surjective y
  rw [ContinuousLinearEquiv.symm_apply_apply, normalCoordinates_apply, map_add, map_smul,
    orthogonalProjectionOnto_mem_subspace_eq_self,
    orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, smul_zero, add_zero]

theorem norm_normalCoordinates_sq (hv : ‖v‖ = 1) (x : (ℝ ∙ v)ᗮ) (t : ℝ) :
    ‖normalCoordinates hv (x, t)‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 := by
  rw [normalCoordinates_apply, norm_add_sq_real]
  simp [norm_smul, hv, inner_smul_right,
    mem_orthogonal_singleton_iff_inner_left.mp x.2]

/-- Normal coordinates with an orthonormal basis in the transverse hyperplane. -/
noncomputable def normalCoordinatesWithBasis {m : ℕ} (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    (EuclideanSpace ℝ (Fin m) × ℝ) ≃L[ℝ] E :=
  (b.toContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans
    (normalCoordinates hv)

theorem normalCoordinatesWithBasis_apply {m : ℕ} (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    (x : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    normalCoordinatesWithBasis hv b (x, t) = (b x : E) + t • v :=
  normalCoordinates_apply hv (b x) t

theorem inner_normalCoordinatesWithBasis {m : ℕ} (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    (x y : EuclideanSpace ℝ (Fin m)) (t s : ℝ) :
    ⟪normalCoordinatesWithBasis hv b (x, t), normalCoordinatesWithBasis hv b (y, s)⟫_ℝ =
      ⟪x, y⟫_ℝ + t * s := by
  simp only [normalCoordinatesWithBasis_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, conj_trivial,
    mem_orthogonal_singleton_iff_inner_left.mp (b x).2,
    mem_orthogonal_singleton_iff_inner_right.mp (b y).2,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one, mul_zero, zero_add, add_zero]
  change ⟪b x, b y⟫_ℝ + s * t = ⟪x, y⟫_ℝ + t * s
  rw [b.inner_map_map, mul_comm s t]

theorem norm_normalCoordinatesWithBasis_symm_fst_le {m : ℕ} (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (z : E) :
    ‖((normalCoordinatesWithBasis hv b).symm z).1‖ ≤ ‖z‖ := by
  obtain ⟨⟨x, t⟩, rfl⟩ := (normalCoordinatesWithBasis hv b).surjective z
  rw [ContinuousLinearEquiv.symm_apply_apply]
  have h := inner_normalCoordinatesWithBasis hv b x x t t
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [sq_nonneg t, norm_nonneg (normalCoordinatesWithBasis hv b (x, t))]

theorem lipschitz_normalCoordinatesWithBasis_symm_fst {m : ℕ} (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    LipschitzWith 1 (fun z ↦ ((normalCoordinatesWithBasis hv b).symm z).1) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul, map_sub, Prod.fst_sub] using
    norm_normalCoordinatesWithBasis_symm_fst_le hv b (x - y)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem measurePreserving_normalCoordinates (hv : ‖v‖ = 1) :
    MeasurePreserving (normalCoordinates hv) volume volume := by
  let i := (LinearIsometryEquiv.withLpProdComm 2 ℝ (ℝ ∙ v)ᗮ ℝ).trans
    ((LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.toSpanUnitSingleton v hv)
      (LinearIsometryEquiv.refl ℝ (ℝ ∙ v)ᗮ)).trans (ℝ ∙ v).orthogonalDecomposition.symm)
  exact i.measurePreserving.comp (WithLp.volume_preserving_toLp (ℝ ∙ v)ᗮ ℝ)

theorem measurePreserving_normalCoordinatesWithBasis {m : ℕ} (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    MeasurePreserving (normalCoordinatesWithBasis hv b) volume volume := by
  have heq : (normalCoordinatesWithBasis hv b : (EuclideanSpace ℝ (Fin m) × ℝ) → E) =
      fun z ↦ normalCoordinates hv (b z.1, z.2) := rfl
  rw [heq]
  have hprod := b.measurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ))
  simpa only [Measure.volume_eq_prod, Function.comp_def, Prod.map_def, id_eq] using
    (measurePreserving_normalCoordinates hv).comp hprod

end NKBesicovitch
