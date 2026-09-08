/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Transverse intercept coordinates

If two normal vectors have nonzero inner product, orthogonal projection
from the first normal hyperplane to the second is a linear isomorphism.
It is a contraction. This is the change from horizontal intercepts to
perpendicular displacements in a nonvertical direction chart.
-/

@[expose] public section

open Submodule
open scoped InnerProductSpace

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v w : E}

theorem injective_transverseProjection (hvw : ⟪v, w⟫_ℝ ≠ 0) :
    Function.Injective ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto.comp (ℝ ∙ v)ᗮ.subtypeL) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hspan : (x : E) ∈ ℝ ∙ w := by
    rw [← orthogonal_orthogonal (ℝ ∙ w), ← ker_orthogonalProjectionOnto]
    exact hx
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hspan
  have hinner := mem_orthogonal_singleton_iff_inner_right.mp x.2
  rw [← hc, inner_smul_right] at hinner
  have hc0 : c = 0 := (mul_eq_zero.mp hinner).resolve_right hvw
  apply Subtype.ext
  simpa only [hc0, zero_smul, Submodule.coe_zero] using hc.symm

theorem surjective_transverseProjection (hvw : ⟪v, w⟫_ℝ ≠ 0) :
    Function.Surjective ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto.comp (ℝ ∙ v)ᗮ.subtypeL) := by
  intro y
  have hx : (y : E) - (⟪v, y⟫_ℝ / ⟪v, w⟫_ℝ) • w ∈ (ℝ ∙ v)ᗮ := by
    rw [mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
      div_mul_cancel₀ _ hvw, sub_self]
  refine ⟨⟨_, hx⟩, ?_⟩
  change (ℝ ∙ w)ᗮ.orthogonalProjectionOnto
    ((y : E) - (⟪v, y⟫_ℝ / ⟪v, w⟫_ℝ) • w) = y
  rw [map_sub, map_smul, orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
    orthogonalProjectionOnto_mem_subspace_eq_self, smul_zero, sub_zero]

variable [FiniteDimensional ℝ E]

/-- Orthogonal projection between transverse normal hyperplanes as a linear homeomorphism. -/
noncomputable def transverseEquiv (hvw : ⟪v, w⟫_ℝ ≠ 0) : (ℝ ∙ v)ᗮ ≃L[ℝ] (ℝ ∙ w)ᗮ :=
  (LinearEquiv.ofBijective
    ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto.comp (ℝ ∙ v)ᗮ.subtypeL).toLinearMap
      ⟨injective_transverseProjection hvw,
        surjective_transverseProjection hvw⟩).toContinuousLinearEquiv

theorem transverseEquiv_apply (hvw : ⟪v, w⟫_ℝ ≠ 0) (x : (ℝ ∙ v)ᗮ) :
    transverseEquiv hvw x = (ℝ ∙ w)ᗮ.orthogonalProjectionOnto x := rfl

theorem norm_transverseEquiv_le (hvw : ⟪v, w⟫_ℝ ≠ 0) (x : (ℝ ∙ v)ᗮ) :
    ‖transverseEquiv hvw x‖ ≤ ‖x‖ := (ℝ ∙ w)ᗮ.norm_orthogonalProjectionOnto_apply_le x

theorem sub_transverseEquiv_mem_span (hvw : ⟪v, w⟫_ℝ ≠ 0) (x : (ℝ ∙ v)ᗮ) :
    (x : E) - transverseEquiv hvw x ∈ ℝ ∙ w := by
  simpa only [transverseEquiv_apply, coe_orthogonalProjectionOnto_apply,
    orthogonal_orthogonal] using
    sub_starProjection_mem_orthogonal (K := (ℝ ∙ w)ᗮ) (x : E)

end NKBesicovitch.XRay
