/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Transporting normal hyperplanes by isometries

An ambient linear isometry equivalence carries the hyperplane normal to
`v` onto the hyperplane normal to its image. Its restriction preserves
the intrinsic Euclidean norm and hence, in finite dimension, volume.
-/

@[expose] public section

open Submodule

namespace NKBesicovitch

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The induced isometry between the normal hyperplanes of a vector and its image. -/
noncomputable def normalIsometry (e : E ≃ₗᵢ[ℝ] F) (v : E) : (ℝ ∙ v)ᗮ ≃ₗᵢ[ℝ] (ℝ ∙ e v)ᗮ :=
  (e.submoduleMap (ℝ ∙ v)ᗮ).trans (LinearIsometryEquiv.ofEq _ _ (by
    change ((ℝ ∙ v)ᗮ).map e.toLinearEquiv.toLinearMap = (ℝ ∙ e v)ᗮ
    rw [map_orthogonal_equiv, map_span, Set.image_singleton]
    rfl))

theorem coe_normalIsometry (e : E ≃ₗᵢ[ℝ] F) (v : E) (x : (ℝ ∙ v)ᗮ) :
    (normalIsometry e v x : F) = e (x : E) := rfl

end NKBesicovitch
