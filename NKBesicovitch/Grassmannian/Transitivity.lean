/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.Action

/-!
# Existence of directions and transitivity of rotations

An isometry between two subspaces of the same dimension extends to an ambient
orthogonal transformation. In particular, every direction is an orbit point
of any fixed direction.
-/

@[expose] public section

namespace NKBesicovitch.Grassmannian

variable {n k : ℕ}

theorem nonempty_iff : Nonempty (Grassmannian n k) ↔ k ≤ n := by
  constructor
  · rintro ⟨V⟩
    simpa [V.property] using Submodule.finrank_le V.submodule
  · intro hkn
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ℝ) (M := Space n)
      (by simpa using hkn)
    exact ⟨⟨Submodule.span ℝ (Set.range f), by simpa using finrank_span_eq_card hf⟩⟩

/-- An intrinsic linear isometry between two directions of the same dimension. -/
noncomputable def isometry (V W : Grassmannian n k) : V.submodule ≃ₗᵢ[ℝ] W.submodule :=
  (stdOrthonormalBasis ℝ V.submodule).repr.trans
    ((stdOrthonormalBasis ℝ W.submodule).reindex
      (finCongr (W.property.trans V.property.symm))).repr.symm

theorem exists_rotate_eq (V W : Grassmannian n k) : ∃ u : Rotations n, rotate u V = W := by
  let L : V.submodule →ₗᵢ[ℝ] Space n :=
    W.submodule.subtypeₗᵢ.comp (isometry V W).toLinearIsometry
  let e : Space n ≃ₗᵢ[ℝ] Space n := L.extend.toLinearIsometryEquiv rfl
  refine ⟨Unitary.linearIsometryEquiv.symm e, ?_⟩
  apply Subtype.ext
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    change e v ∈ W.submodule
    change L.extend v ∈ W.submodule
    rw [L.extend_apply ⟨v, hv⟩]
    exact (isometry V W ⟨v, hv⟩).property
  · exact (rotate _ V).property.trans W.property.symm

instance : MulAction.IsPretransitive (Rotations n) (Grassmannian n k) where
  exists_smul_eq := exists_rotate_eq

end NKBesicovitch.Grassmannian
