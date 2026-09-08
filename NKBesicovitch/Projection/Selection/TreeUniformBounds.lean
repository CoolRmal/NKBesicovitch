/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.TreeParameters
public import NKBesicovitch.Projection.Selection.NodeUniformBounds

/-!
# Polynomial bounds on all selected tree coordinates

Every child remains based at a separated triple in the original time set.
Consequently the same node bound applies at every depth, with no increase
in the coordinate-bound exponent as the tree grows.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

theorem tree_coordinates_uniform_bound {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) (J : ℕ) {q : (ℝ × ℝ) × ℝ}
    (hq : q ∈ separatedTriples I ((volume I).toReal / 100))
    {σ : TreeCoordinate D L J → ℝ} (hσ : σ ∈ S.treeParameters I J q)
    (j : TreeCoordinate D L J) :
    |σ j| ≤ S.upperConstant * (100 / (volume I).toReal) ^ (8 * S.boundExponent) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  induction J generalizing q with
  | zero => exact Fin.elim0 j
  | succ J ih =>
    rcases j with (u | j | ⟨i, j⟩) | ⟨ij, j⟩
    · cases u
      exact S.node_scalar_uniform_bound hIunit hIpos hq hσ.1
    · exact S.node_outer_coordinates_uniform_bound hI hIunit hIpos hσ.1 j
    · exact S.node_inner_coordinates_uniform_bound hI hIunit hIpos hσ.1 i j
    · exact ih (S.cornerNodeParameters_child_triple hI hIunit hIpos (by positivity)
        (mem_separatedTriples.mp hq).2.1 hσ.1 ij.1 ij.2) (hσ.2 ij) j

/-- One positive polynomial coordinate constant works simultaneously at all depths. -/
theorem exists_tree_coordinate_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
      ∀ (J : ℕ) q, q ∈ separatedTriples I ((volume I).toReal / 100) →
        ∀ σ ∈ S.treeParameters I J q, ∀ j,
          |σ j| ≤ C * ((volume I).toReal⁻¹) ^ (8 * S.boundExponent) := by
  refine ⟨S.upperConstant * 100 ^ (8 * S.boundExponent),
    one_le_mul_of_one_le_of_one_le S.one_le_upperConstant (one_le_pow₀ (by norm_num)),
    fun I hI hIunit hIpos J q hq σ hσ j ↦ ?_⟩
  simpa only [div_eq_mul_inv, mul_pow, mul_assoc] using
    S.tree_coordinates_uniform_bound hI hIunit hIpos J hq hσ j

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
