/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PatternExistence
public import NKBesicovitch.Projection.TreeConstruction
public import NKBesicovitch.Projection.TreeNormalized
public import NKBesicovitch.Projection.CornerDepth

/-!
# The normalized corner improvement

An input projection estimate at `1 < β ≤ 2` gives every exponent strictly
above `cornerUpdate β` for bounded Borel line families with parallel
multiplicity at most one and projection-size bound at least one.
All heights, the finite tree, and the final constant are chosen before the
line family. No pattern, stopping node, or companion family is left as an
assumption. Restoring the general multiplicity factor requires dilation.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem exists_normalized_corner_improvement [Nonempty (Fin m)]
    {β β' : ℝ} (hβ : 1 < β) (hβ2 : β ≤ 2) (hgap : cornerUpdate β < β')
    {Γ : Finset ℝ} (hΓ : Γ.Nonempty) (hEstimate : HasProjectionEstimate m β Γ) :
    ∃ Δ : Finset ℝ, Δ.Nonempty ∧ ∃ C : ℝ, 0 < C ∧
      ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
      (parallelMultiplicity G).toReal ≤ 1 →
      ∀ N : ℝ, 1 ≤ N → (∀ t ∈ Δ, volume (atHeight t '' G) ≤ ENNReal.ofReal N) →
      (volume G).toReal ≤ C * N ^ β' := by
  obtain ⟨J, hJ, hdepth⟩ := exists_depth_for_corner_update hβ hgap
  obtain ⟨T, _, _, _⟩ := CornerTree.exists_of_patterns
    (exists_cornerPattern hΓ hEstimate) J 0 1 2 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC, hbound⟩ := T.exists_normalized_bound hJ hβ hβ2
  refine ⟨T.times, T.times_nonempty, C, hC, fun G hG hGb hM N hN hπ ↦ ?_⟩
  exact (hbound G hG hGb hM N hN hπ).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (hdepth J le_rfl).le) hC.le)

end NKBesicovitch.Projection
