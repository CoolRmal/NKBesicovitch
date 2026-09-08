/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerFiberSelection
public import NKBesicovitch.Projection.CornerProjection
public import NKBesicovitch.Projection.SimultaneousCorners

/-!
# A common corner-code fiber with simultaneous projection bounds

If the outer-density cutoffs discard at most half the corner mass, some
positive code fiber retains half its density and satisfies all selected
first-line projection bounds.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι : Type*}

theorem exists_denseCorner_code {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    (u : ι → ℝ) (I : Finset ι) (hua : ∀ i ∈ I, u i ≠ a)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D)
    (hpos : 0 < volume D) (hfin : volume D ≠ ∞) (τ : ℝ≥0∞)
    (S : ι → Set (Line m)) (hS : ∀ i ∈ I, cornerOuterData a b c κ (u i) '' D ⊆ S i)
    (hbudget : ∑ i ∈ I, τ * volume (S i) ≤ volume D / 2) :
    let D' := denseCorners a b c κ u I D τ
    ∃ z, 0 < cornerDensity a b c κ D z ∧
      cornerDensity a b c κ D z ≤ 2 * cornerDensity a b c κ D' z ∧
      ∀ i ∈ I, τ * volume (atHeight (u i) '' cornerFiber a b c κ D' z) ≤
        cornerDensity a b c κ D z := by
  let D' := denseCorners a b c κ u I D τ
  have hD' : MeasurableSet D' := measurableSet_denseCorners a b c κ u I hD τ
  have hsub : D' ⊆ D := denseCorners_subset a b c κ u I D τ
  have hhalf : volume D / 2 ≤ volume D' :=
    half_volume_le_volume_denseCorners hab u I hua hD hfin τ S hS hbudget
  have hmass : volume D ≤ 2 * volume D' := by
    calc
      _ = volume D / 2 + volume D / 2 := (ENNReal.add_halves _).symm
      _ ≤ volume D' + volume D' := add_le_add hhalf hhalf
      _ = _ := (two_mul _).symm
  obtain ⟨z, hz, hratio⟩ := exists_good_corner_code hab c κ hD hD' hsub hpos hfin hmass
  refine ⟨z, hz, hratio, fun i hi ↦ ?_⟩
  exact mul_volume_projection_cornerFiber_le hab (hua i hi) hD τ
    (fun _ hp ↦ le_cornerOuterDensity_of_mem_denseCorners hp hi) z

end NKBesicovitch.Projection
