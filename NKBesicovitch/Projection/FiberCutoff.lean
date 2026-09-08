/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Measurable cutoffs for continuous fiber masses

A monotone cumulative mass on a compact interval reaches every admissible
target mass. Taking the supremum of the strict sublevel set gives a cutoff
measurable in the fiber parameter. This is the selection mechanism used in
the companion construction.
-/

@[expose] public section

open MeasureTheory Set unitInterval
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {X : Type*}

/-- The last cutoff before a monotone cumulative mass reaches the target. -/
noncomputable def fiberCutoff (F : X → I → ℝ≥0∞) (η : ℝ≥0∞) (x : X) : I :=
  sSup {t | F x t < η}

theorem measurable_fiberCutoff [MeasurableSpace X] {F : X → I → ℝ≥0∞}
    (hF : ∀ t, Measurable (fun x ↦ F x t)) (hmono : ∀ x, Monotone (F x)) (η : ℝ≥0∞) :
    Measurable (fiberCutoff F η) := by
  apply measurable_of_Ioi
  intro a
  have he : {x | a < fiberCutoff F η x} =
      ⋃ (q : ℚ) (hq : (q : ℝ) ∈ I) (_ : (a : ℝ) < q), {x | F x ⟨q, hq⟩ < η} := by
    ext x
    constructor
    · intro hx
      change a < sSup {t | F x t < η} at hx
      obtain ⟨t, ht, hat⟩ := lt_sSup_iff.mp hx
      obtain ⟨q, haq, hqt⟩ := exists_rat_btwn (show (a : ℝ) < t from hat)
      have hq : (q : ℝ) ∈ I := ⟨a.2.1.trans haq.le, hqt.le.trans t.2.2⟩
      exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hq, mem_iUnion.mpr
        ⟨haq, (hmono x (show (⟨q, hq⟩ : I) ≤ t from hqt.le)).trans_lt ht⟩⟩⟩
    · intro hx
      obtain ⟨q, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hq, hx⟩ := mem_iUnion.mp hx
      obtain ⟨haq, hx⟩ := mem_iUnion.mp hx
      change a < sSup {t | F x t < η}
      exact lt_sSup_iff.mpr ⟨⟨q, hq⟩, hx, haq⟩
  change MeasurableSet {x | a < fiberCutoff F η x}
  rw [he]
  exact MeasurableSet.iUnion fun q ↦ MeasurableSet.iUnion fun hq ↦
    MeasurableSet.iUnion fun _ ↦ measurableSet_lt (hF ⟨q, hq⟩) measurable_const

/-- The measurable cutoff has exactly the target mass, including the endpoint targets. -/
theorem apply_fiberCutoff {F : X → I → ℝ≥0∞} {x : X} (hmono : Monotone (F x))
    (hcont : Continuous (F x)) (hzero : F x 0 = 0) {η : ℝ≥0∞} (hη : η ≤ F x 1) :
    F x (fiberCutoff F η x) = η := by
  rw [fiberCutoff, hmono.map_sSup_of_continuousAt hcont.continuousAt hzero]
  apply le_antisymm
  · apply sSup_le
    rintro r ⟨t, ht, rfl⟩
    exact ht.le
  · apply le_of_not_gt
    intro hlt
    obtain ⟨r, hsr, hrη⟩ := exists_between hlt
    have hr : r ∈ Icc (F x 0) (F x 1) :=
      ⟨by rw [hzero]; exact bot_le, hrη.le.trans hη⟩
    obtain ⟨t, ht⟩ := intermediate_value_univ (0 : I) 1 hcont hr
    exact hsr.not_ge (le_sSup ⟨t, show F x t < η by rwa [ht], ht⟩)

end NKBesicovitch.Projection
