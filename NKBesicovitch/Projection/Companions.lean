/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.SliceBallMass

/-!
# Measurable companions of prescribed fiber mass

Truncate each original slice fiber by a measurable slope radius. Every fiber
whose mass is at least the target then has exactly that target mass. Positive
dimension is explicit, since the construction uses null sphere boundaries.
-/

@[expose] public section

open MeasureTheory Set Bornology Metric unitInterval
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Radius chosen to reach the target mass in an original slice fiber. -/
noncomputable def companionRadius (a : ℝ) (G : Set (Line m)) (R : ℝ) (η : ℝ≥0∞)
    (y : EuclideanSpace ℝ (Fin m)) : ℝ := R * (fiberCutoff (sliceBallMass a G R) η y : ℝ)

/-- Original lines within the selected slope radius on their slice fiber. -/
noncomputable def companions (a : ℝ) (G : Set (Line m)) (R : ℝ) (η : ℝ≥0∞) : Set (Line m) :=
  G ∩ {g | ‖g.2‖ ≤ companionRadius a G R η (atHeight a g)}

theorem measurable_companionRadius (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G)
    {R : ℝ} (hR : 0 ≤ R) (η : ℝ≥0∞) : Measurable (companionRadius a G R η) :=
  measurable_const.mul ((measurable_fiberCutoff (measurable_sliceBallMass a R hG)
    (monotone_sliceBallMass a G hR) η).subtype_val)

theorem measurableSet_companions (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G)
    {R : ℝ} (hR : 0 ≤ R) (η : ℝ≥0∞) : MeasurableSet (companions a G R η) :=
  hG.inter (measurableSet_le (by fun_prop)
    ((measurable_companionRadius a hG hR η).comp (by unfold atHeight; fun_prop)))

theorem companions_subset (a : ℝ) (G : Set (Line m)) (R : ℝ) (η : ℝ≥0∞) :
    companions a G R η ⊆ G := inter_subset_left

theorem sliceMultiplicity_companions_eq_sliceBallMass (a R : ℝ) (G : Set (Line m))
    (η : ℝ≥0∞) (y : EuclideanSpace ℝ (Fin m)) :
    sliceMultiplicity a (companions a G R η) y =
      sliceBallMass a G R y (fiberCutoff (sliceBallMass a G R) η y) := by
  unfold sliceMultiplicity sliceBallMass
  congr 1
  ext ξ
  simp only [companions, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
    mem_closedBall, dist_zero_right, atHeight_lineAt, sub_self, zero_smul, add_zero]
  rfl

/-- Each sufficiently large original slice fiber has exactly the chosen companion mass. -/
theorem sliceMultiplicity_companions [Nonempty (Fin m)] (a : ℝ)
    {G : Set (Line m)} (hG : MeasurableSet G) (hGb : IsBounded G) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ g ∈ G, ‖g.2‖ ≤ R) (η : ℝ≥0∞) (y : EuclideanSpace ℝ (Fin m))
    (hη : η ≤ sliceMultiplicity a G y) : sliceMultiplicity a (companions a G R η) y = η := by
  rw [sliceMultiplicity_companions_eq_sliceBallMass]
  apply apply_fiberCutoff (monotone_sliceBallMass a G hR y)
    (continuous_sliceBallMass a R hG hGb y) (sliceBallMass_zero a R G y)
  rwa [sliceBallMass_one a R hbound]

/-- Every bounded Borel family in positive dimension admits Borel companions of target mass. -/
theorem exists_companions [Nonempty (Fin m)] (a : ℝ) {G : Set (Line m)}
    (hG : MeasurableSet G) (hGb : IsBounded G) (η : ℝ≥0∞) :
    ∃ C : Set (Line m), MeasurableSet C ∧ C ⊆ G ∧
      ∀ y, η ≤ sliceMultiplicity a G y → sliceMultiplicity a C y = η := by
  obtain ⟨R, hR, hbound⟩ := hGb.image_snd.exists_pos_norm_le
  refine ⟨companions a G R η, measurableSet_companions a hG hR.le η,
    companions_subset a G R η, fun y hη ↦ ?_⟩
  exact sliceMultiplicity_companions a hG hGb hR.le
    (fun g hg ↦ hbound g.2 ⟨g, hg, rfl⟩) η y hη

end NKBesicovitch.Projection
