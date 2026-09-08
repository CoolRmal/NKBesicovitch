/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerJunction
public import NKBesicovitch.Projection.BalancedCorners

/-!
# Lifting a restricted parent family to corners

For each retained parent pair, the last line is chosen from its companion
fiber at the other junction. The corner mass is the integral of this fiber
mass over the retained parent family.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Corners with parent pair in `U` and last line in `B`. -/
def parentCorners (a b : ℝ) (U : Set (PairCoordinates m)) (B : Set (Line m)) :
    Set (CornerCoordinates m) := {p | cornerParent a p ∈ U ∧ cornerLast b p ∈ B}

theorem measurableSet_parentCorners (a b : ℝ) {U : Set (PairCoordinates m)}
    (hU : MeasurableSet U) {B : Set (Line m)} (hB : MeasurableSet B) :
    MeasurableSet (parentCorners a b U B) :=
  (hU.preimage (by unfold cornerParent atHeight; fun_prop)).inter
    (hB.preimage (by unfold cornerLast lineAt atHeight; fun_prop))

theorem volume_parentCorners (a b : ℝ) {U : Set (PairCoordinates m)}
    (hU : MeasurableSet U) {B : Set (Line m)} (hB : MeasurableSet B) :
    volume (parentCorners a b U B) =
      ∫⁻ p in U, sliceMultiplicity b B (atHeight b (lineAt a p.1 p.2.1)) := by
  let S := (fun p : PairCoordinates m × EuclideanSpace ℝ (Fin m) ↦
    cornerFromParent a p.1 p.2) ⁻¹' parentCorners a b U B
  have hS : MeasurableSet S :=
    (measurableSet_parentCorners a b hU hB).preimage (measurable_cornerFromParent a)
  have he : cornerParentCoordinates a ⁻¹' S = parentCorners a b U B := by
    ext p
    change cornerFromParent a (cornerParentCoordinates a p).1
      (cornerParentCoordinates a p).2 ∈ parentCorners a b U B ↔ _
    rw [cornerFromParent_cornerParentCoordinates]
  rw [← he, (measurePreserving_cornerParentCoordinates a).measure_preimage hS.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply hS, ← lintegral_indicator hU]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ U
  · rw [Set.indicator_of_mem hp]
    have hs : Prod.mk p ⁻¹' S = lineAt b (atHeight b (lineAt a p.1 p.2.1)) ⁻¹' B := by
      ext ξ
      change (cornerParent a (cornerFromParent a p ξ) ∈ U ∧
        lineAt b (atHeight b (lineAt a p.1 p.2.1)) ξ ∈ B) ↔ _
      rw [cornerParent_cornerFromParent]
      simp only [hp, true_and, Set.mem_preimage]
    rw [hs]
    rfl
  · rw [Set.indicator_of_notMem hp]
    have hs : Prod.mk p ⁻¹' S = ∅ := by
      ext ξ
      change (cornerParent a (cornerFromParent a p ξ) ∈ U ∧
        cornerLast b (cornerFromParent a p ξ) ∈ B) ↔ False
      simp only [cornerParent_cornerFromParent, hp, false_and]
    rw [hs, measure_empty]

/-- Every retained parent has exactly the prescribed mass of last companions. -/
theorem volume_parentCorners_of_constant_mass (a b : ℝ) {U : Set (PairCoordinates m)}
    (hU : MeasurableSet U) {B : Set (Line m)} (hB : MeasurableSet B) (η : ℝ≥0∞)
    (hη : ∀ p ∈ U, sliceMultiplicity b B (atHeight b (lineAt a p.1 p.2.1)) = η) :
    volume (parentCorners a b U B) = volume U * η := by
  rw [volume_parentCorners a b hU hB]
  calc
    _ = ∫⁻ _p in U, η := setLIntegral_congr_fun hU hη
    _ = _ := by simp [mul_comm]

theorem parentCorners_eq_inter {a b : ℝ} {U : Set (PairCoordinates m)}
    {G₀ A B : Set (Line m)} (hU : U ⊆ companionPairs a G₀ A) :
    parentCorners a b U B = companionCorners a b G₀ A B ∩ cornerParent a ⁻¹' U := by
  ext p
  constructor
  · intro hp
    have h := hU hp.1
    refine ⟨⟨?_, h.2, hp.2⟩, hp.1⟩
    simpa only [first_cornerParent] using h.1
  · intro hp
    exact ⟨hp.2, hp.1.2.2⟩

end NKBesicovitch.Projection
