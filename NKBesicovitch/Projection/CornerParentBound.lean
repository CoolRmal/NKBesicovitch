/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerParent
public import NKBesicovitch.Projection.CodeBound

/-!
# The corner bound from low parent-pair density

The bound uses the parent density only on pairs occurring in the corner
family. Exceptional parallel slopes are handled through the affine code map,
so the conclusion holds at every corner-code value.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem mul_cornerParentSliceMass_le_parentDensity {a c : ℝ} (hca : c ≠ a) (b κ : ℝ)
    {D : Set (CornerCoordinates m)} {W : Set (PairCoordinates m)}
    (hDW : ∀ p ∈ D, cornerParent a p ∈ W) (z y x : EuclideanSpace ℝ (Fin m)) :
    pairJacobian m a b c * cornerParentSliceMass a b c κ D z y x ≤
      pairDensity a b c W (x + b • ((a - b)⁻¹ • (z - κ • y)), y) := by
  apply mul_le_mul le_rfl _ bot_le bot_le
  apply lintegral_mono
  intro w
  dsimp only
  by_cases hp : cornerFromCode a b c κ (lineAt a w ((c - a)⁻¹ • (y - w))) x z ∈ D
  · have hw := hDW _ hp
    rw [cornerParent_cornerFromCode_positions hca] at hw
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hw]
    exact le_rfl
  · simp [Set.indicator_of_notMem hp]

theorem mul_cornerParentSliceMass_le_parallelIndicator {a b c κ : ℝ}
    (hab : a ≠ b) (hca : c ≠ a) {D : Set (CornerCoordinates m)} {G : Set (Line m)}
    (hDG : D ⊆ cornerFamily a b G) {W : Set (PairCoordinates m)}
    (hDW : ∀ p ∈ D, cornerParent a p ∈ W) (Q₀ : ℝ≥0∞)
    (hQ : ∀ p ∈ D, pairDensity a b c W (pairProjections a b c (cornerParent a p)) ≤ Q₀)
    (z y x : EuclideanSpace ℝ (Fin m)) :
    pairJacobian m a b c * cornerParentSliceMass a b c κ D z y x ≤
      {x : EuclideanSpace ℝ (Fin m) | (x, (a - b)⁻¹ • (z - κ • y)) ∈ G}.indicator
        (fun _ ↦ Q₀) x := by
  by_cases he : ∃ w, cornerFromCode a b c κ (lineAt a w ((c - a)⁻¹ • (y - w))) x z ∈ D
  · obtain ⟨w, hw⟩ := he
    have hx := (hDG hw).2.2
    rw [last_cornerFromCode hab, atHeight_lineAt_of_positions hca.symm] at hx
    rw [Set.indicator_of_mem (show x ∈
      {x : EuclideanSpace ℝ (Fin m) | (x, (a - b)⁻¹ • (z - κ • y)) ∈ G} from hx)]
    have h := hQ _ hw
    rw [cornerParent_cornerFromCode_positions hca,
      pairProjections_pairFromData hab.symm hca] at h
    exact (mul_cornerParentSliceMass_le_parentDensity hca b κ hDW z y x).trans h
  · have hz (w : EuclideanSpace ℝ (Fin m)) :
        cornerFromCode a b c κ (lineAt a w ((c - a)⁻¹ • (y - w))) x z ∉ D :=
      fun hw ↦ he ⟨w, hw⟩
    simp [cornerParentSliceMass, Set.indicator_of_notMem, hz]

theorem support_lintegral_cornerParentSliceMass_subset {a c : ℝ} (hca : c ≠ a) (b κ : ℝ)
    {D : Set (CornerCoordinates m)} {G : Set (Line m)} (hDG : D ⊆ cornerFamily a b G)
    (z : EuclideanSpace ℝ (Fin m)) :
    Function.support (fun y ↦ ∫⁻ x,
      pairJacobian m a b c * cornerParentSliceMass a b c κ D z y x) ⊆ atHeight c '' G := by
  intro y hy
  by_contra h
  have hz (x w : EuclideanSpace ℝ (Fin m)) :
      cornerFromCode a b c κ (lineAt a w ((c - a)⁻¹ • (y - w))) x z ∉ D := by
    intro hp
    have hg := (hDG hp).1
    rw [first_cornerFromCode] at hg
    exact h ⟨_, hg, atHeight_lineAt_of_positions hca.symm w y⟩
  exact hy (by simp [cornerParentSliceMass, Set.indicator_of_notMem, hz])

/-- The second corner-fiber bound, with the exact Jacobian and one projection size. -/
theorem cornerDensity_le_parentDensity_bound {a b c κ : ℝ}
    (hab : a ≠ b) (hca : c ≠ a) (hκ : κ ≠ 0)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D) {G : Set (Line m)}
    (hDG : D ⊆ cornerFamily a b G) {W : Set (PairCoordinates m)}
    (hDW : ∀ p ∈ D, cornerParent a p ∈ W) (Q₀ : ℝ≥0∞)
    (hQ : ∀ p ∈ D, pairDensity a b c W (pairProjections a b c (cornerParent a p)) ≤ Q₀)
    (z : EuclideanSpace ℝ (Fin m)) :
    cornerDensity a b c κ D z ≤
      codeJacobian m a b * (parallelMultiplicity G * volume (atHeight c '' G) * Q₀) := by
  have hi (y : EuclideanSpace ℝ (Fin m)) :
    (∫⁻ x, pairJacobian m a b c * cornerParentSliceMass a b c κ D z y x) ≤
      Q₀ * volume {x : EuclideanSpace ℝ (Fin m) | (x, (a - b)⁻¹ • (z - κ • y)) ∈ G} :=
    (lintegral_mono (fun x ↦
      mul_cornerParentSliceMass_le_parallelIndicator hab hca hDG hDW Q₀ hQ z y x)).trans
        (lintegral_indicator_const_le _ Q₀)
  have hM := (quasiMeasurePreserving_codeSlope hab.symm hκ z).ae
    (ENNReal.ae_le_essSup (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
      (fun ξ : EuclideanSpace ℝ (Fin m) ↦ volume {x : EuclideanSpace ℝ (Fin m) | (x, ξ) ∈ G}))
  have hae : ∀ᵐ y, (∫⁻ x,
      pairJacobian m a b c * cornerParentSliceMass a b c κ D z y x) ≤ Q₀ * parallelMultiplicity G :=
    hM.mono fun y hy ↦ (hi y).trans (mul_le_mul le_rfl hy bot_le bot_le)
  rw [cornerDensity_eq_parentSlices hca b κ hD]
  have h := lintegral_le_mul_measure_of_ae_le
    (support_lintegral_cornerParentSliceMass_subset hca b κ hDG z) hae
  have he : Q₀ * parallelMultiplicity G * volume (atHeight c '' G) =
      parallelMultiplicity G * volume (atHeight c '' G) * Q₀ := by ac_rfl
  rw [he] at h
  exact mul_le_mul le_rfl h bot_le bot_le

end NKBesicovitch.Projection
