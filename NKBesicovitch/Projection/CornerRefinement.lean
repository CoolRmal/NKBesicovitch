/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerOuterMeasure
public import NKBesicovitch.Projection.PairRefinement

/-!
# Removing corners with low outer density

The exact restricted-mass identity bounds the deleted corner volume by the
threshold times the outer-data size. The latter is an outer measure.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem support_cornerOuterDensity_subset {a b c κ u : ℝ} (hab : a ≠ b) (hua : u ≠ a)
    (D : Set (CornerCoordinates m)) :
    Function.support (cornerOuterDensity a b c κ u D) ⊆ cornerOuterData a b c κ u '' D := by
  intro yz hyz
  by_contra h
  have hz (s : Line m) : cornerFromOuter a b c κ u yz s ∉ D := by
    intro hs
    exact h ⟨_, hs, cornerOuterData_cornerFromOuter hab hua yz s⟩
  apply hyz
  change codeJacobian m a b ^ 2 * ∫⁻ s,
    D.indicator (1 : CornerCoordinates m → ℝ≥0∞) (cornerFromOuter a b c κ u yz s) = 0
  simp [Set.indicator_of_notMem, hz]

theorem volume_low_cornerOuterDensity_le {a b c κ u : ℝ} (hab : a ≠ b) (hua : u ≠ a)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D) {S : Set (Line m)}
    (hS : cornerOuterData a b c κ u '' D ⊆ S) (τ : ℝ≥0∞) :
    volume (D ∩ {p | cornerOuterDensity a b c κ u D (cornerOuterData a b c κ u p) < τ}) ≤
      τ * volume S := by
  change volume (D ∩ cornerOuterData a b c κ u ⁻¹'
    {yz | cornerOuterDensity a b c κ u D yz < τ}) ≤ _
  rw [← setLIntegral_cornerOuterDensity hab hua hD
    (measurableSet_lt (measurable_cornerOuterDensity a b c κ u hD) measurable_const)]
  exact setLIntegral_lt_le_mul_measure (measurable_cornerOuterDensity a b c κ u hD)
    ((support_cornerOuterDensity_subset hab hua D).trans hS) τ

/-- A product bound using the first-line projection and the allowed inner-pair codes. -/
theorem volume_low_cornerOuterDensity_le_mul {a b c κ u : ℝ} (hab : a ≠ b) (hua : u ≠ a)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D) {G : Set (Line m)}
    (hDG : D ⊆ cornerFamily a b G) {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : ∀ p ∈ D, pairCode b a (cornerInnerCoefficient a c κ u) (cornerInner b p) ∈ B)
    (τ : ℝ≥0∞) :
    volume (D ∩ {p | cornerOuterDensity a b c κ u D (cornerOuterData a b c κ u p) < τ}) ≤
      τ * (volume (atHeight u '' G) * volume B) := by
  have hS : cornerOuterData a b c κ u '' D ⊆ (atHeight u '' G) ×ˢ B := by
    rintro yz ⟨p, hp, rfl⟩
    exact ⟨⟨cornerFirst a p, (hDG hp).1, rfl⟩, hB p hp⟩
  simpa only [Measure.volume_eq_prod, Measure.prod_prod] using
    volume_low_cornerOuterDensity_le hab hua hD hS τ

end NKBesicovitch.Projection
