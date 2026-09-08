/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerFiberBound
public import NKBesicovitch.Projection.FiberSelection
public import NKBesicovitch.Projection.BoundedFamilies

/-!
# Retaining corner density on one code fiber

Corner densities are monotone in the corner family. A refinement retaining
half the total mass therefore retains half the density on some positive
code fiber. Boundedness gives finite masses and finite pointwise densities.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem cornerFiber_mono (a b c κ : ℝ) {D₀ D₁ : Set (CornerCoordinates m)}
    (hD : D₁ ⊆ D₀) (z : EuclideanSpace ℝ (Fin m)) :
    cornerFiber a b c κ D₁ z ⊆ cornerFiber a b c κ D₀ z := by
  rintro g ⟨x, hx⟩
  exact ⟨x, hD hx⟩

theorem cornerDensity_mono (a b c κ : ℝ) {D₀ D₁ : Set (CornerCoordinates m)}
    (hD : D₁ ⊆ D₀) : cornerDensity a b c κ D₁ ≤ cornerDensity a b c κ D₀ := by
  intro z
  apply mul_le_mul le_rfl _ bot_le bot_le
  apply lintegral_mono
  intro p
  exact indicator_le_indicator_of_subset hD (fun _ ↦ bot_le) _

theorem isBounded_cornerFamily (a b : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    IsBounded (cornerFamily a b G) := by
  apply (hG.prod (hG.image_snd.prod hG.image_snd)).subset
  intro p hp
  exact ⟨hp.2.1, ⟨cornerFirst a p, hp.1, rfl⟩, ⟨cornerLast b p, hp.2.2, rfl⟩⟩

theorem volume_cornerFamily_ne_top (a b : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    volume (cornerFamily a b G) ≠ ∞ := (isBounded_cornerFamily a b hG).measure_lt_top.ne

theorem cornerDensity_ne_top {a b κ : ℝ} (hab : a ≠ b) (hκ : κ ≠ 0) (c : ℝ)
    {G : Set (Line m)} {D : Set (CornerCoordinates m)} (hD : MeasurableSet D)
    (hDG : D ⊆ cornerFamily a b G) (hG : IsBounded G) (z : EuclideanSpace ℝ (Fin m)) :
    cornerDensity a b c κ D z ≠ ∞ := by
  have hF : volume (cornerFiber a b c κ D z) ≠ ∞ :=
    (hG.subset (cornerFiber_subset a b c κ hDG z)).measure_lt_top.ne
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (codeJacobian_ne_top m a b))
      (ENNReal.mul_ne_top (parallelMultiplicity_ne_top hG) hF))
    (cornerDensity_le_cornerFiber hab hκ c hD hDG z)

/-- Half the total mass yields half the original density on a positive corner-code fiber. -/
theorem exists_good_corner_code {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    {D₀ D₁ : Set (CornerCoordinates m)} (hD₀ : MeasurableSet D₀) (hD₁ : MeasurableSet D₁)
    (hD : D₁ ⊆ D₀) (hpos : 0 < volume D₀) (hfin : volume D₀ ≠ ∞)
    (hmass : volume D₀ ≤ 2 * volume D₁) :
    ∃ z, 0 < cornerDensity a b c κ D₀ z ∧
      cornerDensity a b c κ D₀ z ≤ 2 * cornerDensity a b c κ D₁ z := by
  apply exists_pos_le_mul_of_lintegral_le (measurable_cornerDensity a b c κ hD₁)
    (measurable_cornerDensity a b c κ hD₀) (cornerDensity_mono a b c κ hD)
  · rwa [lintegral_cornerDensity hab c κ hD₀]
  · rwa [lintegral_cornerDensity hab c κ hD₀]
  · simpa only [lintegral_cornerDensity hab c κ hD₀, lintegral_cornerDensity hab c κ hD₁]
      using hmass

end NKBesicovitch.Projection
