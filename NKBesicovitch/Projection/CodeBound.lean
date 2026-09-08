/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CodeSlices
public import NKBesicovitch.Projection.Parallel
public import NKBesicovitch.Projection.BoundedFamilies

/-!
# Bounding code density by parallel multiplicity

The exceptional slopes in the essential supremum remain negligible under the
invertible affine map from first-line position to second-line slope. Thus the
bound holds at every code value, without replacing the essential supremum by
a pointwise supremum.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem quasiMeasurePreserving_codeSlope {a b c : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (z : Space m) :
    Measure.QuasiMeasurePreserving (fun y : Space m ↦ (b - a)⁻¹ • (z - c • y)) volume volume := by
  have h₁ := Measure.quasiMeasurePreserving_smul (volume : Measure (Space m))
    (neg_ne_zero.mpr hc)
  have h₂ := quasiMeasurePreserving_add_left (volume : Measure (Space m)) z
  have h₃ := Measure.quasiMeasurePreserving_smul (volume : Measure (Space m))
    (inv_ne_zero (sub_ne_zero.mpr hab.symm))
  simpa [Function.comp_def, sub_eq_add_neg, neg_smul] using h₃.comp (h₂.comp h₁)

theorem codeSliceMass_ae_le_parallelMultiplicity {a b c : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hWG : W ⊆ pairFamily a G)
    (z : Space m) : ∀ᵐ y, codeSliceMass a b c W z y ≤ parallelMultiplicity G := by
  have h := (quasiMeasurePreserving_codeSlope hab hc z).ae
    (ENNReal.ae_le_essSup (μ := (volume : Measure (Space m)))
      (fun ξ : Space m ↦ volume {x : Space m | (x, ξ) ∈ G}))
  exact h.mono fun y hy ↦ (codeSliceMass_le_parallelFiber hab c hWG z y).trans hy

theorem lintegral_le_mul_measure_of_ae_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ≥0∞} {S : Set X} (hS : Function.support f ⊆ S) {C : ℝ≥0∞}
    (hC : ∀ᵐ x ∂μ, f x ≤ C) : (∫⁻ x, f x ∂μ) ≤ C * μ S := by
  rw [← setLIntegral_eq_of_support_subset hS]
  exact (lintegral_mono_ae (ae_restrict_of_ae hC)).trans_eq (setLIntegral_const S C)

/-- The exact constant in the code-density upper bound from the basic pair argument. -/
theorem codeDensity_le_parallelMultiplicity {a b c : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (hWG : W ⊆ pairFamily a G) (z : Space m) :
    codeDensity a b c W z ≤ codeJacobian m a b ^ 2 *
      (parallelMultiplicity G * volume (atHeight b '' G)) := by
  rw [codeDensity_eq_lintegral_codeSliceMass hab c hW]
  exact mul_le_mul le_rfl (lintegral_le_mul_measure_of_ae_le
    (support_codeSliceMass_subset hab c hWG z)
    (codeSliceMass_ae_le_parallelMultiplicity hab hc hWG z)) bot_le bot_le

theorem codeDensity_ne_top {a b c : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (hWG : W ⊆ pairFamily a G) (hG : Bornology.IsBounded G) (z : Space m) :
    codeDensity a b c W z ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (codeDensity_le_parallelMultiplicity hab hc hW hWG z)
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (codeJacobian_ne_top m a b))
    (ENNReal.mul_ne_top (parallelMultiplicity_ne_top hG) (volume_projection_ne_top b hG))

end NKBesicovitch.Projection
