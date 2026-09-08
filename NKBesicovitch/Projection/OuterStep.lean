/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.OuterThreshold
public import NKBesicovitch.Projection.CornerStep

/-!
# The outer corner step with its threshold chosen internally

The inner-code image bound supplies the outer-data budget. Choosing the
half-mass threshold then yields a numerical inequality for the original
corner mass, the code-image bound, and the low parent-pair density.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem corner_mass_bound_of_code_images {a b c κ β C M : ℝ}
    (hab : a ≠ b) (hca : c ≠ a) (hκ : κ ≠ 0)
    (hβ : 1 < β) (hβ2 : β ≤ 2) (hC : 0 < C) (hMpos : 0 < M)
    (Γ : Finset ℝ) (hΓ : Γ.Nonempty)
    (hOld : ∀ F : Set (Line m), MeasurableSet F → IsBounded F → (volume F).toReal ≤
      C * (parallelMultiplicity F).toReal ^ (2 - β) * (sliceSize Γ F).toReal ^ β)
    (hua : ∀ t ∈ Γ, t ≠ a) {G : Set (Line m)} (hGb : IsBounded G)
    (hM : (parallelMultiplicity G).toReal ≤ M) {N R : ℝ≥0∞}
    (hN₀ : N ≠ 0) (hN : N ≠ ∞) (hR₀ : R ≠ 0) (hR : R ≠ ∞)
    (hcN : volume (atHeight c '' G) ≤ N) (huN : ∀ u ∈ Γ, volume (atHeight u '' G) ≤ N)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D)
    (hDG : D ⊆ cornerFamily a b G) (hpos : 0 < volume D)
    {W E : Set (PairCoordinates m)} (hDW : ∀ p ∈ D, cornerParent a p ∈ W)
    (hDE : ∀ p ∈ D, cornerInner b p ∈ E) (Q₀ : ℝ≥0∞) (hQ₀ : Q₀ ≠ ∞)
    (hQ : ∀ p ∈ D, pairDensity a b c W (pairProjections a b c (cornerParent a p)) ≤ Q₀)
    (himage : ∀ u ∈ Γ,
      volume (pairCode b a (cornerInnerCoefficient a c κ u) '' E) ≤ R) :
    ((volume D).toReal / (2 * Γ.card * N.toReal * R.toReal)) ^ β ≤
      (2 * (codeJacobian m a b).toReal ^ 2 * C) *
        (codeJacobian m a b).toReal ^ (β - 1) * M ^ 2 * (N.toReal * Q₀.toReal) ^ (β - 1) := by
  let S (u : ℝ) := (atHeight u '' G) ×ˢ
    (pairCode b a (cornerInnerCoefficient a c κ u) '' E)
  have hS : ∀ u ∈ Γ, cornerOuterData a b c κ u '' D ⊆ S u :=
    fun u _ ↦ cornerOuterData_image_subset_prod a b c κ u hDG hDE
  have hbound : ∀ u ∈ Γ, volume (S u) ≤ N * R := by
    intro u hu
    change volume ((atHeight u '' G) ×ˢ
      (pairCode b a (cornerInnerCoefficient a c κ u) '' E)) ≤ _
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact mul_le_mul (huN u hu) (himage u hu) bot_le bot_le
  have hDfin : volume D ≠ ∞ := ((isBounded_cornerFamily a b hGb).subset hDG).measure_lt_top.ne
  have hτ := cornerThreshold_toReal_pos hpos.ne' hDfin hN₀ hN hR₀ hR hΓ.card_ne_zero
  have h := corner_threshold_le_parent_bound hab hca hκ hβ hβ2 hC hMpos Γ hOld hua hGb hM
    (ENNReal.toReal_mono hN hcN) hD hDG hpos hDW Q₀ hQ₀ hQ
    (cornerThreshold (volume D) N R Γ.card) hτ S hS
    (sum_cornerThreshold_mul_volume_le (volume D) hN₀ hN hR₀ hR Γ hΓ S hbound)
  simpa only [cornerThreshold_toReal] using h

end NKBesicovitch.Projection
