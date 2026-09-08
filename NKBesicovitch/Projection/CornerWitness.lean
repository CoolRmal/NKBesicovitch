/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerSelection
public import NKBesicovitch.Projection.CornerParentBound

/-!
# Finite numerical data for a corner improvement

Combine simultaneous outer refinement with both corner-density upper bounds.
The selected first-line family is Borel. Boundedness and the finite parent
density threshold justify every passage from extended measures to real numbers.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι : Type*}

theorem exists_corner_witness {a b c κ : ℝ} (hab : a ≠ b) (hca : c ≠ a) (hκ : κ ≠ 0)
    (u : ι → ℝ) (I : Finset ι) (hua : ∀ i ∈ I, u i ≠ a)
    {G : Set (Line m)} (hGb : IsBounded G) {D : Set (CornerCoordinates m)}
    (hD : MeasurableSet D) (hDG : D ⊆ cornerFamily a b G) (hpos : 0 < volume D)
    {W : Set (PairCoordinates m)} (hDW : ∀ p ∈ D, cornerParent a p ∈ W)
    (Q₀ : ℝ≥0∞) (hQ₀ : Q₀ ≠ ∞)
    (hQ : ∀ p ∈ D, pairDensity a b c W (pairProjections a b c (cornerParent a p)) ≤ Q₀)
    (τ : ℝ≥0∞) (S : ι → Set (Line m))
    (hS : ∀ i ∈ I, cornerOuterData a b c κ (u i) '' D ⊆ S i)
    (hbudget : ∑ i ∈ I, τ * volume (S i) ≤ volume D / 2) :
    ∃ (F : Set (Line m)) (H : ℝ), MeasurableSet F ∧ F ⊆ G ∧ 0 < H ∧
      H ≤ 2 * (codeJacobian m a b).toReal ^ 2 *
        ((parallelMultiplicity G).toReal * (volume F).toReal) ∧
      H ≤ (codeJacobian m a b).toReal *
        ((parallelMultiplicity G).toReal * (volume (atHeight c '' G)).toReal * Q₀.toReal) ∧
      ∀ i ∈ I, τ.toReal * (volume (atHeight (u i) '' F)).toReal ≤ H := by
  let D' := denseCorners a b c κ u I D τ
  have hD' : MeasurableSet D' := measurableSet_denseCorners a b c κ u I hD τ
  have hsub : D' ⊆ D := denseCorners_subset a b c κ u I D τ
  have hDfin : volume D ≠ ∞ :=
    ((isBounded_cornerFamily a b hGb).subset hDG).measure_lt_top.ne
  obtain ⟨z, hz, hratio, hproj⟩ :=
    exists_denseCorner_code hab c κ u I hua hD hpos hDfin τ S hS hbudget
  let F := positiveCornerFiber a b c κ D' z
  have hF : MeasurableSet F := measurableSet_positiveCornerFiber a b c κ hD' z
  have hFG : F ⊆ G := (positiveCornerFiber_subset a b c κ D' z).trans
    (cornerFiber_subset a b c κ (hsub.trans hDG) z)
  have hHfin := cornerDensity_ne_top hab hκ c hD hDG hGb z
  have hMfin := parallelMultiplicity_ne_top hGb
  have hqfin := codeJacobian_ne_top m a b
  refine ⟨F, (cornerDensity a b c κ D z).toReal, hF, hFG,
    ENNReal.toReal_pos hz.ne' hHfin, ?_, ?_, fun i hi ↦ ?_⟩
  · have hu := hratio.trans (mul_le_mul le_rfl
      (cornerDensity_le_positiveCornerFiber hab hκ c hD' (hsub.trans hDG) z) bot_le bot_le)
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top hqfin) (ENNReal.mul_ne_top hMfin
          (hGb.subset hFG).measure_lt_top.ne))) hu
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, mul_assoc] using h
  · have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hqfin (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hMfin (isBounded_projection c hGb).measure_lt_top.ne) hQ₀))
      (cornerDensity_le_parentDensity_bound hab hca hκ hD hDG hDW Q₀ hQ z)
    simpa only [ENNReal.toReal_mul] using h
  · have hp := (mul_le_mul le_rfl (measure_mono
      (Set.image_mono (positiveCornerFiber_subset a b c κ D' z))) bot_le bot_le).trans
        (hproj i hi)
    simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono hHfin hp

end NKBesicovitch.Projection
