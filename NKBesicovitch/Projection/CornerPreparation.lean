/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerCounting
public import Mathlib.Tactic.Finiteness

/-!
# Lifting the selected parent and refined children to positive corner mass

Balanced companion fibers turn the parent mass quota into a corner mass
quota. A child deletion of at most half the parent quota preserves at least
half that corner mass. The resulting Borel family retains both restrictions.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem exists_corners_of_parent_and_child (a b : ℝ) {G₀ A B G : Set (Line m)}
    (hG₀ : MeasurableSet G₀) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hG₀G : G₀ ⊆ G) (hAG : A ⊆ G) (hBG : B ⊆ G)
    {U E : Set (PairCoordinates m)} (hU : MeasurableSet U) (hE : MeasurableSet E)
    (hUP : U ⊆ companionPairs a G₀ A) (hUfin : volume U ≠ ∞)
    {η δ : ℝ≥0∞} (hη : 0 < η) (hηfin : η ≠ ∞) (hδ : 0 < δ)
    (hηₐ : ∀ g ∈ G₀, sliceMultiplicity a A (atHeight a g) = η)
    (hηᵦ : ∀ g ∈ G₀, sliceMultiplicity b B (atHeight b g) = η)
    (hparent : δ ≤ volume U) (hchild : volume (companionPairs b G₀ B \ E) ≤ δ / 2) :
    ∃ D : Set (CornerCoordinates m), MeasurableSet D ∧ D ⊆ cornerFamily a b G ∧
      0 < volume D ∧ (δ * η) / 2 ≤ volume D ∧
      ∀ p ∈ D, cornerParent a p ∈ U ∧ cornerInner b p ∈ E := by
  let D := parentCorners a b U B ∩ cornerInner b ⁻¹' E
  have hD : MeasurableSet D := (measurableSet_parentCorners a b hU hB).inter
    (hE.preimage (by unfold cornerInner atHeight; fun_prop))
  have hDC : D ⊆ companionCorners a b G₀ A B := by
    intro p hp
    have h := hp.1
    rw [parentCorners_eq_inter hUP] at h
    exact h.1
  have hquota : (δ * η) / 2 ≤ (volume U * η) / 2 := by
    simp only [div_eq_mul_inv]
    exact mul_le_mul (mul_le_mul hparent le_rfl bot_le bot_le) le_rfl bot_le bot_le
  have hbudget : volume (companionPairs b G₀ B \ E) * η ≤ (volume U * η) / 2 := by
    calc
      _ ≤ (δ / 2) * η := mul_le_mul hchild le_rfl bot_le bot_le
      _ = (δ * η) / 2 := by simp only [div_eq_mul_inv]; ac_rfl
      _ ≤ _ := hquota
  have hmass := hquota.trans (half_parent_mass_le_retained_corner_mass a b hG₀ hA hB
    hU hUP hE η η hηₐ hηᵦ (by finiteness) hbudget)
  have hquotaPos : 0 < (δ * η) / 2 :=
    ENNReal.div_pos (mul_ne_zero hδ.ne' hη.ne') ENNReal.ofNat_ne_top
  exact ⟨D, hD, hDC.trans (companionCorners_subset_cornerFamily a b hG₀G hAG hBG),
    hquotaPos.trans_le hmass, hmass, fun _ hp ↦ ⟨hp.1.1, hp.2⟩⟩

end NKBesicovitch.Projection
