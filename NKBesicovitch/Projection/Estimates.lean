/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.BoundedFamilies
public import NKBesicovitch.Projection.TwoSlice
public import NKBesicovitch.Projection.PairCode
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Projection estimates and their selected heights

The estimate is uniform over bounded Borel line families, as in the supplied
manuscript. All masses in the real-valued inequality are finite by
`BoundedFamilies`; converting them to real numbers does not discard infinite mass.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- A uniform projection estimate at exponent `β` on a finite set of heights. -/
def HasProjectionEstimate (m : ℕ) (β : ℝ) (Γ : Finset ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
    (volume G).toReal ≤ C * (parallelMultiplicity G).toReal ^ (2 - β) * (sliceSize Γ G).toReal ^ β

/-- The heights needed for a pair improvement, including both base heights. -/
noncomputable def pairTimes (a b c : ℝ) (Γ : Finset ℝ) : Finset ℝ :=
  insert a (insert b (Γ ∪ Γ.image (dualTime a b c)))

theorem volume_projection_le_sliceSize {Γ : Finset ℝ} {t : ℝ} (ht : t ∈ Γ)
    (G : Set (Line m)) : volume (atHeight t '' G) ≤ sliceSize Γ G :=
  le_iSup_of_le t (le_iSup_of_le ht le_rfl)

theorem projection_toReal_le_sliceSize {Γ : Finset ℝ} {t : ℝ} (ht : t ∈ Γ)
    {G : Set (Line m)} (hG : IsBounded G) :
    (volume (atHeight t '' G)).toReal ≤ (sliceSize Γ G).toReal :=
  ENNReal.toReal_mono (sliceSize_ne_top Γ hG) (volume_projection_le_sliceSize ht G)

theorem sliceSize_mono {Γ Δ : Finset ℝ} (hΓ : Γ ⊆ Δ) {F G : Set (Line m)} (hF : F ⊆ G) :
    sliceSize Γ F ≤ sliceSize Δ G := by
  refine iSup_le fun t ↦ iSup_le fun ht ↦ ?_
  exact (measure_mono (image_mono hF)).trans (volume_projection_le_sliceSize (hΓ ht) G)

theorem sliceSize_toReal_le {Γ : Finset ℝ} {G : Set (Line m)} (hG : IsBounded G)
    {C : ℝ} (hC : 0 ≤ C) (hΓ : ∀ t ∈ Γ, (volume (atHeight t '' G)).toReal ≤ C) :
    (sliceSize Γ G).toReal ≤ C := by
  have h : sliceSize Γ G ≤ ENNReal.ofReal C := by
    refine iSup_le fun t ↦ iSup_le fun ht ↦ ?_
    rw [← ENNReal.ofReal_toReal (volume_projection_ne_top t hG)]
    exact ENNReal.ofReal_le_ofReal (hΓ t ht)
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

theorem mem_pairTimes_base_left (a b c : ℝ) (Γ : Finset ℝ) : a ∈ pairTimes a b c Γ := by
  simp [pairTimes]

theorem mem_pairTimes_base_right (a b c : ℝ) (Γ : Finset ℝ) : b ∈ pairTimes a b c Γ := by
  simp [pairTimes]

theorem subset_pairTimes (a b c : ℝ) (Γ : Finset ℝ) : Γ ⊆ pairTimes a b c Γ := by
  intro t ht
  simp [pairTimes, ht]

theorem dualTime_mem_pairTimes (a b c : ℝ) {Γ : Finset ℝ} {t : ℝ} (ht : t ∈ Γ) :
    dualTime a b c t ∈ pairTimes a b c Γ := by
  simp [pairTimes, Finset.mem_image_of_mem _ ht]

/-- The exact two-slice seed gives the exponent-two projection estimate. -/
theorem hasProjectionEstimate_twoSlice {s t : ℝ} (hst : s ≠ t) :
    HasProjectionEstimate m 2 {s, t} := by
  refine ⟨|((t - s) ^ m)⁻¹|, abs_pos.mpr (inv_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hst.symm))),
    fun G _ hG ↦ ?_⟩
  have hf : ENNReal.ofReal |((t - s) ^ m)⁻¹| *
      (volume (atHeight s '' G) * volume (atHeight t '' G)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (volume_projection_ne_top s hG) (volume_projection_ne_top t hG))
  have h := ENNReal.toReal_mono hf (volume_le_two_slice hst G)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at h
  have hs := projection_toReal_le_sliceSize (show s ∈ ({s, t} : Finset ℝ) by simp) hG
  have ht := projection_toReal_le_sliceSize (show t ∈ ({s, t} : Finset ℝ) by simp) hG
  have hp := mul_le_mul hs ht ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  simpa only [sub_self, Real.rpow_zero, mul_one, Real.rpow_two, pow_two, mul_assoc] using
    h.trans (mul_le_mul_of_nonneg_left hp (abs_nonneg _))

end NKBesicovitch.Projection
