/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PairDensity

/-!
# Removing pairs with low projection density

The lost intrinsic volume is bounded by the threshold times the product of
the two projection sizes. These sizes are outer measures; the projection
images need not be Borel.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem setLIntegral_lt_le_mul_measure {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ≥0∞} (hf : Measurable f) {S : Set X}
    (hS : Function.support f ⊆ S) (ℓ : ℝ≥0∞) :
    (∫⁻ x in {x | f x < ℓ}, f x ∂μ) ≤ ℓ * μ S := by
  rw [← lintegral_indicator (measurableSet_lt hf measurable_const)]
  refine (lintegral_mono (fun x ↦ ?_)).trans (lintegral_indicator_const_le S ℓ)
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    by_cases hlt : f x < ℓ
    · rw [Set.indicator_of_mem (show x ∈ {x | f x < ℓ} from hlt)]
      exact hlt.le
    · rw [Set.indicator_of_notMem (show x ∉ {x | f x < ℓ} from hlt)]
      exact bot_le
  · have hz : f x = 0 := by
      by_contra h
      exact hx (hS h)
    simp [Set.indicator, hx, hz]

theorem volume_low_pairDensity_le {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (hWG : W ⊆ pairFamily a G) (ℓ : ℝ≥0∞) :
    volume (W ∩ {p | pairDensity a s t W (pairProjections a s t p) < ℓ}) ≤
      ℓ * (volume (atHeight s '' G) * volume (atHeight t '' G)) := by
  change volume (W ∩ pairProjections a s t ⁻¹' {yz | pairDensity a s t W yz < ℓ}) ≤ _
  rw [← setLIntegral_pairDensity hs ht hW
    (measurableSet_lt (measurable_pairDensity a s t hW) measurable_const)]
  calc
    _ ≤ ℓ * volume ((atHeight s '' G) ×ˢ (atHeight t '' G)) :=
      setLIntegral_lt_le_mul_measure (measurable_pairDensity a s t hW)
        (support_pairDensity_subset hs ht hWG) ℓ
    _ = _ := by rw [Measure.volume_eq_prod, Measure.prod_prod]

end NKBesicovitch.Projection
