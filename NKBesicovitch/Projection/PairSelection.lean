/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.FiberProjection
public import NKBesicovitch.Projection.FiberSelection
public import NKBesicovitch.Projection.SimultaneousRefinement

/-!
# A common code fiber with simultaneous projection bounds

A deletion budget of half the original pair mass gives one positive code
fiber whose density is retained and whose first-line projections satisfy all
selected bounds. This is the selection step in the basic pair improvement.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι : Type*}

theorem exists_densePair_code {a b c : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (t : ι → ℝ) (I : Finset ι) (hta : ∀ i ∈ I, t i ≠ a) (htb : ∀ i ∈ I, t i ≠ b)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (hWG : W ⊆ pairFamily a G) (hpos : 0 < volume W) (hfin : volume W ≠ ∞)
    (ℓ N : ℝ≥0∞) (htN : ∀ i ∈ I, volume (atHeight (t i) '' G) ≤ N)
    (hdN : ∀ i ∈ I, volume (atHeight (dualTime a b c (t i)) '' G) ≤ N)
    (hbudget : I.card * ℓ * N ^ 2 ≤ volume W / 2) :
    let W' := densePairs a t (fun i ↦ dualTime a b c (t i)) I W ℓ
    ∃ z, 0 < codeDensity a b c W z ∧ codeDensity a b c W z ≤ 2 * codeDensity a b c W' z ∧
      ∀ i ∈ I, (ENNReal.ofReal |(((b - a) / (dualTime a b c (t i) - a)) ^ m)⁻¹| * ℓ) *
        volume (atHeight (t i) '' pairFiber a b c W' z) ≤ codeDensity a b c W z := by
  let W' := densePairs a t (fun i ↦ dualTime a b c (t i)) I W ℓ
  have hW' : MeasurableSet W' := measurableSet_densePairs _ _ _ _ hW ℓ
  have hsub : W' ⊆ W := densePairs_subset _ _ _ _ W ℓ
  have hhalf : volume W / 2 ≤ volume W' :=
    half_volume_le_volume_densePairs a t (fun i ↦ dualTime a b c (t i)) I hta
      (fun i hi ↦ dualTime_ne_base hab hc (hta i hi) (htb i hi)) hW hWG hfin ℓ N htN hdN hbudget
  have hmass : volume W ≤ 2 * volume W' := by
    calc
      _ = volume W / 2 + volume W / 2 := (ENNReal.add_halves _).symm
      _ ≤ volume W' + volume W' := add_le_add hhalf hhalf
      _ = _ := (two_mul _).symm
  obtain ⟨z, hz, hratio⟩ := exists_good_code hab c hW hW' hsub hpos hfin hmass
  refine ⟨z, hz, hratio, fun i hi ↦ ?_⟩
  have hℓ : ∀ p ∈ W', ℓ ≤ pairDensity a (t i) (dualTime a b c (t i)) W
      (pairProjections a (t i) (dualTime a b c (t i)) p) := by
    intro p hp
    exact le_pairDensity_of_mem_densePairs (s := t) (t := fun j ↦ dualTime a b c (t j)) hp hi
  exact mul_volume_projection_pairFiber_le (W₁ := W') hab hc (hta i hi) (htb i hi) hW ℓ hℓ z

end NKBesicovitch.Projection
