/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PairData

/-!
# Double-projection density of incident pairs

The density uses the intrinsic pair coordinates: the common point and two slopes.
Its integral is exactly the volume of the pair family in those coordinates.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Density of the two projected positions, with the exact inverse Jacobian. -/
noncomputable def pairDensity (a s t : ℝ) (W : Set (PairCoordinates m))
    (yz : Line m) : ℝ≥0∞ :=
  pairJacobian m a s t * ∫⁻ w, W.indicator 1 (pairFromData a s t (w, yz))

theorem measurable_pairDensity (a s t : ℝ) {W : Set (PairCoordinates m)}
    (hW : MeasurableSet W) : Measurable (pairDensity a s t W) := by
  have hf : Measurable (fun p : PairCoordinates m ↦
      W.indicator (1 : PairCoordinates m → ℝ≥0∞) (pairFromData a s t p)) :=
    (measurable_const.indicator hW).comp (continuous_pairFromData a s t).measurable
  exact measurable_const.mul (hf.lintegral_prod_left' (μ := volume))

theorem lintegral_pairDensity {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) :
    (∫⁻ yz, pairDensity a s t W yz) = volume W := by
  let f : PairCoordinates m → ℝ≥0∞ := fun p ↦ W.indicator 1 (pairFromData a s t p)
  have hf : Measurable f :=
    (measurable_const.indicator hW).comp (continuous_pairFromData a s t).measurable
  have hi := (measurePreserving_pairData (m := m) hs ht).lintegral_comp hf
  calc
    (∫⁻ yz, pairDensity a s t W yz) =
        pairJacobian m a s t * ∫⁻ yz, ∫⁻ w, f (w, yz) :=
      lintegral_const_mul _ (hf.lintegral_prod_left' (μ := volume))
    _ = pairJacobian m a s t * ∫⁻ p, f p := by
      congr 1
      simpa only [Measure.volume_eq_prod] using
        (lintegral_prod_symm' (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
          (ν := (volume : Measure (Line m))) f hf).symm
    _ = ∫⁻ p, f p ∂(pairJacobian m a s t • volume) := by
      rw [lintegral_smul_measure, smul_eq_mul]
    _ = ∫⁻ p, W.indicator 1 p := by
      rw [← hi]
      apply lintegral_congr
      intro p
      dsimp [f]
      rw [pairFromData_pairData hs ht]
    _ = volume W := lintegral_indicator_one hW

theorem pairDensity_inter_preimage {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    (W : Set (PairCoordinates m)) (B : Set (Line m)) (yz : Line m) :
    pairDensity a s t (W ∩ pairProjections a s t ⁻¹' B) yz =
      B.indicator (pairDensity a s t W) yz := by
  by_cases hB : yz ∈ B
  · simp only [Set.indicator_of_mem hB, pairDensity]
    congr 1
    apply lintegral_congr
    intro w
    by_cases hw : pairFromData a s t (w, yz) ∈ W
    · have hp : pairFromData a s t (w, yz) ∈ W ∩ pairProjections a s t ⁻¹' B :=
        ⟨hw, by simpa only [Set.mem_preimage, pairProjections_pairFromData hs ht] using hB⟩
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem (fun h ↦ hw h.1), Set.indicator_of_notMem hw]
  · simp only [Set.indicator_of_notMem hB, pairDensity]
    have hz : ∀ w : EuclideanSpace ℝ (Fin m),
        (W ∩ pairProjections a s t ⁻¹' B).indicator
          (1 : PairCoordinates m → ℝ≥0∞) (pairFromData a s t (w, yz)) = 0 := by
      intro w
      simp [Set.indicator, pairProjections_pairFromData hs ht, hB]
    simp [hz]

theorem setLIntegral_pairDensity {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    {B : Set (Line m)} (hB : MeasurableSet B) :
    (∫⁻ yz in B, pairDensity a s t W yz) =
      volume (W ∩ pairProjections a s t ⁻¹' B) := by
  rw [← lintegral_indicator hB]
  simp_rw [← pairDensity_inter_preimage hs ht]
  exact lintegral_pairDensity hs ht
    (hW.inter (hB.preimage (continuous_pairProjections a s t).measurable))

theorem pairDensity_le_projection (a s t : ℝ) {G : Set (Line m)}
    {W : Set (PairCoordinates m)} (hWG : W ⊆ pairFamily a G) (yz : Line m) :
    pairDensity a s t W yz ≤ pairJacobian m a s t * volume (atHeight a '' G) := by
  apply mul_le_mul le_rfl _ bot_le bot_le
  refine (lintegral_mono (fun w ↦ ?_)).trans (lintegral_indicator_one_le (atHeight a '' G))
  by_cases hw : pairFromData a s t (w, yz) ∈ W
  · have hg := (hWG hw).1
    have ha : w ∈ atHeight a '' G := by
      refine ⟨lineAt a w ((s - a)⁻¹ • (yz.1 - w)), hg, ?_⟩
      simp [atHeight_lineAt]
    simp [Set.indicator_of_mem hw, Set.indicator_of_mem ha]
  · simp [Set.indicator_of_notMem hw]

theorem pairProjections_mem_prod (a s t : ℝ) {G : Set (Line m)}
    {W : Set (PairCoordinates m)} (hWG : W ⊆ pairFamily a G)
    {p : PairCoordinates m} (hp : p ∈ W) :
    pairProjections a s t p ∈ (atHeight s '' G) ×ˢ (atHeight t '' G) := by
  rw [pairProjections_eq]
  exact ⟨⟨_, (hWG hp).1, rfl⟩, ⟨_, (hWG hp).2, rfl⟩⟩

theorem support_pairDensity_subset {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hWG : W ⊆ pairFamily a G) :
    Function.support (pairDensity a s t W) ⊆ (atHeight s '' G) ×ˢ (atHeight t '' G) := by
  intro yz hyz
  by_contra h
  have hz (w : EuclideanSpace ℝ (Fin m)) : pairFromData a s t (w, yz) ∉ W := by
    intro hw
    have hp := pairProjections_mem_prod a s t hWG hw
    rw [pairProjections_pairFromData hs ht] at hp
    exact h hp
  exact hyz (by simp [pairDensity, Set.indicator_of_notMem, hz])

end NKBesicovitch.Projection
