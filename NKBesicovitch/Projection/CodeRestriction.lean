/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.FiberSelection

/-!
# Pair-code density under restriction and deletion

Restricting pairs by their code restricts the code density by the same set.
The density of a measurable refinement and its deleted part sum pointwise
to the original density. These identities also apply to infinite masses.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem codeDensity_inter_preimage {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    (W : Set (PairCoordinates m)) (B : Set (EuclideanSpace ℝ (Fin m)))
    (z : EuclideanSpace ℝ (Fin m)) :
    codeDensity a b c (W ∩ pairCode a b c ⁻¹' B) z =
      B.indicator (codeDensity a b c W) z := by
  by_cases hz : z ∈ B
  · rw [Set.indicator_of_mem hz]
    have he : pairFiber a b c (W ∩ pairCode a b c ⁻¹' B) z = pairFiber a b c W z := by
      ext g
      simp only [pairFiber, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
        pairCode_pairFromCode hab, hz, and_true]
    simp only [codeDensity, he]
  · rw [Set.indicator_of_notMem hz]
    have he : pairFiber a b c (W ∩ pairCode a b c ⁻¹' B) z = ∅ := by
      ext g
      simp only [pairFiber, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
        pairCode_pairFromCode hab, hz, and_false, Set.notMem_empty]
    simp only [codeDensity, he, measure_empty, mul_zero]

theorem setLIntegral_codeDensity {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    {B : Set (EuclideanSpace ℝ (Fin m))} (hB : MeasurableSet B) :
    (∫⁻ z in B, codeDensity a b c W z) = volume (W ∩ pairCode a b c ⁻¹' B) := by
  rw [← lintegral_indicator hB]
  simp_rw [← codeDensity_inter_preimage hab c]
  exact lintegral_codeDensity hab c
    (hW.inter (hB.preimage (by unfold pairCode lineAt atHeight; fun_prop)))

theorem codeDensity_add_sdiff (a b c : ℝ) {W E : Set (PairCoordinates m)}
    (hE : MeasurableSet E) (hEW : E ⊆ W) (z : EuclideanSpace ℝ (Fin m)) :
    codeDensity a b c E z + codeDensity a b c (W \ E) z = codeDensity a b c W z := by
  have h := measure_inter_add_sdiff (μ := volume) (pairFiber a b c W z)
    (measurableSet_pairFiber a b c hE z)
  rw [inter_eq_right.mpr (pairFiber_mono a b c hEW z)] at h
  change codeJacobian m a b * volume (pairFiber a b c E z) +
    codeJacobian m a b * volume (pairFiber a b c W z \ pairFiber a b c E z) = _
  rw [← mul_add, h]
  rfl

end NKBesicovitch.Projection
