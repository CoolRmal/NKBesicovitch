/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CodePruning

/-!
# Retaining comparable densities for finitely many pair codes

For each selected code, remove zero original density and fibers on which
the refinement has less than half the original density. The total loss is
at most `1 + 2 |I|` times the original pair deletion.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι : Type*}

/-- Pairs whose selected codes all retain a positive, comparable density. -/
noncomputable def retainedCodePairs (a b : ℝ) (c : ι → ℝ) (I : Finset ι)
    (W E : Set (PairCoordinates m)) : Set (PairCoordinates m) :=
  E ∩ ⋂ i ∈ I, {p | 0 < codeDensity a b (c i) W (pairCode a b (c i) p) ∧
    codeDensity a b (c i) W (pairCode a b (c i) p) / 2 ≤
      codeDensity a b (c i) E (pairCode a b (c i) p)}

theorem retainedCodePairs_subset (a b : ℝ) (c : ι → ℝ) (I : Finset ι)
    (W E : Set (PairCoordinates m)) : retainedCodePairs a b c I W E ⊆ E := inter_subset_left

theorem codeDensity_bounds_of_mem_retainedCodePairs {a b : ℝ} {c : ι → ℝ} {I : Finset ι}
    {W E : Set (PairCoordinates m)} {p : PairCoordinates m}
    (hp : p ∈ retainedCodePairs a b c I W E) {i : ι} (hi : i ∈ I) :
    0 < codeDensity a b (c i) W (pairCode a b (c i) p) ∧
      codeDensity a b (c i) W (pairCode a b (c i) p) ≤
        2 * codeDensity a b (c i) E (pairCode a b (c i) p) := by
  have h := mem_iInter.mp (mem_iInter.mp hp.2 i) hi
  refine ⟨h.1, ?_⟩
  calc
    _ = codeDensity a b (c i) W (pairCode a b (c i) p) / 2 +
        codeDensity a b (c i) W (pairCode a b (c i) p) / 2 := (ENNReal.add_halves _).symm
    _ ≤ codeDensity a b (c i) E (pairCode a b (c i) p) +
        codeDensity a b (c i) E (pairCode a b (c i) p) := add_le_add h.2 h.2
    _ = _ := (two_mul _).symm

theorem measurableSet_retainedCodePairs (a b : ℝ) (c : ι → ℝ) (I : Finset ι)
    {W E : Set (PairCoordinates m)} (hW : MeasurableSet W) (hE : MeasurableSet E) :
    MeasurableSet (retainedCodePairs a b c I W E) := by
  apply hE.inter (I.measurableSet_biInter fun i _ ↦ ?_)
  have hcode : Measurable (pairCode (m := m) a b (c i)) := by
    unfold pairCode lineAt atHeight
    fun_prop
  have hDW := (measurable_codeDensity a b (c i) hW).comp hcode
  have hDE := (measurable_codeDensity a b (c i) hE).comp hcode
  exact (measurableSet_lt measurable_const hDW).inter
    (measurableSet_le (hDW.div_const 2) hDE)

theorem sdiff_retainedCodePairs_subset (a b : ℝ) (c : ι → ℝ) (I : Finset ι)
    (W E : Set (PairCoordinates m)) :
    W \ retainedCodePairs a b c I W E ⊆ (W \ E) ∪
      ⋃ i ∈ I, W ∩ {p | codeDensity a b (c i) W (pairCode a b (c i) p) = 0 ∨
        codeDensity a b (c i) E (pairCode a b (c i) p) <
          codeDensity a b (c i) W (pairCode a b (c i) p) / 2} := by
  intro p hp
  by_cases hpE : p ∈ E
  · right
    by_contra h
    apply hp.2
    refine ⟨hpE, mem_iInter.mpr fun i ↦ mem_iInter.mpr fun hi ↦ ?_⟩
    constructor
    · exact pos_iff_ne_zero.mpr fun hz ↦
        h (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hp.1, Or.inl hz⟩⟩)
    · exact le_of_not_gt fun hlt ↦
        h (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hp.1, Or.inr hlt⟩⟩)
  · exact Or.inl ⟨hp.1, hpE⟩

theorem volume_sdiff_retainedCodePairs_le {a b : ℝ} (hab : a ≠ b)
    (c : ι → ℝ) (I : Finset ι) {W E : Set (PairCoordinates m)}
    (hW : MeasurableSet W) (hE : MeasurableSet E) (hEW : E ⊆ W) :
    volume (W \ retainedCodePairs a b c I W E) ≤ (1 + 2 * I.card) * volume (W \ E) := by
  calc
    _ ≤ volume ((W \ E) ∪ ⋃ i ∈ I, W ∩
        {p | codeDensity a b (c i) W (pairCode a b (c i) p) = 0 ∨
          codeDensity a b (c i) E (pairCode a b (c i) p) <
            codeDensity a b (c i) W (pairCode a b (c i) p) / 2}) :=
      measure_mono (sdiff_retainedCodePairs_subset a b c I W E)
    _ ≤ volume (W \ E) + ∑ i ∈ I, volume (W ∩
        {p | codeDensity a b (c i) W (pairCode a b (c i) p) = 0 ∨
          codeDensity a b (c i) E (pairCode a b (c i) p) <
            codeDensity a b (c i) W (pairCode a b (c i) p) / 2}) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le I _))
    _ ≤ volume (W \ E) + ∑ _i ∈ I, 2 * volume (W \ E) :=
      add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦
        volume_bad_codeDensity_le hab (c i) hW hE hEW)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, add_mul, mul_comm, mul_assoc]

end NKBesicovitch.Projection
