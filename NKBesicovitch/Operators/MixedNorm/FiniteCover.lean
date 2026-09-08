/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Norm estimates from a finite cover

For finite exponents at least one, a global norm is bounded by the sum
of the norms on a finite cover. Neither the function nor the covering
sets need be measurable: subadditivity of the restricted measures and
of the power `1 / p` suffices. This applies to direction caps even before
joint measurability of the geometric X-ray norm is established.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

theorem eLpNorm_restrict_union_le (f : X → ℝ≥0∞) (A B : Set X)
    (hp : 1 ≤ p) (hpfin : p ≠ ∞) :
    eLpNorm f p (μ.restrict (A ∪ B)) ≤
      eLpNorm f p (μ.restrict A) + eLpNorm f p (μ.restrict B) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hreal : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_le_toReal (by simp) hpfin).mpr hp
  have hinv : 0 ≤ 1 / p.toReal := one_div_nonneg.mpr (by positivity)
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpfin, enorm_eq_self]
  exact (ENNReal.rpow_le_rpow (lintegral_union_le (fun x ↦ f x ^ p.toReal) A B) hinv).trans
    (ENNReal.rpow_add_le_add_rpow _ _ hinv (by simpa using inv_le_one_of_one_le₀ hreal))

/-- Local norms on any finite cover control the global norm. -/
theorem eLpNorm_le_sum_restrict (f : X → ℝ≥0∞) (s : Finset ι) (A : ι → Set X)
    (hcover : ∀ x, ∃ i ∈ s, x ∈ A i) (hp : 1 ≤ p) (hpfin : p ≠ ∞) :
    eLpNorm f p μ ≤ ∑ i ∈ s, eLpNorm f p (μ.restrict (A i)) := by
  classical
  have hbound : ∀ t : Finset ι, eLpNorm f p (μ.restrict (⋃ i ∈ t, A i)) ≤
      ∑ i ∈ t, eLpNorm f p (μ.restrict (A i)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      simp only [Finset.set_biUnion_insert, Finset.sum_insert hi]
      exact (eLpNorm_restrict_union_le f _ _ hp hpfin).trans (add_le_add le_rfl ih)
  have heq : (⋃ i ∈ s, A i) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hi, hx⟩ := hcover x
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hx⟩⟩
  simpa only [heq, Measure.restrict_univ] using hbound s

end NKBesicovitch
