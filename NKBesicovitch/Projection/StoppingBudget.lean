/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.ChildRefinement
public import NKBesicovitch.Projection.StoppingParameters
public import Mathlib.Tactic.Finiteness

/-!
# The stopping parameters meet the child deletion budget

Use the level-dependent density and image bounds in the three-stage child
refinement. The gap in loss exponents makes the total deletion at most half
the low-density parent mass. The original pair mass is explicitly finite.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι κ : Type*}

theorem child_pruning_budget_ennreal {N : ℝ} (hN : 1 ≤ N)
    {V : ℝ≥0∞} (hV : V ≠ ∞) (r k : ℕ) {J i : ℕ} (hJ : 0 < J) (hi : i < J)
    (hlarge : 4 * (1 + 2 * (k : ℝ)) * r ≤ N ^ (1 / (J : ℝ) ^ 2)) :
    (1 + 2 * k) * (r * (V * ENNReal.ofReal (N ^ (-stoppingAlpha J (i + 1)))) +
      r * (V * ENNReal.ofReal (N ^ (-2 + stoppingRho J i - 200 / J))) *
        ENNReal.ofReal (N ^ (2 - stoppingRho J (i + 1)))) ≤
      (V * ENNReal.ofReal (N ^ (-stoppingAlpha J i))) / 2 := by
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)]
  have he : (r : ℝ) * (V.toReal * N ^ (-2 + stoppingRho J i - 200 / J)) *
      N ^ (2 - stoppingRho J (i + 1)) = (r : ℝ) * (V.toReal * N ^ (-100 / (J : ℝ))) := by
    rw [mul_assoc, inner_threshold_mul_image hNpos]
  rw [he]
  exact child_pruning_budget hN ENNReal.toReal_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg k)
    hJ hi hlarge

/-- The concrete stopping parameters produce child families losing at most half the parent quota. -/
theorem exists_refined_child_pairs_half_parent {a b N : ℝ} (hab : a ≠ b) (hN : 1 ≤ N)
    (s t : ι → ℝ) (I : Finset ι) (c : κ → ℝ) (K : Finset κ)
    (hs : ∀ i ∈ I, s i ≠ a) (ht : ∀ i ∈ I, t i ≠ a)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) {V : ℝ≥0∞} (hV : V ≠ ∞)
    {J i : ℕ} (hJ : 0 < J) (hi : i < J)
    (hlarge : 4 * (1 + 2 * (K.card : ℝ)) * I.card ≤ N ^ (1 / (J : ℝ) ^ 2))
    (hchild : ∀ j ∈ I, ∃ E : Set (PairCoordinates m), MeasurableSet E ∧ E ⊆ W ∧
      volume (W \ E) ≤ V * ENNReal.ofReal (N ^ (-stoppingAlpha J (i + 1))) ∧
      volume (pairProjections a (s j) (t j) '' E) ≤
        ENNReal.ofReal (N ^ (2 - stoppingRho J (i + 1)))) :
    let ℓ := V * ENNReal.ofReal (N ^ (-2 + stoppingRho J i - 200 / J))
    ∃ E₁ E₂ E₃ : Set (PairCoordinates m),
      MeasurableSet E₁ ∧ MeasurableSet E₂ ∧ MeasurableSet E₃ ∧
      E₁ ⊆ W ∧ E₂ ⊆ E₁ ∧ E₃ ⊆ E₂ ∧
      volume (W \ E₃) ≤ (V * ENNReal.ofReal (N ^ (-stoppingAlpha J i))) / 2 ∧
      (∀ j ∈ I, ∀ p ∈ E₂, ℓ ≤ pairDensity a (s j) (t j) E₁
        (pairProjections a (s j) (t j) p)) ∧
      ∀ k ∈ K, ∀ p ∈ E₃, 0 < codeDensity a b (c k) W (pairCode a b (c k) p) ∧
        codeDensity a b (c k) W (pairCode a b (c k) p) ≤
          2 * codeDensity a b (c k) E₂ (pairCode a b (c k) p) := by
  obtain ⟨E₁, E₂, E₃, hE₁, hE₂, hE₃, hE₁W, hE₂E₁, hE₃E₂, hloss, hdense, hretain⟩ :=
    exists_refined_child_pairs hab s t I c K hs ht hW
      (V * ENNReal.ofReal (N ^ (-stoppingAlpha J (i + 1))))
      (ENNReal.ofReal (N ^ (2 - stoppingRho J (i + 1))))
      (V * ENNReal.ofReal (N ^ (-2 + stoppingRho J i - 200 / J))) hchild
  exact ⟨E₁, E₂, E₃, hE₁, hE₂, hE₃, hE₁W, hE₂E₁, hE₃E₂,
    hloss.trans (child_pruning_budget_ennreal hN hV I.card K.card hJ hi hlarge), hdense, hretain⟩

end NKBesicovitch.Projection
