/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerPattern
public import NKBesicovitch.Projection.PairParameters
public import Mathlib.Tactic.Linarith

/-!
# Uniform constants for a fixed corner pattern

Finitely many input estimates share a positive constant. The finitely many
inner-code projection Jacobians share a positive lower bound. Both constants
are chosen before the line family is supplied.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerPattern

variable {m : ℕ} {β : ℝ}

theorem exists_input_constant (P : CornerPattern m β) :
    ∃ C : ℝ, 0 < C ∧
      (∀ G : Set (Line m), MeasurableSet G → IsBounded G → (volume G).toReal ≤
        C * (parallelMultiplicity G).toReal ^ (2 - β) * (sliceSize P.outer G).toReal ^ β) ∧
      ∀ u ∈ P.outer, ∀ G : Set (Line m), MeasurableSet G → IsBounded G → (volume G).toReal ≤
        C * (parallelMultiplicity G).toReal ^ (2 - β) * (sliceSize (P.inner u) G).toReal ^ β := by
  classical
  obtain ⟨C₀, hC₀, hOuter⟩ := P.outer_estimate
  let Cᵢ (u : P.outer) : ℝ := Classical.choose (P.inner_estimate u u.property)
  have hInner (u : P.outer) := Classical.choose_spec (P.inner_estimate u u.property)
  let C := 1 + C₀ + ∑ u : P.outer, Cᵢ u
  have hsum : 0 ≤ ∑ u : P.outer, Cᵢ u := Finset.sum_nonneg fun u _ ↦ (hInner u).1.le
  have hC : 0 < C := by dsimp only [C]; linarith
  have hC₀C : C₀ ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, fun G hG hGb ↦ ?_, fun u hu G hG hGb ↦ ?_⟩
  · exact (hOuter G hG hGb).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₀C (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      (Real.rpow_nonneg ENNReal.toReal_nonneg _))
  · have hCi : Cᵢ ⟨u, hu⟩ ≤ ∑ v : P.outer, Cᵢ v :=
      Finset.single_le_sum (fun v _ ↦ (hInner v).1.le) (Finset.mem_univ (⟨u, hu⟩ : P.outer))
    have hCiC : Cᵢ ⟨u, hu⟩ ≤ C := by dsimp only [C]; linarith
    exact ((hInner ⟨u, hu⟩).2 G hG hGb).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCiC (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      (Real.rpow_nonneg ENNReal.toReal_nonneg _))

theorem exists_innerJacobian_lower_bound (P : CornerPattern m β) :
    ∃ q : ℝ, 0 < q ∧ ∀ u ∈ P.outer, ∀ t ∈ P.inner u, q ≤
      (ENNReal.ofReal |(((P.a - P.b) /
        (dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) t - P.b)) ^ m)⁻¹|).toReal := by
  let f : ℝ × ℝ → ℝ := fun p ↦ (ENNReal.ofReal |(((P.a - P.b) /
    (dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ p.1) p.2 - P.b)) ^ m)⁻¹|).toReal
  refine ⟨P.children.inf' P.children_nonempty f, ?_, fun u hu t ht ↦
    Finset.inf'_le f (mem_children.mpr ⟨hu, ht⟩)⟩
  apply (Finset.lt_inf'_iff P.children_nonempty).mpr
  intro p hp
  have hdual := sub_ne_zero.mpr (P.child_dual_ne_base hp)
  dsimp only [f]
  rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  exact abs_pos.mpr (inv_ne_zero (pow_ne_zero _ (div_ne_zero
    (sub_ne_zero.mpr P.a_ne_b) hdual)))

end NKBesicovitch.Projection.CornerPattern
