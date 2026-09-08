/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.ControlPolynomial
public import NKBesicovitch.Projection.Selection.TreeControl

/-!
# Polynomial stopping constants uniform over selected trees

Fix the balanced-mass coefficients before selecting parameters. One
positive constant and one positive integer exponent then bound the
stopping constant at every node of every selected tree. Neither depends
on the time set, the chosen parameters, or the tree depth.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

theorem exists_node_stopping_constants (hβ : 1 < β) (hβ2 : β ≤ 2)
    {c₀ c₁ d : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧
      ∀ (I : Set ℝ) (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I)
        (q : (ℝ × ℝ) × ℝ) (hq : q ∈ separatedTriples I ((volume I).toReal / 100))
        (p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ)))
        (hp : p ∈ S.cornerNodeParameters I q.1.1 q.1.2 q.2 ((volume I).toReal / 100)),
        (S.nodePattern hI hIunit hIpos hq hp).StoppingNodeBound c₀ c₁ d
          (C * ((volume I).toReal⁻¹) ^ N) := by
  obtain ⟨C, hC, N, hN, hbound⟩ := exists_polynomial_bound_controlledStoppingConstant m
    (8 * S.boundExponent) S.label_pos β (zero_lt_one.trans_le S.one_le_upperConstant) hc₀ hc₁ hd
  refine ⟨C, hC, N, hN, fun I hI hIunit hIpos q hq p hp ↦ ?_⟩
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  have hx1 : (volume I).toReal ≤ 1 := by
    simpa only [measureReal_def, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one] using measureReal_mono (μ := volume) hIunit (by simp)
  exact ((S.nodePattern_isControlled hI hIunit hIpos hq hp).stoppingNodeBound
    hβ hβ2 hc₀ hc₁ hd).mono (hbound _ hx hx1)

/-- Selected trees whose every internal node has one common polynomial stopping bound. -/
theorem exists_tree_stopping_constants (hβ : 1 < β) (hβ2 : β ≤ 2)
    {c₀ c₁ d : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧
      ∀ (I : Set ℝ), MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
        ∀ (J : ℕ) q, q ∈ separatedTriples I ((volume I).toReal / 100) →
          ∀ σ ∈ S.treeParameters I J q, ∃ T : CornerTree m β J,
            T.a T.root = q.1.1 ∧ T.b T.root = q.1.2 ∧ T.c T.root = q.2 ∧
              T.times ⊆ S.treeTimes J q σ ∧ ∀ v h,
                (T.pattern v h).StoppingNodeBound c₀ c₁ d (C * ((volume I).toReal⁻¹) ^ N) := by
  obtain ⟨C, hC, N, hN, hnode⟩ := S.exists_node_stopping_constants hβ hβ2 hc₀ hc₁ hd
  refine ⟨C, hC, N, hN, fun I hI hIunit hIpos J q hq σ hσ ↦ ?_⟩
  exact S.exists_cornerTree_of_mem_treeParameters_of_pattern_property hI hIunit hIpos
    (fun P ↦ P.StoppingNodeBound c₀ c₁ d (C * ((volume I).toReal⁻¹) ^ N))
    (hnode I hI hIunit hIpos) J hq hσ

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
