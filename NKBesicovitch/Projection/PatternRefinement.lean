/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PatternCodeImages
public import NKBesicovitch.Projection.StoppingBudget

/-!
# Refining all children of a fixed corner pattern

Concentrated children produce one Borel pair family with small images under
every inner code. The loss is at most half the parent quota. Its image bound
uses a positive constant chosen before the line family and stopping level.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerPattern

variable {m : ℕ} {β : ℝ}

/-- The child-refinement conclusion with a prescribed inner-code constant. -/
def RefinementBound (P : CornerPattern m β) (K : ℝ) : Prop :=
    ∀ G : Set (Line m), IsBounded G → (parallelMultiplicity G).toReal ≤ 1 →
      ∀ W : Set (PairCoordinates m), MeasurableSet W → W ⊆ pairFamily P.b G →
      ∀ V : ℝ≥0∞, 0 < V → V ≠ ∞ → volume W = V →
      ∀ N : ℝ, 1 ≤ N → ∀ J i : ℕ, 0 < J → i < J →
      4 * (1 + 2 * (P.outer.card : ℝ)) * P.children.card ≤ N ^ (1 / (J : ℝ) ^ 2) →
      (∀ v ∈ P.children, ∃ E : Set (PairCoordinates m), MeasurableSet E ∧ E ⊆ W ∧
        volume (W \ E) ≤ V * ENNReal.ofReal (N ^ (-stoppingAlpha J (i + 1))) ∧
        volume (pairProjections P.b v.2
          (dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ v.1) v.2) '' E) ≤
            ENNReal.ofReal (N ^ (2 - stoppingRho J (i + 1)))) →
      ∃ E : Set (PairCoordinates m), MeasurableSet E ∧ E ⊆ W ∧
        volume (W \ E) ≤ (V * ENNReal.ofReal (N ^ (-stoppingAlpha J i))) / 2 ∧
        ∀ u ∈ P.outer,
          volume (pairCode P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) '' E) ≤
            ENNReal.ofReal (K * V.toReal *
              (V.toReal * N ^ (-2 + stoppingRho J i - 200 / J)) ^ (-(β / (β - 1))))

theorem refinementBound_of_codeImageBound (P : CornerPattern m β) {K : ℝ}
    (hcode : P.CodeImageBound K) : P.RefinementBound K := by
  intro G hGb hM W hW hWG V hV₀ hV hWV N hN J i hJ hi hlarge hchild
  have hs : ∀ v ∈ P.children, v.2 ≠ P.b := by
    intro v hv
    obtain ⟨hu, ht⟩ := mem_children.mp hv
    exact P.inner_ne_b v.1 hu v.2 ht
  obtain ⟨E₁, E₂, E₃, hE₁, hE₂, hE₃, hE₁W, hE₂E₁, hE₃E₂, hloss, hdense, hretain⟩ :=
    exists_refined_child_pairs_half_parent P.a_ne_b.symm hN Prod.snd
      (fun v ↦ dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ v.1) v.2) P.children
      (cornerInnerCoefficient P.a P.c P.κ) P.outer hs (fun _ ↦ P.child_dual_ne_base)
      hW hV hJ hi hlarge hchild
  refine ⟨E₃, hE₃, hE₃E₂.trans (hE₂E₁.trans hE₁W), hloss, fun u hu ↦ ?_⟩
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  have hVreal := ENNReal.toReal_pos hV₀.ne' hV
  have hℓ : 0 < (V * ENNReal.ofReal (N ^ (-2 + stoppingRho J i - 200 / J))).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)]
    exact mul_pos hVreal (Real.rpow_pos_of_pos hNpos _)
  simpa only [hWV, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)] using
    hcode G hGb hM W E₁ E₂ E₃ hW hE₁ hE₂ hWG hE₁W (hE₂E₁.trans hE₁W)
      _ hℓ hdense hretain u hu

theorem exists_refinement_constant (P : CornerPattern m β) (hβ : 1 < β) (hβ2 : β ≤ 2) :
    ∃ K : ℝ, 0 < K ∧ P.RefinementBound K := by
  obtain ⟨K, hK, hcode⟩ := P.exists_code_image_constant hβ hβ2
  exact ⟨K, hK, P.refinementBound_of_codeImageBound hcode⟩

end NKBesicovitch.Projection.CornerPattern
