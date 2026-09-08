/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PatternCorners
public import NKBesicovitch.Projection.NormalizedAmplification

/-!
# The normalized bound at one stopping node

For a fixed admissible pattern, a uniform parent and concentrated children
give the finite-depth exponent bound. The constant is independent of the
line family, projection size, stopping level, and depth. Balanced masses
are expressed by fixed upper and lower coefficients.

This is conditional on the supplied stopping data. The construction of a
finite height tree and the selection of such a node are separate steps.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerPattern

variable {m : ℕ} {β : ℝ}

theorem exists_stopping_node_constant (P : CornerPattern m β) (hβ : 1 < β) (hβ2 : β ≤ 2)
    {c₀ c₁ d : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hd : 0 < d) :
    let q := β / (β - 1)
    ∃ C : ℝ, 0 < C ∧
      ∀ G : Set (Line m), IsBounded G → (parallelMultiplicity G).toReal ≤ 1 →
      ∀ G₀ A B : Set (Line m), MeasurableSet G₀ → MeasurableSet A → MeasurableSet B →
      G₀ ⊆ G → A ⊆ G → B ⊆ G → ∀ η : ℝ≥0∞, 0 < η → η ≠ ∞ →
      (∀ g ∈ G₀, sliceMultiplicity P.a A (atHeight P.a g) = η) →
      (∀ g ∈ G₀, sliceMultiplicity P.b B (atHeight P.b g) = η) →
      ∀ V : ℝ≥0∞, 0 < V → V ≠ ∞ → volume (companionPairs P.b G₀ B) = V →
      ∀ L N : ℝ, 0 < L → 1 ≤ N →
      c₀ * L ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤ V.toReal →
      V.toReal ≤ c₁ * L ^ (2 : ℝ) * N ^ (-1 : ℝ) →
      d * L * N ^ (-1 : ℝ) ≤ η.toReal →
      (∀ t ∈ P.times, volume (atHeight t '' G) ≤ ENNReal.ofReal N) →
      ∀ J i : ℕ, 0 < J → i < J →
      4 * (1 + 2 * (P.outer.card : ℝ)) * P.children.card ≤ N ^ (1 / (J : ℝ) ^ 2) →
      ∀ U : Set (PairCoordinates m), MeasurableSet U → U ⊆ companionPairs P.a G₀ A →
      V * ENNReal.ofReal (N ^ (-stoppingAlpha J i)) ≤ volume U →
      (∀ p ∈ U, pairDensity P.a P.b P.c (companionPairs P.a G₀ A)
        (pairProjections P.a P.b P.c p) ≤ V * ENNReal.ofReal (N ^ (-2 + stoppingRho J i))) →
      (∀ v ∈ P.children, ∃ E : Set (PairCoordinates m), MeasurableSet E ∧
        E ⊆ companionPairs P.b G₀ B ∧
        volume (companionPairs P.b G₀ B \ E) ≤
          V * ENNReal.ofReal (N ^ (-stoppingAlpha J (i + 1))) ∧
        volume (pairProjections P.b v.2
          (dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ v.1) v.2) '' E) ≤
            ENNReal.ofReal (N ^ (2 - stoppingRho J (i + 1)))) →
      L ≤ C * N ^ ((2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) /
        (q + 2 * q ^ 2 - 2)) := by
  let q := β / (β - 1)
  have hq : 1 < q := (lt_div_iff₀ (sub_pos.mpr hβ)).mpr (by linarith)
  have hr : 0 < (P.outer.card : ℝ) := Nat.cast_pos.mpr P.outer_nonempty.card_pos
  obtain ⟨K, C₀, hK, hC₀, hcorners⟩ := P.exists_stopping_corner_constants hβ hβ2
  let A₀ := (c₀ * d / 2) / (2 * P.outer.card * (K * c₀ ^ (1 - q)))
  have hA₀ : 0 < A₀ := by dsimp only [A₀]; positivity
  refine ⟨(C₀ * c₁ / A₀ ^ q) ^ (1 / (q + 2 * q ^ 2 - 2)), by positivity,
    fun G hGb hM G₀ A B hG₀ hA hB hG₀G hAG hBG η hη hηfin hηₐ hηᵦ V hV₀ hV hWV
      L N hL hN hVlower hVupper hηlower htimes J i hJ hi hlarge U hU hUP hparent hQ hchild ↦ ?_⟩
  obtain ⟨D, hD, houter⟩ := hcorners G hGb hM G₀ A B hG₀ hA hB hG₀G hAG hBG η
    hη hηfin hηₐ hηᵦ V hV₀ hV hWV N hN htimes J i hJ hi hlarge U hU hUP hparent hQ hchild
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  have hVreal := ENNReal.toReal_pos hV₀.ne' hV
  have hR : 0 < K * V.toReal * (V.toReal * N ^ (-2 + stoppingRho J i - 200 / J)) ^ (-q) :=
    by positivity
  exact normalized_corner_bound hq hc₀ hc₁.le hd hK hC₀.le hL hN hVreal
    ENNReal.toReal_nonneg hR hr hJ hi.le hVlower hVupper hηlower hD le_rfl houter

end NKBesicovitch.Projection.CornerPattern
