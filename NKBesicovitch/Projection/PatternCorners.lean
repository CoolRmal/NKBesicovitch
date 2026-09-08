/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PatternRefinement
public import NKBesicovitch.Projection.PatternOuter
public import NKBesicovitch.Projection.CornerPreparation

/-!
# The geometric inequalities at a stopping corner node

A parent with enough low-density mass and concentrated children supplies
positive corner mass. The simultaneous inner-code bounds and the outer
projection estimate give the two inequalities needed for numerical
amplification, with constants fixed before the line family and level.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerPattern

variable {m : ℕ} {β : ℝ}

theorem exists_stopping_corner_constants (P : CornerPattern m β) (hβ : 1 < β) (hβ2 : β ≤ 2) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ G : Set (Line m), IsBounded G → (parallelMultiplicity G).toReal ≤ 1 →
      ∀ G₀ A B : Set (Line m), MeasurableSet G₀ → MeasurableSet A → MeasurableSet B →
      G₀ ⊆ G → A ⊆ G → B ⊆ G → ∀ η : ℝ≥0∞, 0 < η → η ≠ ∞ →
      (∀ g ∈ G₀, sliceMultiplicity P.a A (atHeight P.a g) = η) →
      (∀ g ∈ G₀, sliceMultiplicity P.b B (atHeight P.b g) = η) →
      ∀ V : ℝ≥0∞, 0 < V → V ≠ ∞ → volume (companionPairs P.b G₀ B) = V →
      ∀ N : ℝ, 1 ≤ N → (∀ t ∈ P.times, volume (atHeight t '' G) ≤ ENNReal.ofReal N) →
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
      ∃ D : ℝ, (V.toReal * N ^ (-stoppingAlpha J i)) * η.toReal / 2 ≤ D ∧
        (D / (2 * P.outer.card * N *
          (K * V.toReal * (V.toReal * N ^ (-2 + stoppingRho J i - 200 / J)) ^
            (-(β / (β - 1)))))) ^ (β / (β - 1)) ≤
          C * (N * (V.toReal * N ^ (-2 + stoppingRho J i))) := by
  obtain ⟨K, hK, hrefine⟩ := P.exists_refinement_constant hβ hβ2
  obtain ⟨C, hC, houter⟩ := P.exists_outer_constant hβ hβ2
  refine ⟨K, C, hK, hC, fun G hGb hM G₀ A B hG₀ hA hB hG₀G hAG hBG η hη hηfin
    hηₐ hηᵦ V hV₀ hV hWV N hN htimes J i hJ hi hlarge U hU hUP hparent hQ hchild ↦ ?_⟩
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  have hVreal := ENNReal.toReal_pos hV₀.ne' hV
  obtain ⟨E, hE, _, hloss, himage⟩ := hrefine G hGb hM _
    (measurableSet_companionPairs P.b hG₀ hB)
    (companionPairs_subset_pairFamily P.b hG₀G hBG) V hV₀ hV hWV N hN J i hJ hi hlarge hchild
  have hUfin : volume U ≠ ∞ := ((isBounded_pairFamily P.a hGb).subset
    (hUP.trans (companionPairs_subset_pairFamily P.a hG₀G hAG))).measure_lt_top.ne
  have hδ : 0 < V * ENNReal.ofReal (N ^ (-stoppingAlpha J i)) :=
    ENNReal.mul_pos hV₀.ne' (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hNpos _)).ne'
  obtain ⟨D, hD, hDG, hDpos, hmass, hrestrict⟩ := exists_corners_of_parent_and_child P.a P.b
    hG₀ hA hB hG₀G hAG hBG hU hE hUP hUfin hη hηfin hδ hηₐ hηᵦ hparent hloss
  let R := K * V.toReal * (V.toReal * N ^ (-2 + stoppingRho J i - 200 / J)) ^ (-(β / (β - 1)))
  have hR : 0 < R := by dsimp only [R]; positivity
  have hDfin : volume D ≠ ∞ :=
    ((isBounded_cornerFamily P.a P.b hGb).subset hDG).measure_lt_top.ne
  refine ⟨(volume D).toReal, ?_, ?_⟩
  · have h := (ENNReal.toReal_le_toReal (by finiteness) hDfin).mpr hmass
    simpa only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)] using h
  · have h := houter G hGb hM (ENNReal.ofReal N) (ENNReal.ofReal R)
      (ENNReal.ofReal_pos.mpr hNpos).ne' ENNReal.ofReal_ne_top
      (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top
      (htimes P.c P.c_mem_times) (fun u hu ↦ htimes u (P.outer_subset_times hu))
      D hD hDG hDpos (companionPairs P.a G₀ A) E
      (fun p hp ↦ hUP (hrestrict p hp).1) (fun p hp ↦ (hrestrict p hp).2)
      _ (by finiteness) (fun p hp ↦ hQ _ (hrestrict p hp).1) himage
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hNpos.le,
      ENNReal.toReal_ofReal hR.le, ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)] using h

end NKBesicovitch.Projection.CornerPattern
