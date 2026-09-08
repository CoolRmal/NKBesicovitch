/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.TreeControl
public import NKBesicovitch.Projection.TreePolynomialBound
public import NKBesicovitch.Projection.Normalization

/-!
# Uniform polynomial projection bounds for selected tree parameters

Fix the input scheme and a positive depth. Every selected parameter then
satisfies the finite-tree projection estimate with the same constant,
bounded by a fixed power of the inverse measure of the time set. Spatial
normalization restores the full parallel-multiplicity factor and preserves
that constant.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L J : ℕ} [Nonempty (Fin m)] {β : ℝ}
  (S : SelectableProjectionScheme m β D L)

theorem exists_tree_normalized_constants (hβ : 1 < β) (hβ2 : β ≤ 2) (hJ : 0 < J) :
    let q := β / (β - 1)
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 0 < B ∧
      ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
        ∀ q₀, q₀ ∈ separatedTriples I ((volume I).toReal / 100) →
          ∀ σ ∈ S.treeParameters I J q₀,
            ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
              (parallelMultiplicity G).toReal ≤ 1 → ∀ N : ℝ, 1 ≤ N →
                (∀ t ∈ S.treeTimes J q₀ σ, volume (atHeight t '' G) ≤ ENNReal.ofReal N) →
                (volume G).toReal ≤ (C * (volume I).toReal⁻¹ ^ B) * N ^
                  ((2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) /
                    (q + 2 * q ^ 2 - 2)) := by
  have hH : (0 : ℝ) < Fintype.card (TreeTimeLabel L J) := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨C, hC, B, hB, hbound⟩ := exists_polynomial_normalized_tree_bound
    (m := m) (8 * S.boundExponent) hβ hβ2 S.label_pos hJ
    (zero_lt_one.trans_le S.one_le_upperConstant) hH
  refine ⟨C, hC, B, hB, fun I hI hIunit hIpos q₀ hq σ hσ G hG hGb hM N hN hπ ↦ ?_⟩
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  have hx₁ : (volume I).toReal ≤ 1 := by
    simpa only [measureReal_def, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one] using measureReal_mono (μ := volume) hIunit (by simp)
  obtain ⟨T, _, _, _, htimes, hcontrol⟩ :=
    S.exists_controlled_cornerTree_of_mem_treeParameters hI hIunit hIpos J hq hσ
  have hcard : T.times.card ≤ Fintype.card (TreeTimeLabel L J) :=
    (Finset.card_le_card htimes).trans (Finset.card_image_le.trans_eq (Finset.card_univ))
  exact hbound _ hx hx₁ T (Nat.cast_le.mpr hcard) hcontrol G hG hGb hM N hN
    (fun t ht ↦ hπ t (htimes ht))

theorem exists_tree_projection_constants (hβ : 1 < β) (hβ2 : β ≤ 2) (hJ : 0 < J) :
    let q := β / (β - 1)
    let γ := (2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) / (q + 2 * q ^ 2 - 2)
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 0 < B ∧
      ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
        ∀ q₀, q₀ ∈ separatedTriples I ((volume I).toReal / 100) →
          ∀ σ ∈ S.treeParameters I J q₀,
            ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
              (volume G).toReal ≤ (C * (volume I).toReal⁻¹ ^ B) *
                (parallelMultiplicity G).toReal ^ (2 - γ) *
                  (sliceSize (S.treeTimes J q₀ σ) G).toReal ^ γ := by
  obtain ⟨C, hC, B, hB, hbound⟩ := S.exists_tree_normalized_constants hβ hβ2 hJ
  refine ⟨C, hC, B, hB, fun I hI hIunit hIpos q₀ hq σ hσ G hG hGb ↦ ?_⟩
  have htimes : (S.treeTimes J q₀ σ).Nonempty :=
    Finset.univ_nonempty.image (S.treeTime J q₀ σ)
  exact volume_le_of_normalized htimes (by positivity)
    (hbound I hI hIunit hIpos q₀ hq σ hσ) hG hGb

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
