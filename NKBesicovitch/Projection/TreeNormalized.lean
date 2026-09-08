/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.TreeBound

/-!
# The normalized finite-tree estimate at every projection size above one

The finite-tree argument handles large line mass and large projection size.
Small line mass is absorbed by the constant, and bounded projection size
is controlled by the two-slice seed at the root's first two heights.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerTree

variable {m J : ℕ} {β : ℝ}

theorem exists_normalized_bound [Nonempty (Fin m)] (T : CornerTree m β J)
    (hJ : 0 < J) (hβ : 1 < β) (hβ2 : β ≤ 2) :
    let q := β / (β - 1)
    ∃ C : ℝ, 0 < C ∧ ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
      (parallelMultiplicity G).toReal ≤ 1 →
      ∀ N : ℝ, 1 ≤ N → (∀ t ∈ T.times, volume (atHeight t '' G) ≤ ENNReal.ofReal N) →
      (volume G).toReal ≤ C *
        N ^ ((2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) /
          (q + 2 * q ^ 2 - 2)) := by
  let q := β / (β - 1)
  let σ := (2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) / (q + 2 * q ^ 2 - 2)
  have hq : 1 < q := (lt_div_iff₀ (sub_pos.mpr hβ)).mpr (by linarith)
  have hσ : 0 ≤ σ := by
    apply div_nonneg _ (corner_power_exponent_pos hq).le
    have hmain : 0 ≤ 2 * q + 3 * q ^ 2 - 2 := by nlinarith [sq_nonneg q]
    exact add_nonneg hmain (by positivity)
  obtain ⟨C, N₀, hC, hN₀, hlarge⟩ := T.exists_large_normalized_bound hJ hβ hβ2
  obtain ⟨K, hK, htwo⟩ := hasProjectionEstimate_twoSlice (m := m) (T.b_ne_a T.root).symm
  let D := max 1 (max C (K * N₀ ^ 2))
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨D, hD, fun G hG hGb hM N hN hπ ↦ ?_⟩
  have hNpos := zero_lt_one.trans_le hN
  have hDpow : D ≤ D * N ^ σ := le_mul_of_one_le_right hD.le (Real.one_le_rpow hN hσ)
  by_cases hL : 1 ≤ (volume G).toReal
  · by_cases hNN₀ : N₀ ≤ N
    · exact (hlarge G hG hGb hM hL N hNN₀ hπ).trans
        (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
          (Real.rpow_nonneg hNpos.le _))
    · have hsubset : ({T.a T.root, T.b T.root} : Finset ℝ) ⊆ T.times := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact T.a_mem_times T.root
        · exact Finset.mem_singleton.mp ht ▸ T.b_mem_times T.root
      have hsize : (sliceSize {T.a T.root, T.b T.root} G).toReal ≤ N₀ := by
        apply sliceSize_toReal_le hGb (zero_le_one.trans hN₀)
        intro t ht
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hπ t (hsubset ht))
        rw [ENNReal.toReal_ofReal hNpos.le] at h
        exact h.trans (le_of_not_ge hNN₀)
      have h := htwo G hG hGb
      simp only [sub_self, Real.rpow_zero, mul_one, Real.rpow_two, pow_two] at h
      have hmass : (volume G).toReal ≤ K * N₀ ^ 2 := by
        simpa only [pow_two] using h.trans (mul_le_mul_of_nonneg_left
          (mul_self_le_mul_self ENNReal.toReal_nonneg hsize) hK.le)
      exact hmass.trans (((le_max_right _ _).trans (le_max_right _ _)).trans hDpow)
  · exact (le_of_not_ge hL).trans ((le_max_left _ _).trans hDpow)

end NKBesicovitch.Projection.CornerTree
