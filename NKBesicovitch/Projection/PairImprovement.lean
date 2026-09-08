/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PairStep
public import NKBesicovitch.Projection.PairParameters
public import Mathlib.Tactic.NormNum

/-!
# The basic pair improvement

A uniform estimate at exponent `β ∈ (1,2]` improves to exponent
`2 - 1/(2β)` after adjoining the base heights and dual heights. The new constant
is uniform over all bounded Borel line families. This is Proposition 5.1 of
the supplied projection manuscript.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem HasProjectionEstimate.pair_improvement {β a b c : ℝ} {Γ : Finset ℝ}
    (hEst : HasProjectionEstimate m β Γ) (hβ : 1 < β) (hβ2 : β ≤ 2)
    (hΓ : Γ.Nonempty) (hab : a ≠ b) (hc : c ≠ 0)
    (hta : ∀ t ∈ Γ, t ≠ a) (htb : ∀ t ∈ Γ, t ≠ b) :
    HasProjectionEstimate m (2 - 1 / (2 * β)) (pairTimes a b c Γ) := by
  obtain ⟨C, hC, hOld⟩ := hEst
  obtain ⟨q, hq, hqt⟩ := exists_uniform_pairJacobian (m := m) hab hc hΓ hta htb
  let J := (codeJacobian m a b).toReal
  let R : ℝ := 2 * Γ.card
  let K := (((2 * J * C) * (J ^ 2) ^ (β - 1)) * (R / q) ^ β) ^ (1 / (2 * β))
  have hJ : 0 < J := ENNReal.toReal_pos (codeJacobian_pos hab).ne' (codeJacobian_ne_top m a b)
  have hr : Γ.card ≠ 0 := (Finset.card_pos.mpr hΓ).ne'
  have hR : 0 < R := mul_pos (by positivity) (Nat.cast_pos.mpr (Finset.card_pos.mpr hΓ))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun G hG hGb ↦ ?_⟩
  rw [show 2 - (2 - 1 / (2 * β)) = 1 / (2 * β) by ring]
  by_cases hz : volume G = 0
  · rw [hz, ENNReal.toReal_zero]
    positivity
  have hGpos : 0 < volume G := pos_iff_ne_zero.mpr hz
  let N := sliceSize (pairTimes a b c Γ) G
  let ℓ := pairThreshold (volume (pairFamily a G)) N Γ.card
  have hN : N ≠ ∞ := sliceSize_ne_top _ hGb
  have haN := volume_projection_le_sliceSize (mem_pairTimes_base_left a b c Γ) G
  have hbN := volume_projection_le_sliceSize (mem_pairTimes_base_right a b c Γ) G
  have hNpos : 0 < N := (parallelMultiplicity_pos hG hGpos).trans_le
    ((parallelMultiplicity_le_projection G b).trans hbN)
  have hℓ : 0 < ℓ.toReal := pairThreshold_toReal_pos (volume_pairFamily_pos a hG hGpos).ne'
    (volume_pairFamily_ne_top a hGb) hNpos.ne' hN hr
  exact volume_le_pair_step hab hc hβ hβ2 hC Γ hOld hta htb hG hGb hGpos ℓ N hℓ hN
    (ENNReal.toReal_pos hNpos.ne' hN) hbN
    (fun t ht ↦ volume_projection_le_sliceSize (subset_pairTimes a b c Γ ht) G)
    (fun t ht ↦ volume_projection_le_sliceSize (dualTime_mem_pairTimes a b c ht) G)
    (pairThreshold_budget _ hNpos.ne' hN hr).le R q hR hq hqt
    (sq_volume_le_pairThreshold a hG hGb hNpos.ne' hN haN hr)

/-- One pair improvement of the two-slice seed gives the classical exponent `7/4`. -/
theorem hasProjectionEstimate_seven_four :
    HasProjectionEstimate m (7 / 4) {0, 1, 2, 3, 3 / 2} := by
  have hseed := hasProjectionEstimate_twoSlice (m := m) (s := 2) (t := 3) (by norm_num)
  have h := hseed.pair_improvement
    (a := 0) (b := 1) (c := 1) (by norm_num) (by norm_num) (by simp)
    (by norm_num) (by norm_num) (by simp) (by simp)
  norm_num [pairTimes, dualTime] at h
  simpa [Finset.insert_comm] using h

end NKBesicovitch.Projection
