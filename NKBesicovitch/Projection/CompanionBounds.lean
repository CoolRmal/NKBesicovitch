/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CompanionSystem

/-!
# Balanced masses using an upper bound on the height count

An upper bound `H` on the number of heights gives fixed lower coefficients
`1/(4H)` for pair mass and `1/(2H)` for slice mass. The pair-mass upper
coefficient can be chosen as `1/2`, independently of the actual height set.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

theorem exists_companionSystem_of_card_le {m : ℕ} [Nonempty (Fin m)] (Γ : Finset ℝ)
    (hΓ : Γ.Nonempty) {H : ℝ} (hH : (Γ.card : ℝ) ≤ H)
    {G : Set (Line m)} (hG : MeasurableSet G) (hGb : IsBounded G) (hGpos : 0 < volume G)
    {N : ℝ} (hN : 0 < N) (hπ : ∀ t ∈ Γ, volume (atHeight t '' G) ≤ ENNReal.ofReal N) :
    ∃ S : CompanionSystem G Γ,
      (1 / (2 * H)) * (volume G).toReal * N ^ (-1 : ℝ) ≤ S.η.toReal ∧
      (1 / (4 * H)) * (volume G).toReal ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤
        (volume S.centers * S.η).toReal ∧
      (volume S.centers * S.η).toReal ≤
        (1 / 2) * (volume G).toReal ^ (2 : ℝ) * N ^ (-1 : ℝ) := by
  have hr : 0 < (Γ.card : ℝ) := Nat.cast_pos.mpr hΓ.card_pos
  have hr1 : 1 ≤ (Γ.card : ℝ) := by exact_mod_cast hΓ.card_pos
  have hHpos := hr.trans_le hH
  have hc₀ : 1 / (4 * H) ≤ 1 / (4 * Γ.card) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hd : 1 / (2 * H) ≤ 1 / (2 * Γ.card) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hc₁ : 1 / (2 * (Γ.card : ℝ)) ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  obtain ⟨S, hη, hVl, hVu⟩ := exists_companionSystem Γ hΓ hG hGb hGpos hN hπ
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [hη]
    calc
      _ ≤ (1 / (2 * Γ.card)) * (volume G).toReal * N ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd ENNReal.toReal_nonneg)
          (Real.rpow_nonneg hN.le _)
      _ = _ := by rw [Real.rpow_neg_one]; field_simp
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc₀ (by positivity)) (Real.rpow_nonneg hN.le _)).trans hVl
  · exact hVu.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc₁ (by positivity)) (Real.rpow_nonneg hN.le _))

end NKBesicovitch.Projection
