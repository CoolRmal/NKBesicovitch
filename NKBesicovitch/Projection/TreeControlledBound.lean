/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.ControlledThreshold
public import NKBesicovitch.Projection.TreeUniformBound

/-!
# An explicit normalized bound for controlled trees

The large-size stopping estimate and the separated two-slice estimate
combine with coefficient `max 1 (max C (r⁻ᵐ N₀²))`. All its inputs are
uniform geometric or analytic bounds, rather than a choice of tree.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerTree

variable {m L J : ℕ} {β r A C H : ℝ}

theorem normalized_bound_of_controlled [Nonempty (Fin m)] (T : CornerTree m β J)
    (hJ : 0 < J) (hβ : 1 < β) (hH : (T.times.card : ℝ) ≤ H)
    (hcontrol : ∀ v h, (T.pattern v h).IsControlled r A L)
    (hbound : ∀ v h, (T.pattern v h).StoppingNodeBound (1 / (4 * H)) (1 / 2) (1 / (2 * H)) C)
    {G : Set (Line m)} (hG : MeasurableSet G) (hGb : IsBounded G)
    (hM : (parallelMultiplicity G).toReal ≤ 1) {N : ℝ} (hN : 1 ≤ N)
    (hπ : ∀ t ∈ T.times, volume (atHeight t '' G) ≤ ENNReal.ofReal N) :
    let q := β / (β - 1)
    let N₀ := controlledStoppingThreshold m L J r H
    (volume G).toReal ≤ max 1 (max C (r⁻¹ ^ m * N₀ ^ 2)) * N ^
      ((2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) / (q + 2 * q ^ 2 - 2)) := by
  let q := β / (β - 1)
  let σ := (2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) / (q + 2 * q ^ 2 - 2)
  let N₀ := controlledStoppingThreshold m L J r H
  let D := max 1 (max C (r⁻¹ ^ m * N₀ ^ 2))
  have hq : 1 < q := (lt_div_iff₀ (sub_pos.mpr hβ)).mpr (by linarith)
  have hσ : 0 ≤ σ := by
    apply div_nonneg _ (corner_power_exponent_pos hq).le
    have hmain : 0 ≤ 2 * q + 3 * q ^ 2 - 2 := by nlinarith [sq_nonneg q]
    exact add_nonneg hmain (by positivity)
  have hD₁ : 1 ≤ D := le_max_left _ _
  have hDpow : D ≤ D * N ^ σ :=
    le_mul_of_one_le_right (zero_le_one.trans hD₁) (Real.one_le_rpow hN hσ)
  by_cases hL : 1 ≤ (volume G).toReal
  · by_cases hNN₀ : N₀ ≤ N
    · have hHpos := (Nat.cast_pos.mpr T.times_nonempty.card_pos).trans_le hH
      obtain ⟨_, hroot, hprune⟩ := T.stopping_threshold_of_controlled hJ hHpos hcontrol hNN₀
      exact (T.large_normalized_bound_of_stoppingNodeBounds hJ hH hbound
        hG hGb hM hL hN hπ hroot hprune).trans (mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (le_max_right _ _)) (Real.rpow_nonneg (by linarith) _))
    · have hroot : T.level T.root < J := T.root_level ▸ hJ
      have hsep := (hcontrol T.root hroot).base_separation
      rw [T.pattern_a, T.pattern_b] at hsep
      have hN₀ : 0 ≤ N₀ := zero_le_one.trans (le_max_left _ _)
      have hmass := volume_toReal_le_two_slice_of_separated
        (hcontrol T.root hroot).radius_pos hsep hN₀ G
        ((hπ _ (T.a_mem_times T.root)).trans (ENNReal.ofReal_le_ofReal (le_of_not_ge hNN₀)))
        ((hπ _ (T.b_mem_times T.root)).trans (ENNReal.ofReal_le_ofReal (le_of_not_ge hNN₀)))
      exact hmass.trans (((le_max_right _ _).trans (le_max_right _ _)).trans hDpow)
  · exact (le_of_not_ge hL).trans (hD₁.trans hDpow)

end NKBesicovitch.Projection.CornerTree
