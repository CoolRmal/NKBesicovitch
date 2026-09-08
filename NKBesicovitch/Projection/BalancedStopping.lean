/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.BalancedPairs
public import NKBesicovitch.Projection.StoppingParameters
public import Mathlib.Tactic.Finiteness

/-!
# Balanced masses with the stopping constants

For a positive line mass `L` and a finite nonempty height set of size `r`,
choose companion mass `L / (2rN)`. The center family retains at least half
the line mass, and all its companion-pair masses lie between
`L² / (4rN)` and `L² / (2rN)`.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem balanced_pair_mass_bounds {L L₀ r N η : ℝ} (hL : 0 ≤ L) (hr : 0 < r) (hN : 0 < N)
    (hlower : L / 2 ≤ L₀) (hupper : L₀ ≤ L) (hη : η = L / (2 * r * N)) :
    (1 / (4 * r)) * L ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤ L₀ * η ∧
      L₀ * η ≤ (1 / (2 * r)) * L ^ (2 : ℝ) * N ^ (-1 : ℝ) := by
  have hηpos : 0 ≤ η := by rw [hη]; positivity
  constructor
  · calc
      _ = (L / 2) * η := by
        rw [hη, Real.rpow_two, Real.rpow_neg_one]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlower hηpos
  · calc
      _ ≤ L * η := mul_le_mul_of_nonneg_right hupper hηpos
      _ = _ := by
        rw [hη, Real.rpow_two, Real.rpow_neg_one]
        field_simp

theorem exists_balanced_stopping_data [Nonempty (Fin m)] (Γ : Finset ℝ) (hΓ : Γ.Nonempty)
    {G : Set (Line m)} (hG : MeasurableSet G) (hGb : IsBounded G) (hGpos : 0 < volume G)
    {N : ℝ} (hN : 0 < N) (hπ : ∀ t ∈ Γ, volume (atHeight t '' G) ≤ ENNReal.ofReal N) :
    ∃ η : ℝ≥0∞, 0 < η ∧ η ≠ ∞ ∧
      η.toReal = (volume G).toReal / (2 * Γ.card * N) ∧
      ∃ G₀ : Set (Line m), MeasurableSet G₀ ∧ G₀ ⊆ G ∧ volume G / 2 ≤ volume G₀ ∧
        (1 / (4 * Γ.card)) * (volume G).toReal ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤
          (volume G₀ * η).toReal ∧
        (volume G₀ * η).toReal ≤
          (1 / (2 * Γ.card)) * (volume G).toReal ^ (2 : ℝ) * N ^ (-1 : ℝ) ∧
        ∀ t ∈ Γ, ∃ C : Set (Line m), MeasurableSet C ∧ C ⊆ G ∧
          (∀ g ∈ G₀, sliceMultiplicity t C (atHeight t g) = η) ∧
          volume (companionPairs t G₀ C) = volume G₀ * η := by
  let L := (volume G).toReal
  let r := (Γ.card : ℝ)
  have hr : 0 < r := Nat.cast_pos.mpr hΓ.card_pos
  have hGfin : volume G ≠ ∞ := hGb.measure_lt_top.ne
  have hL : 0 < L := ENNReal.toReal_pos hGpos.ne' hGfin
  let η := ENNReal.ofReal (L / (2 * r * N))
  have hηreal : η.toReal = L / (2 * r * N) := ENNReal.toReal_ofReal (by positivity)
  have hη : 0 < η := ENNReal.ofReal_pos.mpr (by positivity)
  have hηfin : η ≠ ∞ := ENNReal.ofReal_ne_top
  have hbudget : Γ.card * η * ENNReal.ofReal N ≤ volume G / 2 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, hηreal,
      ENNReal.toReal_ofReal hN.le, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    change r * (L / (2 * r * N)) * N ≤ L / 2
    have h : r * (L / (2 * r * N)) * N = L / 2 := by field_simp
    exact h.le
  obtain ⟨G₀, hG₀, hG₀G, hhalf, hcompanions⟩ := exists_balanced_pairs Γ hG hGb η _ hπ hbudget
  have hG₀fin : volume G₀ ≠ ∞ := (hGb.subset hG₀G).measure_lt_top.ne
  have hlower : L / 2 ≤ (volume G₀).toReal := by
    simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using
      (ENNReal.toReal_le_toReal (by finiteness) hG₀fin).mpr hhalf
  have hupper : (volume G₀).toReal ≤ L :=
    (ENNReal.toReal_le_toReal hG₀fin hGfin).mpr (measure_mono hG₀G)
  have hmass := balanced_pair_mass_bounds hL.le hr hN hlower hupper hηreal
  rw [← ENNReal.toReal_mul] at hmass
  exact ⟨η, hη, hηfin, hηreal, G₀, hG₀, hG₀G, hhalf, hmass.1, hmass.2, hcompanions⟩

end NKBesicovitch.Projection
