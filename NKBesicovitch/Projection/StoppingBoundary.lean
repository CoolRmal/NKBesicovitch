/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Concentration
public import NKBesicovitch.Projection.StoppingParameters
public import Mathlib.Tactic.Finiteness

/-!
# Root and terminal bounds for corner stopping

At a terminal node, the original pair image already has outer measure at
most `N²`. At the root, the balanced pair mass and a sufficiently large
projection size make every pair lie below the initial density threshold.
The root loss quota is therefore attained without deleting any pairs.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem volume_pairProjections_le_square {a s t N : ℝ} (hN : 0 ≤ N)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hWG : W ⊆ pairFamily a G)
    (hs : volume (atHeight s '' G) ≤ ENNReal.ofReal N)
    (ht : volume (atHeight t '' G) ≤ ENNReal.ofReal N) :
    volume (pairProjections a s t '' W) ≤ ENNReal.ofReal (N ^ (2 : ℝ)) := by
  calc
    _ ≤ volume ((atHeight s '' G) ×ˢ (atHeight t '' G)) :=
      measure_mono (by rintro _ ⟨p, hp, rfl⟩; exact pairProjections_mem_prod a s t hWG hp)
    _ = volume (atHeight s '' G) * volume (atHeight t '' G) := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
    _ ≤ ENNReal.ofReal N * ENNReal.ofReal N := mul_le_mul hs ht bot_le bot_le
    _ = _ := by rw [← ENNReal.ofReal_mul hN, Real.rpow_two, pow_two]

theorem stopping_density_mul_image_ennreal (V : ℝ≥0∞) {N ρ : ℝ} (hN : 0 < N) :
    (V * ENNReal.ofReal (N ^ (-2 + ρ))) * ENNReal.ofReal (N ^ (2 - ρ)) = V := by
  rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]
  simp only [show (-2 + ρ) + (2 - ρ) = 0 by ring, Real.rpow_zero, ENNReal.ofReal_one, mul_one]

theorem root_density_threshold {c j L N V : ℝ} (hc : 0 ≤ c) (hL : 1 ≤ L) (hN : 0 < N)
    (hV : c * L ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤ V) (hlarge : j < c * N ^ (96 : ℝ)) :
    j * N < V * N ^ (98 : ℝ) := by
  have hLsq : 1 ≤ L ^ (2 : ℝ) := Real.one_le_rpow hL (by norm_num)
  calc
    j * N < (c * N ^ (96 : ℝ)) * N := mul_lt_mul_of_pos_right hlarge hN
    _ = c * N ^ (97 : ℝ) := by
      have h : N ^ (96 : ℝ) * N = N ^ (97 : ℝ) := by
        simpa only [show (96 : ℝ) + 1 = 97 by norm_num, Real.rpow_one] using
          (Real.rpow_add hN (96 : ℝ) 1).symm
      rw [mul_assoc, h]
    _ ≤ (c * L ^ (2 : ℝ)) * N ^ (97 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc hLsq)
        (Real.rpow_nonneg hN.le _)
    _ = (c * L ^ (2 : ℝ) * N ^ (-1 : ℝ)) * N ^ (98 : ℝ) := by
      symm
      rw [mul_assoc, ← Real.rpow_add hN]; norm_num
    _ ≤ V * N ^ (98 : ℝ) := mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg hN.le _)

theorem root_threshold {c j N : ℝ} (hc : 0 < c) (hN : 1 ≤ N)
    (hj : (j + 1) / c ≤ N) : j < c * N ^ (96 : ℝ) := by
  have hj' : j + 1 ≤ c * N := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hj
  have hpow : N ≤ N ^ (96 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN
      (by norm_num : (1 : ℝ) ≤ 96)
  exact (by linarith : j < c * N).trans_le (mul_le_mul_of_nonneg_left hpow hc.le)

theorem exists_root_threshold {c : ℝ} (hc : 0 < c) (j : ℝ) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N, N₀ ≤ N → j < c * N ^ (96 : ℝ) :=
  ⟨max 1 ((j + 1) / c), le_max_left _ _, fun _ hN ↦
    root_threshold hc ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN)⟩

theorem root_lowPairs_eq {a s t c L N : ℝ} (hc : 0 ≤ c) (hL : 1 ≤ L) (hN : 1 ≤ N)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hWG : W ⊆ pairFamily a G)
    {V : ℝ≥0∞} (hVfin : V ≠ ∞) (hV : c * L ^ (2 : ℝ) * N ^ (-1 : ℝ) ≤ V.toReal)
    (ha : volume (atHeight a '' G) ≤ ENNReal.ofReal N)
    (hlarge : (pairJacobian m a s t).toReal < c * N ^ (96 : ℝ)) (J : ℕ) :
    lowPairs a s t W (V * ENNReal.ofReal (N ^ (-2 + stoppingRho J 0))) = W := by
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  apply lowPairs_eq_of_projection_bound a s t hWG
  have hJac : pairJacobian m a s t ≠ ∞ := by unfold pairJacobian; finiteness
  have hproj : volume (atHeight a '' G) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, stoppingRho_zero]
  norm_num only [show (-2 : ℝ) + 100 = 98 by norm_num,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)]
  have hπ : (volume (atHeight a '' G)).toReal ≤ N := by
    have h := (ENNReal.toReal_le_toReal hproj ENNReal.ofReal_ne_top).mpr ha
    simpa only [ENNReal.toReal_ofReal hNpos.le] using h
  exact (mul_le_mul_of_nonneg_left hπ ENNReal.toReal_nonneg).trans_lt
    (root_density_threshold hc hL hNpos hV hlarge)

end NKBesicovitch.Projection
