/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.DyadicDecomposition
public import NKBesicovitch.Operators.XRay.InterpolatedFibers
public import NKBesicovitch.Operators.Interpolation.BlockSummation

/-!
# Strong mixed-norm bounds for indicator inputs

At every projection exponent above the critical root and at most two,
some finite outer exponent `Q > 2` gives the indicator bound
`‖T 1_E‖_(L^Q L^(Q/(β-1))) ≤ C |E|^(βθ/Q)` for each `0 < θ < 1`.
The constant is uniform over Borel subsets of a fixed bounded support.
The slope set is fixed, bounded, and Borel. The two dyadic series are
summed internally; no fiber-size restriction remains in the conclusion.
-/

public section

open MeasureTheory Set Bornology NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

theorem exists_indicator_mixedNorm_bound (m : ℕ) [Nonempty (Fin m)] {β : ℝ}
    (hβ : projectionExponent < β) (hβ2 : β ≤ 2) :
    ∃ Q : ℕ, 2 < Q ∧ ∀ K : Set (EuclideanSpace ℝ (Fin m) × ℝ), IsBounded K →
      ∀ Ξ : Set (EuclideanSpace ℝ (Fin m)), MeasurableSet Ξ → IsBounded Ξ →
        ∀ θ : ℝ, 0 < θ → θ < 1 → ∃ C : ℝ, 0 < C ∧
          ∀ E : Set (EuclideanSpace ℝ (Fin m) × ℝ), MeasurableSet E → E ⊆ K →
            mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
              (fun g : Line m ↦ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1))
                (ENNReal.ofReal Q) (ENNReal.ofReal ((Q : ℝ) / (β - 1))) volume volume ≤
                  ENNReal.ofReal C * volume E ^ (β * θ / Q) := by
  obtain ⟨C, hC, Q, hQ, hblock⟩ := exists_restricted_mixedNorm_fiberBlock_bound m hβ hβ2
  refine ⟨Q, hQ, ?_⟩
  intro K hK Ξ hΞ hΞb θ hθ hθ1
  have hβ1 : 1 < β := projectionExponent_mem.1.trans hβ
  have hden : 0 < β - 1 := by linarith
  have hQreal : (2 : ℝ) < Q := by exact_mod_cast hQ
  have hq : 1 ≤ ENNReal.ofReal (Q : ℝ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hr : 1 ≤ ENNReal.ofReal ((Q : ℝ) / (β - 1)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hden).mpr (by linarith))
  obtain ⟨B, hB, hfibers⟩ := exists_uniform_fiber_bound hK hΞb
  obtain ⟨D, hD, hsum⟩ := exists_interpolated_series_constant
    (C := ENNReal.ofReal C) (S := volume Ξ) ENNReal.ofReal_ne_top hΞb.measure_lt_top.ne hB
    (by linarith : 0 < (Q : ℝ)) hβ1 hθ.le hθ1
  refine ⟨D, hD, fun E hE hEK ↦ ?_⟩
  have hEb := hK.subset hEK
  have hEfin : volume E ≠ ∞ := hEb.measure_lt_top.ne
  apply (mixedNorm_localXRay_le_double_sum hE hΞ hB
    (fun j ξ ↦ hfibers E hE hEK _ (by positivity) ξ) hq hr
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).trans
  apply hsum
  intro j l
  have hj : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hgeom := hblock E hE hEfin (richLines E Ξ ((1 / 2 : ℝ) ^ j / 2))
    (measurableSet_richLines hE hΞ _) (isBounded_richLines hE hEb hΞb (by positivity))
    (B * (1 / 2 : ℝ) ^ l) ((1 / 2 : ℝ) ^ j / 2) (by positivity) (by positivity)
    (by linarith) (fun _ hg ↦ hg.2)
  have hint := interpolate_mixedNorm_fiberBlock (by omega : 0 < Q) hβ1 hC.le
    ENNReal.toReal_nonneg (measurableSet_richLines hE hΞ _) hΞ (fun _ hg ↦ hg.1)
    (by positivity) hθ.le hθ1.le hgeom
  simpa only [ENNReal.ofReal_toReal hEfin] using hint

end NKBesicovitch.XRay
