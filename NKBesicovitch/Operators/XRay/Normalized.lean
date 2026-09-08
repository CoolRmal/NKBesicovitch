/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.Indicator
public import NKBesicovitch.Operators.XRay.InputBound

/-!
# Normalized strong mixed-norm X-ray bounds

For each projection exponent `β` above the critical root, one outer
exponent `Q > 2` works for every input exponent `p > Q / β`. An indicator
exponent is selected strictly between `1 / p` and `β / Q`, so the input
superlevel series converges. Constants are uniform over inputs with
`L^p` norm at most one on a fixed bounded support and bounded slope set.
-/

public section

open MeasureTheory Set Bornology NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

theorem exists_normalized_mixedNorm_bound (m : ℕ) [Nonempty (Fin m)] {β : ℝ}
    (hβ : projectionExponent < β) (hβ2 : β ≤ 2) :
    ∃ Q : ℕ, 2 < Q ∧ ∀ K : Set (EuclideanSpace ℝ (Fin m) × ℝ), IsBounded K →
      ∀ Ξ : Set (EuclideanSpace ℝ (Fin m)), MeasurableSet Ξ → IsBounded Ξ →
        ∀ p : ℝ, (Q : ℝ) / β < p → ∃ C : ℝ, 0 < C ∧
          ∀ f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞, Measurable f →
            Function.support f ⊆ K → eLpNorm f (ENNReal.ofReal p) volume ≤ 1 →
              mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
                (fun g : Line m ↦ localXRay f g.2 g.1)) (ENNReal.ofReal Q)
                  (ENNReal.ofReal ((Q : ℝ) / (β - 1))) volume volume ≤ ENNReal.ofReal C := by
  obtain ⟨Q, hQ, hind⟩ := exists_indicator_mixedNorm_bound m hβ hβ2
  refine ⟨Q, hQ, fun K hK Ξ hΞ hΞb p hp ↦ ?_⟩
  have hβ1 : 1 < β := projectionExponent_mem.1.trans hβ
  have hβ0 : 0 < β := by linarith
  have hQreal : (2 : ℝ) < Q := by exact_mod_cast hQ
  have hQ0 : 0 < (Q : ℝ) := by linarith
  have hp0 : 0 < p := (div_pos hQ0 hβ0).trans hp
  have hprod : (Q : ℝ) < β * p := by
    have h := (div_lt_iff₀ hβ0).mp hp
    nlinarith
  have hratio : (Q : ℝ) / (β * p) < 1 := (div_lt_one (mul_pos hβ0 hp0)).mpr hprod
  obtain ⟨θ, hθlow, hθ1⟩ := exists_between hratio
  have hθ : 0 < θ := (div_pos hQ0 (mul_pos hβ0 hp0)).trans hθlow
  have he : 0 < β * θ / Q := div_pos (mul_pos hβ0 hθ) hQ0
  have hpe : 1 < p * (β * θ / Q) := by
    rw [← mul_div_assoc, lt_div_iff₀ hQ0]
    have h := (div_lt_iff₀ (mul_pos hβ0 hp0)).mp hθlow
    nlinarith
  obtain ⟨C, hC, hbound⟩ := hind K hK Ξ hΞ hΞb θ hθ hθ1
  have hq : 1 ≤ ENNReal.ofReal (Q : ℝ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hr : 1 ≤ ENNReal.ofReal ((Q : ℝ) / (β - 1)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ (by linarith : 0 < β - 1)).mpr (by linarith))
  exact exists_normalized_bound_of_indicator hK.measure_lt_top.ne hΞ hq hr
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hC hp0 he hpe hbound

end NKBesicovitch.XRay
