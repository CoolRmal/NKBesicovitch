/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.Normalized
public import NKBesicovitch.Operators.XRay.Scaling

/-!
# Strong mixed-norm estimates for the local X-ray transform

For every `β` strictly above the critical projection exponent and at
most two, some outer exponent `Q > 2` gives
`‖T f‖_(L^Q L^(Q/(β-1))) ≤ C ‖f‖_p` for every `p > Q / β`.
The support and slope sets are fixed and bounded, and the slope set
is Borel. Inputs are arbitrary Borel nonnegative extended-valued
functions supported there. The constant is independent of the input.
-/

public section

open MeasureTheory Set Bornology NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

theorem exists_strong_mixedNorm_bound (m : ℕ) [Nonempty (Fin m)] {β : ℝ}
    (hβ : projectionExponent < β) (hβ2 : β ≤ 2) :
    ∃ Q : ℕ, 2 < Q ∧ ∀ K : Set (EuclideanSpace ℝ (Fin m) × ℝ), IsBounded K →
      ∀ Ξ : Set (EuclideanSpace ℝ (Fin m)), MeasurableSet Ξ → IsBounded Ξ →
        ∀ p : ℝ, (Q : ℝ) / β < p → ∃ C : ℝ, 0 < C ∧
          ∀ f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞, Measurable f →
            Function.support f ⊆ K →
              mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
                (fun g : Line m ↦ localXRay f g.2 g.1)) (ENNReal.ofReal Q)
                  (ENNReal.ofReal ((Q : ℝ) / (β - 1))) volume volume ≤
                    ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨Q, hQ, hnormalized⟩ := exists_normalized_mixedNorm_bound m hβ hβ2
  refine ⟨Q, hQ, fun K hK Ξ hΞ hΞb p hp ↦ ?_⟩
  obtain ⟨C, hC, hbound⟩ := hnormalized K hK Ξ hΞ hΞb p hp
  exact ⟨C, hC, fun _ hf hsupport ↦ mixedNorm_localXRay_bound_of_normalized
    (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top hbound hf hsupport⟩

end NKBesicovitch.XRay
