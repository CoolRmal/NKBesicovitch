/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.NodeMass

/-!
# The one-node selection exponent

For base triples separated by `|I|/100`, one corner node contributes
parameter measure at least a positive constant times
`|I|^(4 + (8 + 6L)A)`. Here `L` is the input label count and `A` its
selection-volume exponent. The constant is uniform over the time set
and the separated base triple.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

private theorem node_volume_power_aux (c x : ℝ) (A L : ℕ) :
    (c * (x / 100 * x ^ 5 / 8000000) ^ A) ^ L *
      (c * (x / 100 * x ^ 7 / 320000000000) ^ A) * (x / 100 * x ^ 3 / 160000) =
      ((c * (1 / 800000000 : ℝ) ^ A) ^ L *
        (c * (1 / 32000000000000 : ℝ) ^ A) / 16000000) * x ^ (4 + (8 + 6 * L) * A) := by
  have h₁ : x / 100 * x ^ 5 / 8000000 = (1 / 800000000 : ℝ) * x ^ 6 := by ring
  have h₂ : x / 100 * x ^ 7 / 320000000000 = (1 / 32000000000000 : ℝ) * x ^ 8 := by ring
  have h₃ : x / 100 * x ^ 3 / 160000 = x ^ 4 / 16000000 := by ring
  rw [h₁, h₂, h₃]
  simp only [mul_pow, pow_add, pow_mul]
  ring

/-- The explicit polynomial selection-volume exponent contributed by one corner node. -/
theorem exists_node_volume_constant {m D L : ℕ} {β : ℝ}
    (S : SelectableProjectionScheme m β D L) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
      ∀ p ∈ separatedTriples I ((volume I).toReal / 100),
        ENNReal.ofReal (C * (volume I).toReal ^ (4 + (8 + 6 * L) * S.volumeExponent)) ≤
          volume (S.cornerNodeParameters I p.1.1 p.1.2 p.2 ((volume I).toReal / 100)) := by
  let C := (S.lowerConstant * (1 / 800000000 : ℝ) ^ S.volumeExponent) ^ L *
    (S.lowerConstant * (1 / 32000000000000 : ℝ) ^ S.volumeExponent) / 16000000
  have hc := S.lowerConstant_pos
  refine ⟨C, by positivity, fun I hI hIunit hIpos p hp ↦ ?_⟩
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  obtain ⟨ha, hb, hcI, hab, _, _⟩ := mem_separatedTriples.mp hp
  have h := S.volume_cornerNodeParameters_lower hI hIunit hIpos
    (hIunit ha) (hIunit hb) (hIunit hcI) (by positivity) hab
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), node_volume_power_aux] at h
  exact h

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
