/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CodeMarginal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Projection bounds on pair-code fibers

The double-projection density lower bound on a refinement bounds the first-line
projection on every code fiber. The statement uses outer measure and does not
divide by the threshold; it therefore covers zero and infinite values too.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- The exact, division-free form of the supplied manuscript's pair-fiber projection bound. -/
theorem mul_volume_projection_pairFiber_le {a b c t : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (hta : t ≠ a) (htb : t ≠ b) {W₀ W₁ : Set (PairCoordinates m)}
    (hW₀ : MeasurableSet W₀) (ℓ : ℝ≥0∞)
    (hℓ : ∀ p ∈ W₁, ℓ ≤ pairDensity a t (dualTime a b c t) W₀
      (pairProjections a t (dualTime a b c t) p)) (z : EuclideanSpace ℝ (Fin m)) :
    (ENNReal.ofReal |(((b - a) / (dualTime a b c t - a)) ^ m)⁻¹| * ℓ) *
      volume (atHeight t '' pairFiber a b c W₁ z) ≤ codeDensity a b c W₀ z := by
  let f : EuclideanSpace ℝ (Fin m) → ℝ≥0∞ := fun y ↦ pairDensity a t (dualTime a b c t) W₀
    (y, ((b - a) / (dualTime a b c t - a))⁻¹ •
      (z - (c * (b - a) / (t - a)) • y))
  have hf : Measurable f :=
    (measurable_pairDensity a t (dualTime a b c t) hW₀).comp (by fun_prop)
  have hsub : atHeight t '' pairFiber a b c W₁ z ⊆ {y | ℓ ≤ f y} := by
    rintro y ⟨g, hg, rfl⟩
    have h := hℓ (pairFromCode a b c g z) hg
    rwa [pairProjections_pairFromCode_dual hab hc hta htb] at h
  have hi : ℓ * volume (atHeight t '' pairFiber a b c W₁ z) ≤ ∫⁻ y, f y :=
    (mul_le_mul le_rfl (measure_mono hsub) bot_le bot_le).trans
      (mul_meas_ge_le_lintegral hf ℓ)
  rw [codeDensity_eq_marginal hab hc hta htb hW₀, mul_assoc]
  exact mul_le_mul le_rfl hi bot_le bot_le

end NKBesicovitch.Projection
