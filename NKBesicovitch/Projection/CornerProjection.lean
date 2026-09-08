/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerOuter
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Projection bounds on corner-code fibers

A lower bound on outer density controls every first-line projection of a
corner-code fiber. The division-free statement uses outer measure, so it
does not require measurability of the existential projection image.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- The corner-fiber projection bound from the exact outer marginal. -/
theorem mul_volume_projection_cornerFiber_le {a b c κ u : ℝ} (hab : a ≠ b)
    (hua : u ≠ a) {D₀ D₁ : Set (CornerCoordinates m)} (hD₀ : MeasurableSet D₀)
    (τ : ℝ≥0∞) (hτ : ∀ p ∈ D₁,
      τ ≤ cornerOuterDensity a b c κ u D₀ (cornerOuterData a b c κ u p)) (z : Space m) :
    τ * volume (atHeight u '' cornerFiber a b c κ D₁ z) ≤ cornerDensity a b c κ D₀ z := by
  let f : Space m → ℝ≥0∞ := fun y ↦
    cornerOuterDensity a b c κ u D₀ (y, z - cornerOuterCoefficient a c κ u • y)
  have hf : Measurable f :=
    (measurable_cornerOuterDensity a b c κ u hD₀).comp (by fun_prop)
  have hsub : atHeight u '' cornerFiber a b c κ D₁ z ⊆ {y | τ ≤ f y} := by
    rintro y ⟨g, ⟨x, hx⟩, rfl⟩
    have h := hτ (cornerFromCode a b c κ g x z) hx
    rwa [cornerOuterData_cornerFromCode hab hua] at h
  calc
    _ ≤ τ * volume {y | τ ≤ f y} := mul_le_mul le_rfl (measure_mono hsub) bot_le bot_le
    _ ≤ ∫⁻ y, f y := mul_meas_ge_le_lintegral hf τ
    _ = _ := lintegral_cornerOuterDensity_at_code a b c κ u hD₀ z

/-- The same bound applies to the Borel positive first-line family. -/
theorem mul_volume_projection_positiveCornerFiber_le {a b c κ u : ℝ} (hab : a ≠ b)
    (hua : u ≠ a) {D₀ D₁ : Set (CornerCoordinates m)} (hD₀ : MeasurableSet D₀)
    (τ : ℝ≥0∞) (hτ : ∀ p ∈ D₁,
      τ ≤ cornerOuterDensity a b c κ u D₀ (cornerOuterData a b c κ u p)) (z : Space m) :
    τ * volume (atHeight u '' positiveCornerFiber a b c κ D₁ z) ≤
      cornerDensity a b c κ D₀ z := by
  exact (mul_le_mul le_rfl (measure_mono
    (Set.image_mono (positiveCornerFiber_subset a b c κ D₁ z))) bot_le bot_le).trans
      (mul_volume_projection_cornerFiber_le hab hua hD₀ τ hτ z)

end NKBesicovitch.Projection
