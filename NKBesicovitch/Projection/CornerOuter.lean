/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerDensity

/-!
# The outer density of a corner

The outer data combine the first line's position and the inner-pair code.
The exact marginal identity holds for the explicit pointwise representatives.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- First-line position and inner-pair code at an outer height. -/
noncomputable def cornerOuterData (a b c κ u : ℝ) (p : CornerCoordinates m) : Line m :=
  (atHeight u (cornerFirst a p), pairCode b a (cornerInnerCoefficient a c κ u) (cornerInner b p))

theorem continuous_cornerOuterData (a b c κ u : ℝ) :
    Continuous (cornerOuterData (m := m) a b c κ u) := by
  unfold cornerOuterData cornerInner pairCode cornerFirst lineAt atHeight
  fun_prop

theorem cornerOuterData_eq {a b c κ u : ℝ} (hua : u ≠ a) (p : CornerCoordinates m) :
    cornerOuterData a b c κ u p = (atHeight u (cornerFirst a p),
      cornerCode a b c κ p - cornerOuterCoefficient a c κ u • atHeight u (cornerFirst a p)) := by
  apply Prod.ext
  · rfl
  · change pairCode b a (cornerInnerCoefficient a c κ u) (cornerInner b p) = _
    rw [cornerCode_eq_outer_add_inner hua]
    module

theorem cornerOuterData_cornerFromCode {a b c κ u : ℝ} (hab : a ≠ b) (hua : u ≠ a)
    (g : Line m) (x z : Space m) :
    cornerOuterData a b c κ u (cornerFromCode a b c κ g x z) =
      (atHeight u g, z - cornerOuterCoefficient a c κ u • atHeight u g) := by
  rw [cornerOuterData_eq hua, first_cornerFromCode, cornerCode_cornerFromCode hab]

/-- Density of the first-line position and inner-pair code. -/
noncomputable def cornerOuterDensity (a b c κ u : ℝ) (D : Set (CornerCoordinates m))
    (yz : Line m) : ℝ≥0∞ :=
  codeJacobian m a b ^ 2 * ∫⁻ p : Line m,
    D.indicator 1 (cornerFromCode a b c κ (lineAt u yz.1 p.1) p.2
      (cornerOuterCoefficient a c κ u • yz.1 + yz.2))

theorem measurable_cornerOuterDensity (a b c κ u : ℝ) {D : Set (CornerCoordinates m)}
    (hD : MeasurableSet D) : Measurable (cornerOuterDensity a b c κ u D) := by
  have hf : Measurable (fun p : Line m × Line m ↦ D.indicator (1 : CornerCoordinates m → ℝ≥0∞)
      (cornerFromCode a b c κ (lineAt u p.1.1 p.2.1) p.2.2
        (cornerOuterCoefficient a c κ u • p.1.1 + p.1.2))) :=
    (measurable_const.indicator hD).comp (by unfold cornerFromCode lineAt atHeight; fun_prop)
  exact measurable_const.mul hf.lintegral_prod_right'

theorem cornerOuterDensity_at_code (a b c κ u : ℝ) {D : Set (CornerCoordinates m)}
    (hD : MeasurableSet D) (y z : Space m) :
    cornerOuterDensity a b c κ u D (y, z - cornerOuterCoefficient a c κ u • y) =
      codeJacobian m a b ^ 2 * ∫⁻ ξ, cornerFirstDensity a b c κ D z (lineAt u y ξ) := by
  have hf : Measurable (fun p : Line m ↦ D.indicator (1 : CornerCoordinates m → ℝ≥0∞)
      (cornerFromCode a b c κ (lineAt u y p.1) p.2 z)) :=
    (measurable_const.indicator hD).comp (by unfold cornerFromCode lineAt atHeight; fun_prop)
  unfold cornerOuterDensity cornerFirstDensity
  simp only [add_sub_cancel]
  rw [Measure.volume_eq_prod, lintegral_prod _ hf.aemeasurable]

/-- The exact outer marginal identity, at every corner-code value. -/
theorem lintegral_cornerOuterDensity_at_code (a b c κ u : ℝ) {D : Set (CornerCoordinates m)}
    (hD : MeasurableSet D) (z : Space m) :
    (∫⁻ y, cornerOuterDensity a b c κ u D
      (y, z - cornerOuterCoefficient a c κ u • y)) = cornerDensity a b c κ D z := by
  simp_rw [cornerOuterDensity_at_code a b c κ u hD]
  have hq : codeJacobian m a b ^ 2 ≠ ∞ := ENNReal.pow_ne_top (codeJacobian_ne_top m a b)
  rw [lintegral_const_mul' _ _ hq,
    lintegral_lineAt u (measurable_cornerFirstDensity a b c κ hD z),
    cornerDensity_eq_lintegral a b c κ hD]

end NKBesicovitch.Projection
