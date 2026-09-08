/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CodeCoordinates

/-!
# The density of the pair code

The explicit first-line fiber gives a pointwise representative of the code
density. Its integral equals the intrinsic volume of the pair family.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Pair-code density, normalized by the exact second-slope Jacobian. -/
noncomputable def codeDensity (a b c : ℝ) (W : Set (PairCoordinates m))
    (z : EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  codeJacobian m a b * volume (pairFiber a b c W z)

theorem codeDensity_eq_lintegral (a b c : ℝ) {W : Set (PairCoordinates m)}
    (hW : MeasurableSet W) (z : EuclideanSpace ℝ (Fin m)) :
    codeDensity a b c W z = codeJacobian m a b *
      ∫⁻ g, W.indicator 1 (pairFromCode a b c g z) := by
  unfold codeDensity
  congr 1
  rw [← lintegral_indicator_one (measurableSet_pairFiber a b c hW z)]
  apply lintegral_congr
  intro g
  simp only [Set.indicator, pairFiber]
  rfl

theorem measurable_codeDensity (a b c : ℝ) {W : Set (PairCoordinates m)}
    (hW : MeasurableSet W) : Measurable (codeDensity a b c W) := by
  have hf : Measurable (fun p : Line m × EuclideanSpace ℝ (Fin m) ↦
      W.indicator (1 : PairCoordinates m → ℝ≥0∞) (pairFromCode a b c p.1 p.2)) :=
    (measurable_const.indicator hW).comp (continuous_pairFromCode a b c).measurable
  have he : codeDensity a b c W = fun z ↦
      codeJacobian m a b * ∫⁻ g, W.indicator 1 (pairFromCode a b c g z) :=
    funext (codeDensity_eq_lintegral a b c hW)
  rw [he]
  exact measurable_const.mul (hf.lintegral_prod_left' (μ := volume))

theorem lintegral_codeDensity {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) :
    (∫⁻ z, codeDensity a b c W z) = volume W := by
  let f : Line m × EuclideanSpace ℝ (Fin m) → ℝ≥0∞ := fun p ↦
    W.indicator 1 (pairFromCode a b c p.1 p.2)
  have hf : Measurable f :=
    (measurable_const.indicator hW).comp (continuous_pairFromCode a b c).measurable
  have hi := (measurePreserving_codeCoordinates (m := m) hab c).lintegral_comp hf
  calc
    (∫⁻ z, codeDensity a b c W z) = codeJacobian m a b * ∫⁻ z, ∫⁻ g, f (g, z) := by
      simp_rw [codeDensity_eq_lintegral a b c hW]
      exact lintegral_const_mul _ (hf.lintegral_prod_left' (μ := volume))
    _ = codeJacobian m a b * ∫⁻ p, f p := by
      congr 1
      simpa only [Measure.volume_eq_prod] using
        (lintegral_prod_symm' (μ := (volume : Measure (Line m)))
          (ν := (volume : Measure (EuclideanSpace ℝ (Fin m)))) f hf).symm
    _ = ∫⁻ p, f p ∂(codeJacobian m a b • volume) := by
      rw [lintegral_smul_measure, smul_eq_mul]
    _ = ∫⁻ p, W.indicator 1 p := by
      rw [← hi]
      apply lintegral_congr
      intro p
      change W.indicator 1 (pairFromCode a b c (lineAt a p.1 p.2.1) (pairCode a b c p)) = _
      rw [pairFromCode_pairCode hab]
    _ = volume W := lintegral_indicator_one hW

end NKBesicovitch.Projection
