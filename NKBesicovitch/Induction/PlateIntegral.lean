/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.PlateVolume
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Comparing plate integrals with lower-dimensional X-ray averages

Tonelli and the cylinder containment bound a lifted plate integral by
the lower-dimensional plate integral of the full X-ray transform.
The volume comparison contributes the uniform factor `2^m` to the
normalized averages, including extended-valued inputs and integrals.
-/

public section

open MeasureTheory Set Metric NKBesicovitch.Grassmannian
open scoped ENNReal

namespace NKBesicovitch.Induction

variable {n m k : ℕ} {v : EuclideanSpace ℝ (Fin n)}

theorem lintegral_plate_normalLift_le (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    (a : EuclideanSpace ℝ (Fin m) × ℝ) (δ : ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in plate δ (normalLift hv b V).val (normalCoordinatesWithBasis hv b a), f z) ≤
      ∫⁻ x in plate δ V.val a.1, ∫⁻ t : ℝ, f (normalCoordinatesWithBasis hv b (x, t)) := by
  have hs : MeasurableSet
      (plate δ (normalLift hv b V).val (normalCoordinatesWithBasis hv b a)) :=
    isOpen_thickening.measurableSet
  rw [← (measurePreserving_normalCoordinatesWithBasis hv b).setLIntegral_comp_preimage hs hf]
  calc
    _ ≤ ∫⁻ z in plate δ V.val a.1 ×ˢ univ, f (normalCoordinatesWithBasis hv b z) :=
      lintegral_mono_set (preimage_plate_normalCoordinates_subset hv b V a δ)
    _ = _ := by
      rw [Measure.volume_eq_prod, setLIntegral_prod]
      · simp only [Measure.restrict_univ]
      · exact (hf.comp (normalCoordinatesWithBasis hv b).continuous.measurable).aemeasurable

theorem plateAverage_normalLift_le (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    (a : EuclideanSpace ℝ (Fin m) × ℝ) {δ : ℝ} (hδ : 0 < δ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in plate δ (normalLift hv b V).val (normalCoordinatesWithBasis hv b a), f z) /
        volume (plate δ (normalLift hv b V).val (normalCoordinatesWithBasis hv b a)) ≤
      (2 : ℝ≥0∞) ^ m *
        ((∫⁻ x in plate δ V.val a.1, ∫⁻ t : ℝ, f (normalCoordinatesWithBasis hv b (x, t))) /
          volume (plate δ V.val a.1)) := by
  have hc0 : (2 : ℝ≥0∞)⁻¹ ^ m ≠ 0 := pow_ne_zero _ (by simp)
  have hcfin : (2 : ℝ≥0∞)⁻¹ ^ m ≠ ∞ := by finiteness
  apply (ENNReal.div_le_div (lintegral_plate_normalLift_le hv b V a δ hf)
    (half_pow_mul_volume_plate_le_centers hv b V hδ a.1
      (normalCoordinatesWithBasis hv b a))).trans_eq
  rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl hcfin),
    ENNReal.inv_pow, inv_inv, div_eq_mul_inv]
  ac_rfl

/-- A lifted plate maximal function is controlled by the lower-dimensional
X-ray maximal function. -/
theorem plateMaximal_normalLift_le (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (V : Grassmannian m k)
    {δ : ℝ} (hδ : 0 < δ) {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    plateMaximal δ f (normalLift hv b V) ≤ (2 : ℝ≥0∞) ^ m *
      plateMaximal δ (fun x ↦ ∫⁻ t : ℝ, f (normalCoordinatesWithBasis hv b (x, t))) V := by
  apply iSup_le
  intro z
  obtain ⟨a, rfl⟩ := (normalCoordinatesWithBasis hv b).surjective z
  apply (plateAverage_normalLift_le hv b V a hδ hf).trans
  apply mul_le_mul_right
  exact le_iSup (fun c ↦ (∫⁻ x in plate δ V.val c,
    ∫⁻ t : ℝ, f (normalCoordinatesWithBasis hv b (x, t))) / volume (plate δ V.val c)) a.1

end NKBesicovitch.Induction
