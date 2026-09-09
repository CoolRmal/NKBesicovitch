/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.TranslatedAverages
public import NKBesicovitch.Operators.PlateTranslation
public import NKBesicovitch.Geometry.Plates

/-!
# Positive kernel bounds from plate maxima

Translation comparability on a plate converts integration against a positive
kernel into a bound by the plate maximal function times the kernel mass.
The bound includes inputs and maximal functions with infinite values.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch

/-- A kernel comparable under plate-sized translations is controlled by the plate maximum. -/
theorem lintegral_mul_le_plateMaximal {n k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (V : Grassmannian n k) {f K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) (hK : Measurable K) {C : ℝ≥0}
    (hshift : ∀ z t, t ∈ plate δ V.val 0 → K z ≤ C * K (z - t)) :
    (∫⁻ z, f z * K z) ≤ C * plateMaximal δ f V * ∫⁻ z, K z := by
  apply lintegral_mul_le_of_translated_averages volume hf hK (S := plate δ V.val 0)
    isOpen_thickening.measurableSet
    (volume_plate_pos hδ V.val 0).ne' (volume_plate_lt_top δ V.val 0).ne hshift
  intro z
  apply (ENNReal.div_le_iff (volume_plate_pos hδ V.val 0).ne'
    (volume_plate_lt_top δ V.val 0).ne).mp
  have h := le_iSup (fun a ↦ (∫⁻ x in plate δ V.val a, f x) / volume (plate δ V.val a)) (0 + z)
  rw [plateAverage_add_right] at h
  simpa only [add_comm, plateMaximal] using h

end NKBesicovitch
