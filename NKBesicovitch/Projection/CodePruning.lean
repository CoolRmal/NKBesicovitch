/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CodeRestriction

/-!
# Deleting code fibers with poor density retention

The original pair mass above codes where a refinement retains less than half
the density is at most twice the total deleted mass. Original zero-density
codes carry no pair mass. No pointwise finiteness assumption is needed.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem le_two_mul_of_add_eq_of_lt_half {x y z : ℝ≥0∞} (hadd : x + y = z)
    (hhalf : x < z / 2) : z ≤ 2 * y := by
  have hx : x ≠ ∞ := ne_top_of_lt hhalf
  have hxx : x + x ≤ x + y := by
    calc
      _ ≤ z / 2 + z / 2 := add_le_add hhalf.le hhalf.le
      _ = z := ENNReal.add_halves z
      _ = _ := hadd.symm
  have hxy := ENNReal.le_of_add_le_add_left hx hxx
  calc
    z = x + y := hadd.symm
    _ ≤ y + y := add_le_add hxy le_rfl
    _ = _ := (two_mul y).symm

theorem volume_zero_codeDensity {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) :
    volume (W ∩ {p | codeDensity a b c W (pairCode a b c p) = 0}) = 0 := by
  have hZ : MeasurableSet {z | codeDensity a b c W z = 0} :=
    measurableSet_eq_fun (measurable_codeDensity a b c hW) measurable_const
  change volume (W ∩ pairCode a b c ⁻¹' {z | codeDensity a b c W z = 0}) = 0
  rw [← setLIntegral_codeDensity hab c hW hZ]
  calc
    _ = ∫⁻ _z in {z | codeDensity a b c W z = 0}, (0 : ℝ≥0∞) :=
      setLIntegral_congr_fun hZ (fun _ hz ↦ hz)
    _ = 0 := lintegral_zero

/-- Bad retained-to-original density ratios cost at most twice the deleted pair mass. -/
theorem volume_codeDensity_lt_half_le {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {W E : Set (PairCoordinates m)} (hW : MeasurableSet W) (hE : MeasurableSet E)
    (hEW : E ⊆ W) :
    volume (W ∩ {p | codeDensity a b c E (pairCode a b c p) <
      codeDensity a b c W (pairCode a b c p) / 2}) ≤ 2 * volume (W \ E) := by
  let B := {z | codeDensity a b c E z < codeDensity a b c W z / 2}
  have hB : MeasurableSet B := measurableSet_lt (measurable_codeDensity a b c hE)
    ((measurable_codeDensity a b c hW).div_const 2)
  change volume (W ∩ pairCode a b c ⁻¹' B) ≤ _
  rw [← setLIntegral_codeDensity hab c hW hB]
  calc
    _ ≤ ∫⁻ z in B, 2 * codeDensity a b c (W \ E) z :=
      setLIntegral_mono' hB fun z hz ↦
        le_two_mul_of_add_eq_of_lt_half (codeDensity_add_sdiff a b c hE hEW z) hz
    _ ≤ ∫⁻ z, 2 * codeDensity a b c (W \ E) z :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by
      rw [lintegral_const_mul _ (measurable_codeDensity a b c (hW.diff hE)),
        lintegral_codeDensity hab c (hW.diff hE)]

/-- Adding the zero-density codes does not increase the deletion bound. -/
theorem volume_bad_codeDensity_le {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {W E : Set (PairCoordinates m)} (hW : MeasurableSet W) (hE : MeasurableSet E)
    (hEW : E ⊆ W) :
    volume (W ∩ {p | codeDensity a b c W (pairCode a b c p) = 0 ∨
      codeDensity a b c E (pairCode a b c p) <
        codeDensity a b c W (pairCode a b c p) / 2}) ≤ 2 * volume (W \ E) := by
  rw [show {p | codeDensity a b c W (pairCode a b c p) = 0 ∨
      codeDensity a b c E (pairCode a b c p) < codeDensity a b c W (pairCode a b c p) / 2} =
    {p | codeDensity a b c W (pairCode a b c p) = 0} ∪
      {p | codeDensity a b c E (pairCode a b c p) < codeDensity a b c W (pairCode a b c p) / 2}
    from rfl, inter_union_distrib_left]
  exact (measure_union_le _ _).trans (by
    rw [volume_zero_codeDensity hab c hW, zero_add]
    exact volume_codeDensity_lt_half_le hab c hW hE hEW)

end NKBesicovitch.Projection
