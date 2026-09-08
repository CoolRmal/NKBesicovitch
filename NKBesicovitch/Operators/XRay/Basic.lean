/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Defs
public import NKBesicovitch.Projection.Defs
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measurable line-time incidence for the local X-ray transform

For an indicator function, the local transform is exactly the measure of
the times at which the line meets the set. This family of time sets is
jointly Borel, as required by the selectable projection scheme.
-/

@[expose] public section

open MeasureTheory Set NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {m : ℕ}

/-- Times in the unit interval at which the line meets the spatial set. -/
def lineTimes (E : Set (EuclideanSpace ℝ (Fin m) × ℝ)) (g : Line m) : Set ℝ :=
  Icc 0 1 ∩ (fun t ↦ (atHeight t g, t)) ⁻¹' E

theorem measurableSet_lineTimes_family {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) : MeasurableSet {p : Line m × ℝ | p.2 ∈ lineTimes E p.1} := by
  have h := ((measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1)).preimage
    (measurable_snd : Measurable (Prod.snd : Line m × ℝ → ℝ))).inter
    (hE.preimage (f := fun p : Line m × ℝ ↦ (atHeight p.2 p.1, p.2))
      (by unfold atHeight; fun_prop))
  simpa only [lineTimes, preimage, mem_ofPred_eq, mem_inter_iff, ofPred_and] using h

theorem measurableSet_lineTimes {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) (g : Line m) : MeasurableSet (lineTimes E g) :=
  (measurableSet_lineTimes_family hE).preimage (f := fun t ↦ (g, t)) (by fun_prop)

theorem localXRay_indicator_eq_volume_lineTimes {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) (g : Line m) :
    localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1 = volume (lineTimes E g) := by
  unfold localXRay
  rw [← lintegral_indicator measurableSet_Icc,
    ← lintegral_indicator_fun_one (measurableSet_lineTimes hE g)]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Icc (0 : ℝ) 1 <;>
    by_cases he : (atHeight t g, t) ∈ E <;>
      simp_all [lineTimes, atHeight]

theorem volume_lineTimes_le_one (E : Set (EuclideanSpace ℝ (Fin m) × ℝ)) (g : Line m) :
    volume (lineTimes E g) ≤ 1 := by
  simpa only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one] using
    measure_mono (μ := volume) (show lineTimes E g ⊆ Icc 0 1 from inter_subset_left)

theorem measurable_localXRay {f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun g : Line m ↦ localXRay f g.2 g.1) := by
  have h : Measurable (fun p : Line m × ℝ ↦ f (atHeight p.2 p.1, p.2)) :=
    hf.comp (by unfold atHeight; fun_prop)
  exact h.lintegral_prod_right' (ν := volume.restrict (Icc (0 : ℝ) 1))

end NKBesicovitch.XRay
