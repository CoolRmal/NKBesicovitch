/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.BoundedFamilies
public import NKBesicovitch.Projection.FiberCutoff
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Continuous cumulative masses of slice fibers

Intersect each slope fiber with expanding closed balls. Spheres have zero
Lebesgue measure in positive dimension, so these cumulative masses are
continuous in the radius and measurable in the slice point.
-/

@[expose] public section

open MeasureTheory Set Bornology Metric Filter unitInterval
open scoped ENNReal Topology

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem continuous_volume_inter_closedBall [Nonempty (Fin m)] {S : Set (EuclideanSpace ℝ (Fin m))}
    (hS : MeasurableSet S) (hfin : volume S ≠ ∞) :
    Continuous (fun r : ℝ ↦ volume (S ∩ closedBall 0 r)) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  apply tendsto_measure_of_ae_tendsto_indicator (𝓝 r)
    (hS.inter measurableSet_closedBall) (fun _ ↦ hS.inter measurableSet_closedBall)
    hS hfin (Eventually.of_forall fun _ ↦ inter_subset_left)
  have hs : ∀ᵐ ξ : EuclideanSpace ℝ (Fin m), ξ ∉ sphere 0 r := by
    apply ae_iff.mpr
    simpa only [not_not, sphere, mem_ofPred_eq, dist_zero_right] using
      Measure.addHaar_sphere (volume : Measure (EuclideanSpace ℝ (Fin m))) 0 r
  filter_upwards [hs] with ξ hξ
  have hne : ‖ξ‖ ≠ r := by simpa [mem_sphere, dist_zero_right] using hξ
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · filter_upwards [Ioi_mem_nhds hlt] with r' hr'
    change ‖ξ‖ < r' at hr'
    simp [mem_closedBall, dist_zero_right, hlt.le, hr'.le]
  · filter_upwards [Iio_mem_nhds hlt] with r' hr'
    change r' < ‖ξ‖ at hr'
    simp [mem_closedBall, dist_zero_right, hlt.not_ge, hr'.not_ge]

/-- Mass inside a slope ball whose radius ranges from zero to `R`. -/
noncomputable def sliceBallMass (a : ℝ) (G : Set (Line m)) (R : ℝ)
    (y : EuclideanSpace ℝ (Fin m)) (t : I) : ℝ≥0∞ :=
  volume (lineAt a y ⁻¹' G ∩ closedBall 0 (R * (t : ℝ)))

theorem measurable_sliceBallMass (a R : ℝ) {G : Set (Line m)} (hG : MeasurableSet G) (t : I) :
    Measurable (fun y ↦ sliceBallMass a G R y t) := by
  have hs : MeasurableSet {p : Line m | lineAt a p.1 p.2 ∈ G ∧ p.2 ∈ closedBall 0 (R * (t : ℝ))} :=
    (hG.preimage (by unfold lineAt; fun_prop)).inter
      (measurableSet_closedBall.preimage measurable_snd)
  exact measurable_measure_prodMk_left (ν := (volume : Measure (EuclideanSpace ℝ (Fin m)))) hs

theorem monotone_sliceBallMass (a : ℝ) (G : Set (Line m)) {R : ℝ} (hR : 0 ≤ R)
    (y : EuclideanSpace ℝ (Fin m)) :
    Monotone (sliceBallMass a G R y) := by
  intro s t hst
  exact measure_mono (inter_subset_inter_right _
    (closedBall_subset_closedBall (mul_le_mul_of_nonneg_left hst hR)))

theorem continuous_sliceBallMass [Nonempty (Fin m)] (a R : ℝ)
    {G : Set (Line m)} (hG : MeasurableSet G) (hGb : IsBounded G) (y : EuclideanSpace ℝ (Fin m)) :
    Continuous (sliceBallMass a G R y) := by
  have hs : MeasurableSet (lineAt a y ⁻¹' G) := hG.preimage (by unfold lineAt; fun_prop)
  have hb : IsBounded (lineAt a y ⁻¹' G) := hGb.image_snd.subset
    (fun ξ hξ ↦ ⟨lineAt a y ξ, hξ, rfl⟩)
  exact (continuous_volume_inter_closedBall hs hb.measure_lt_top.ne).comp (by fun_prop)

theorem sliceBallMass_zero [Nonempty (Fin m)] (a R : ℝ) (G : Set (Line m))
    (y : EuclideanSpace ℝ (Fin m)) :
    sliceBallMass a G R y 0 = 0 := by
  unfold sliceBallMass
  change volume (lineAt a y ⁻¹' G ∩ closedBall 0 (R * 0)) = 0
  rw [mul_zero, closedBall_zero]
  exact measure_mono_null inter_subset_right (measure_singleton _)

theorem sliceBallMass_one (a R : ℝ) {G : Set (Line m)}
    (hR : ∀ g ∈ G, ‖g.2‖ ≤ R) (y : EuclideanSpace ℝ (Fin m)) :
    sliceBallMass a G R y 1 = sliceMultiplicity a G y := by
  unfold sliceBallMass sliceMultiplicity
  change volume (lineAt a y ⁻¹' G ∩ closedBall 0 (R * 1)) = _
  rw [mul_one]
  congr 1
  apply inter_eq_left.mpr
  intro ξ hξ
  simpa only [mem_closedBall, dist_zero_right, lineAt] using hR (lineAt a y ξ) hξ

end NKBesicovitch.Projection
