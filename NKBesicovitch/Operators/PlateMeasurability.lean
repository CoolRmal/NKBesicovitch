/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.RigidMotions
public import NKBesicovitch.Grassmannian.Topology
public import NKBesicovitch.Operators.Semicontinuity

/-!
# Measurability of the plate maximal operator

For every Borel nonnegative input, pull the moving plate indicator back by
the inverse rigid motion. Fatou gives lower semicontinuity on the orthogonal
group, which descends to the Grassmannian through its compact orbit quotient.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

private theorem lowerSemicontinuous_plate_indicator_orbit (δ : ℝ)
    (a x : EuclideanSpace ℝ (Fin n)) (V : Grassmannian n k) (c : ℝ≥0∞) :
    LowerSemicontinuous (fun u : Rotations n ↦
      (plate δ (Grassmannian.rotate u V).val a).indicator (fun _ ↦ c) x) := by
  have heq (u : Rotations n) :
      (plate δ (Grassmannian.rotate u V).val a).indicator (fun _ ↦ c) x =
        (plate δ V.val 0).indicator (fun _ ↦ c) ((rigidMotion u a).symm x) := by
    have hm : (rigidMotion u a).symm x ∈ plate δ V.val 0 ↔
        x ∈ plate δ (Grassmannian.rotate u V).val a := by
      rw [← preimage_plate_rigidMotion u a V δ]
      simp only [mem_preimage, IsometryEquiv.apply_symm_apply]
    by_cases hx : x ∈ plate δ (Grassmannian.rotate u V).val a
    · rw [indicator_of_mem hx, indicator_of_mem (hm.mpr hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (mt hm.mp hx)]
  simp_rw [heq]
  apply (Metric.isOpen_thickening.lowerSemicontinuous_indicator bot_le).comp
  change Continuous (fun u : Rotations n ↦
    ((star u : Rotations n) : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) (x - a))
  exact (continuous_subtype_val.comp continuous_star).clm_apply continuous_const

/-- Fatou's lemma applies to the moving open plate, with the input kept fixed. -/
theorem lowerSemicontinuous_plate_average_orbit (δ : ℝ) (a : EuclideanSpace ℝ (Fin n))
    (V : Grassmannian n k) {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    LowerSemicontinuous (fun u : Rotations n ↦
      (∫⁻ x in plate δ (Grassmannian.rotate u V).val a, f x) /
        volume (plate δ (Grassmannian.rotate u V).val a)) := by
  have hm (u : Rotations n) : MeasurableSet (plate δ (Grassmannian.rotate u V).val a) :=
    Metric.isOpen_thickening.measurableSet
  simp_rw [volume_plate_rotate, div_eq_mul_inv,
    ← lintegral_mul_const _ hf,
    ← lintegral_indicator (hm _)]
  apply lowerSemicontinuous_lintegral
  · intro u
    exact ((hf.mul measurable_const).indicator
      Metric.isOpen_thickening.measurableSet).aemeasurable
  · intro x
    exact lowerSemicontinuous_plate_indicator_orbit δ a x V _

/-- The plate maximal operator is lower semicontinuous for every Borel nonnegative input. -/
theorem lowerSemicontinuous_plateMaximal (δ : ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    LowerSemicontinuous (plateMaximal δ f : Grassmannian n k → ℝ≥0∞) := by
  by_cases h : Nonempty (Grassmannian n k)
  · obtain ⟨V⟩ := h
    have hq := Topology.IsQuotientMap.of_surjective_continuous
      (Grassmannian.orbit_surjective V) (Grassmannian.continuous_orbit V)
    have hl : LowerSemicontinuous (fun u : Rotations n ↦
        plateMaximal δ f (Grassmannian.rotate u V)) :=
      lowerSemicontinuous_iSup fun a ↦ lowerSemicontinuous_plate_average_orbit δ a V hf
    refine lowerSemicontinuous_iff_isOpen_preimage.mpr fun r ↦ ?_
    exact hq.isCoinducing.isOpen_preimage.mp (hl.isOpen_preimage r)
  · have : IsEmpty (Grassmannian n k) := not_nonempty_iff.mp h
    exact fun V ↦ isEmptyElim V

theorem measurable_plateMaximal (δ : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) : Measurable (plateMaximal δ f : Grassmannian n k → ℝ≥0∞) :=
  (lowerSemicontinuous_plateMaximal δ hf).measurable

theorem lowerSemicontinuous_plateMaximal_indicator (δ : ℝ) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) :
    LowerSemicontinuous (plateMaximal δ (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) :
      Grassmannian n k → ℝ≥0∞) :=
  lowerSemicontinuous_plateMaximal δ (measurable_const.indicator hU.measurableSet)

theorem measurable_plateMaximal_indicator (δ : ℝ) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) :
    Measurable (plateMaximal δ (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) :
      Grassmannian n k → ℝ≥0∞) :=
  (lowerSemicontinuous_plateMaximal_indicator δ hU).measurable

end NKBesicovitch
