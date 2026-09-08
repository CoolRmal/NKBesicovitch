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
# Measurability of the plate maximal operator on open indicators

Pull each average back to a fixed plate by a volume-preserving rigid motion.
Fatou then gives lower semicontinuity on the orthogonal group, which descends
to the Grassmannian through its compact orbit quotient.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

theorem plate_average_indicator_eq (δ : ℝ) (u : Rotations n) (a : Space n)
    (V : Grassmannian n k) {U : Set (Space n)} (hU : MeasurableSet U) :
    (∫⁻ x in plate δ (Grassmannian.rotate u V).submodule a,
        U.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) /
      volume (plate δ (Grassmannian.rotate u V).submodule a) =
    ∫⁻ x in plate δ V.submodule 0,
      U.indicator (fun _ ↦ (volume (plate δ V.submodule 0))⁻¹) (rigidMotion u a x) := by
  have hm : Measurable (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) := measurable_const.indicator hU
  have hi := (measurePreserving_rigidMotion u a).setLIntegral_comp_preimage
    (s := plate δ (Grassmannian.rotate u V).submodule a)
    Metric.isOpen_thickening.measurableSet hm
  rw [preimage_plate_rigidMotion] at hi
  have hm' : Measurable (fun x ↦ U.indicator (fun _ ↦ (1 : ℝ≥0∞)) (rigidMotion u a x)) :=
    hm.comp (rigidMotion u a).continuous.measurable
  rw [← hi, volume_plate_rotate, div_eq_mul_inv,
    ← lintegral_mul_const (μ := volume.restrict (plate δ V.submodule 0)) _ hm']
  simp only [← Set.indicator_mul_const, one_mul]

theorem lowerSemicontinuous_plate_average_orbit (δ : ℝ) (a : Space n)
    (V : Grassmannian n k) {U : Set (Space n)} (hU : IsOpen U) :
    LowerSemicontinuous (fun u : Rotations n ↦
      (∫⁻ x in plate δ (Grassmannian.rotate u V).submodule a,
          U.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) /
        volume (plate δ (Grassmannian.rotate u V).submodule a)) := by
  simp_rw [plate_average_indicator_eq δ _ a V hU.measurableSet]
  apply lowerSemicontinuous_lintegral
  · intro u
    exact ((measurable_const.indicator hU.measurableSet).comp
      (rigidMotion u a).continuous.measurable).aemeasurable
  · intro x
    apply (hU.lowerSemicontinuous_indicator bot_le).comp
    change Continuous (fun u : Rotations n ↦ (u : Space n →L[ℝ] Space n) x + a)
    exact (continuous_subtype_val.clm_apply continuous_const).add continuous_const

theorem lowerSemicontinuous_plateMaximal_indicator (δ : ℝ) {U : Set (Space n)}
    (hU : IsOpen U) :
    LowerSemicontinuous (plateMaximal δ (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) :
      Grassmannian n k → ℝ≥0∞) := by
  by_cases h : Nonempty (Grassmannian n k)
  · obtain ⟨V⟩ := h
    have hq := Topology.IsQuotientMap.of_surjective_continuous
      (Grassmannian.orbit_surjective V) (Grassmannian.continuous_orbit V)
    have hl : LowerSemicontinuous (fun u : Rotations n ↦
        plateMaximal δ (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) (Grassmannian.rotate u V)) :=
      lowerSemicontinuous_iSup fun a ↦ lowerSemicontinuous_plate_average_orbit δ a V hU
    refine lowerSemicontinuous_iff_isOpen_preimage.mpr fun r ↦ ?_
    exact hq.isCoinducing.isOpen_preimage.mp (hl.isOpen_preimage r)
  · have : IsEmpty (Grassmannian n k) := not_nonempty_iff.mp h
    exact fun V ↦ isEmptyElim V

theorem measurable_plateMaximal_indicator (δ : ℝ) {U : Set (Space n)} (hU : IsOpen U) :
    Measurable (plateMaximal δ (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) :
      Grassmannian n k → ℝ≥0∞) :=
  (lowerSemicontinuous_plateMaximal_indicator δ hU).measurable

end NKBesicovitch
