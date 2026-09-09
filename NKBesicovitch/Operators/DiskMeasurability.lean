/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.DiskRotation
public import NKBesicovitch.Operators.Semicontinuity
public import NKBesicovitch.Grassmannian.Topology
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Measurability of disk maxima

For lower semicontinuous inputs, Fatou applies after rotating each disk
back to a fixed intrinsic unit ball. Proper descent through the orbit
map proves joint lower semicontinuity for parameterized input families.
This covers both smooth inputs and indicators of open sets.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NKBesicovitch

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {n k : ℕ}

private lemma lowerSemicontinuous_diskMaximal_family_orbit_aux (V : Grassmannian n k)
    {f : X × EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun z : X × Rotations n ↦
      diskMaximal (fun x ↦ f (z.1, x)) (Grassmannian.rotate z.2 V)) := by
  simp_rw [diskMaximal_rotate]
  simp only [diskMaximal, diskAverage, Function.comp_apply]
  apply lowerSemicontinuous_iSup
  intro a
  change LowerSemicontinuous ((fun s : ℝ≥0∞ ↦ s / volume (closedBall (0 : V.val) 1)) ∘
    (fun z : X × Rotations n ↦ ∫⁻ w in closedBall (0 : V.val) 1,
      f (z.1, Unitary.linearIsometryEquiv z.2 (a + w))))
  apply (ENNReal.continuous_div_const _
    (measure_closedBall_pos volume _ zero_lt_one).ne').comp_lowerSemicontinuous
  · apply lowerSemicontinuous_lintegral
    · intro z
      exact (hf.comp (continuous_const.prodMk ((Unitary.linearIsometryEquiv z.2).continuous.comp
        (continuous_const.add continuous_subtype_val)))).measurable.aemeasurable
    · intro w
      exact hf.comp (continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).clm_apply continuous_const))
  · intro s t h
    exact mul_le_mul_left h _

/-- Lower semicontinuous input families have jointly lower semicontinuous disk maxima. -/
theorem lowerSemicontinuous_diskMaximal_family
    {f : X × EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun z : X × Grassmannian n k ↦
      diskMaximal (fun x ↦ f (z.1, x)) z.2) := by
  by_cases h : Nonempty (Grassmannian n k)
  · obtain ⟨V⟩ := h
    let q := Prod.map (id : X → X) (fun u : Rotations n ↦ Grassmannian.rotate u V)
    have hq : Topology.IsQuotientMap q :=
      (isProperMap_id.prodMap
        (Grassmannian.continuous_orbit V).isProperMap).isClosedMap.isQuotientMap
        (continuous_id.prodMap (Grassmannian.continuous_orbit V))
        (Function.surjective_id.prodMap (Grassmannian.orbit_surjective V))
    have hl := lowerSemicontinuous_diskMaximal_family_orbit_aux V hf
    refine lowerSemicontinuous_iff_isOpen_preimage.mpr fun r ↦ ?_
    exact hq.isCoinducing.isOpen_preimage.mp (hl.isOpen_preimage r)
  · have : IsEmpty (Grassmannian n k) := not_nonempty_iff.mp h
    exact fun z ↦ isEmptyElim z.2

omit [TopologicalSpace X] [FirstCountableTopology X] in
/-- The disk maximum of a lower semicontinuous input is lower semicontinuous in direction. -/
theorem lowerSemicontinuous_diskMaximal {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : LowerSemicontinuous f) : LowerSemicontinuous (diskMaximal f (k := k)) := by
  have h := lowerSemicontinuous_diskMaximal_family
    (f := fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦ f z.2)
    (hf.comp continuous_snd) (k := k)
  have h' := h.comp (continuous_const.prodMk continuous_id :
    Continuous (fun V : Grassmannian n k ↦ ((0 : EuclideanSpace ℝ (Fin n)), V)))
  simpa only [Function.comp_def] using h'

end NKBesicovitch
