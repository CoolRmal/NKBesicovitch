/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.PlateMeasurability
public import NKBesicovitch.Operators.PlateRotation
public import NKBesicovitch.Geometry.Plates
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Plate maxima of continuous families

Pulling a rotated plate back to a fixed plate gives lower semicontinuity
jointly in the input parameter and the rotation. The proper orbit map
then descends this property to the Grassmannian. Taking the supremum
over centers preserves lower semicontinuity.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {n k : ℕ}

private lemma lowerSemicontinuous_plateMaximal_family_orbit_aux {δ : ℝ} (hδ : 0 < δ)
    (V : Grassmannian n k) {f : X × EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Continuous f) :
    LowerSemicontinuous (fun z : X × Rotations n ↦
      plateMaximal δ (fun x ↦ f (z.1, x)) (Grassmannian.rotate z.2 V)) := by
  simp_rw [plateMaximal_rotate]
  simp only [plateMaximal, Function.comp_apply]
  apply lowerSemicontinuous_iSup
  intro a
  change LowerSemicontinuous ((fun s : ℝ≥0∞ ↦ s / volume (plate δ V.val a)) ∘
    (fun z : X × Rotations n ↦
      ∫⁻ x in plate δ V.val a, f (z.1, Unitary.linearIsometryEquiv z.2 x)))
  apply (ENNReal.continuous_div_const _
    (volume_plate_pos hδ V.val a).ne').comp_lowerSemicontinuous
  · apply lowerSemicontinuous_lintegral
    · intro z
      exact (hf.comp (continuous_const.prodMk
        (Unitary.linearIsometryEquiv z.2).continuous)).measurable.aemeasurable
    · intro x
      exact (hf.comp (continuous_fst.prodMk ((continuous_subtype_val.comp
        continuous_snd).clm_apply continuous_const))).lowerSemicontinuous
  · intro s t h
    exact mul_le_mul_left h _

/-- A continuous family has plate maxima jointly lower semicontinuous in parameter and direction. -/
theorem lowerSemicontinuous_plateMaximal_family {δ : ℝ} (hδ : 0 < δ)
    {f : X × EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Continuous f) :
    LowerSemicontinuous (fun z : X × Grassmannian n k ↦
      plateMaximal δ (fun x ↦ f (z.1, x)) z.2) := by
  by_cases h : Nonempty (Grassmannian n k)
  · obtain ⟨V⟩ := h
    let q := Prod.map (id : X → X) (fun u : Rotations n ↦ Grassmannian.rotate u V)
    have hq : Topology.IsQuotientMap q :=
      (isProperMap_id.prodMap
        (Grassmannian.continuous_orbit V).isProperMap).isClosedMap.isQuotientMap
        (continuous_id.prodMap (Grassmannian.continuous_orbit V))
        (Function.surjective_id.prodMap (Grassmannian.orbit_surjective V))
    have hl := lowerSemicontinuous_plateMaximal_family_orbit_aux hδ V hf
    refine lowerSemicontinuous_iff_isOpen_preimage.mpr fun r ↦ ?_
    exact hq.isCoinducing.isOpen_preimage.mp (hl.isOpen_preimage r)
  · have : IsEmpty (Grassmannian n k) := not_nonempty_iff.mp h
    exact fun z ↦ isEmptyElim z.2

end NKBesicovitch
