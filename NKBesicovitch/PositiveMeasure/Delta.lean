/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.Plates

/-!
# Thickened disks inside open sets

Compactness of a unit disk gives a positive thickness inside any open superset.
The thickness may depend on the direction. Every smaller positive thickness
then gives a plate maximal value at least one, with a valid normalizing volume.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

/-- An open set containing every directional disk has plate maximal value at least one
at all sufficiently small positive scales, separately in each direction. -/
theorem exists_scale_one_le_plateMaximal {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hB : IsBesicovitch k U) (V : Grassmannian n k) :
    ∃ δ₀ > 0, ∀ δ ∈ Ioc (0 : ℝ) δ₀,
      1 ≤ plateMaximal δ (U.indicator (fun _ ↦ (1 : ℝ≥0∞))) V := by
  obtain ⟨a, ha⟩ := isBesicovitch_iff_unitDisk_subset.mp hB V.val V.property
  obtain ⟨δ₀, hδ₀, hsub⟩ := (isCompact_unitDisk V.val a).exists_thickening_subset_open hU ha
  refine ⟨δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  have hs : plate δ V.val a ⊆ U := (Metric.thickening_mono hδ.2 _).trans hsub
  have he : (∫⁻ x in plate δ V.val a, U.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) =
      volume (plate δ V.val a) := by
    have hg : ∀ x ∈ plate δ V.val a, U.indicator (fun _ ↦ (1 : ℝ≥0∞)) x = 1 :=
      fun x hx ↦ Set.indicator_of_mem (hs hx) _
    rw [setLIntegral_congr_fun (μ := volume) (s := plate δ V.val a)
      Metric.isOpen_thickening.measurableSet hg,
      setLIntegral_const, one_mul]
  have hv : (∫⁻ x in plate δ V.val a, U.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) /
      volume (plate δ V.val a) = 1 := by
    rw [he]
    exact ENNReal.div_self (volume_plate_pos hδ.1 _ _).ne' (volume_plate_lt_top δ _ _).ne
  rw [plateMaximal]
  exact le_iSup_of_le a hv.symm.le

end NKBesicovitch
