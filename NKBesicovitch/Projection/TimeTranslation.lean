/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Estimates

/-!
# Translating the heights of a projection estimate

Changing the origin of the height coordinate shears intercepts while
fixing slopes. This preserves line volume and every parallel-fiber mass,
so the same estimate constant works on any translate of its height set.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem atHeight_image_preimage_lineCoordinates (a t : ℝ) (G : Set (Line m)) :
    atHeight t '' (lineCoordinates a ⁻¹' G) = atHeight (t + a) '' G := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨lineCoordinates a g, hg, ?_⟩
    rw [lineCoordinates_apply, atHeight_lineAt, add_sub_cancel_right]
    rfl
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(lineCoordinates a).symm g, by simpa using hg, ?_⟩
    simp only [lineCoordinates_symm_apply, atHeight, add_smul]
    module

theorem parallelMultiplicity_preimage_lineCoordinates (a : ℝ) (G : Set (Line m)) :
    parallelMultiplicity (lineCoordinates a ⁻¹' G) = parallelMultiplicity G := by
  unfold parallelMultiplicity
  congr 1
  funext ξ
  have hs : {x | (x, ξ) ∈ lineCoordinates a ⁻¹' G} =
      (fun x ↦ x + (-a) • ξ) ⁻¹' {x | (x, ξ) ∈ G} := by
    ext x
    simp only [mem_preimage, lineCoordinates_apply, lineAt, mem_ofPred_eq,
      sub_eq_add_neg, neg_smul]
  rw [hs, measure_preimage_add_right]

theorem sliceSize_preimage_lineCoordinates (a : ℝ) (Γ : Finset ℝ) (G : Set (Line m)) :
    sliceSize Γ (lineCoordinates a ⁻¹' G) = sliceSize (Γ.image (· + a)) G := by
  simp only [sliceSize, Finset.iSup_finset_image, atHeight_image_preimage_lineCoordinates]

theorem HasProjectionEstimate.translate {β : ℝ} {Γ : Finset ℝ}
    (h : HasProjectionEstimate m β Γ) (a : ℝ) :
    HasProjectionEstimate m β (Γ.image (· + a)) := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun G hG hGb ↦ ?_⟩
  have hF : MeasurableSet (lineCoordinates a ⁻¹' G) :=
    hG.preimage (lineCoordinates a).continuous.measurable
  have hFb : IsBounded (lineCoordinates a ⁻¹' G) := by
    rw [← (lineCoordinates a).image_symm_eq_preimage]
    exact (lineCoordinates a).symm.toContinuousLinearMap.lipschitz.isBounded_image hGb
  have hmass : volume (lineCoordinates a ⁻¹' G) = volume G :=
    (measurePreserving_lineCoordinates a).measure_preimage hG.nullMeasurableSet
  simpa only [hmass, parallelMultiplicity_preimage_lineCoordinates,
    sliceSize_preimage_lineCoordinates] using hbound _ hF hFb

/-- A finite height pattern can be translated away from any finite forbidden set. -/
theorem exists_translate_avoiding (Γ F : Finset ℝ) :
    ∃ a : ℝ, ∀ t ∈ Γ.image (· + a), t ∉ F := by
  classical
  obtain ⟨a, ha⟩ := (F.biUnion fun f ↦ Γ.image (fun t ↦ f - t)).exists_notMem
  refine ⟨a, fun t ht hF ↦ ?_⟩
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
  exact ha (Finset.mem_biUnion.mpr ⟨s + a, hF,
    Finset.mem_image.mpr ⟨s, hs, by ring⟩⟩)

end NKBesicovitch.Projection
