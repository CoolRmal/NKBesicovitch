/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.GoodTimes
public import NKBesicovitch.Projection.Selection.CommonParameters

/-!
# Projection control for lines sharing a good-time parameter

Every selected height lies in every retained line's good-time set.
Consequently all selected projections lie in spatial slices of bounded
volume. Applying the scheme at any retained line's time set gives a
projection estimate with the common polynomial constant.
-/

@[expose] public section

open MeasureTheory Set Bornology NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {m D L : ℕ} {β : ℝ} (S : Selection.SelectableProjectionScheme m β D L)

theorem volume_projection_commonLines_goodTimes_le
    {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)} (hE : MeasurableSet E)
    {F : Set (Line m)} {N : ℝ≥0∞} {r : ℝ} (hr : 0 < r)
    (hmeasure : ∀ g ∈ F, ENNReal.ofReal r ≤ volume (goodTimes E N g))
    (σ : Fin D → ℝ) (i : Fin L) :
    volume (atHeight (S.time σ i) '' S.commonLines F (goodTimes E N) σ) ≤ N := by
  have htime (g : Line m) (hg : g ∈ S.commonLines F (goodTimes E N) σ) :
      S.time σ i ∈ goodTimes E N g :=
    S.time_mem _ (measurableSet_goodTimes hE N g) (goodTimes_subset_unit E N g)
      ((ENNReal.ofReal_pos.mpr hr).trans_le (hmeasure g hg.1)) σ hg.2 i
  by_cases hG : (S.commonLines F (goodTimes E N) σ).Nonempty
  · obtain ⟨g₀, hg₀⟩ := hG
    have hsubset : atHeight (S.time σ i) '' S.commonLines F (goodTimes E N) σ ⊆
        (fun x ↦ (x, S.time σ i)) ⁻¹' E := by
      rintro _ ⟨g, hg, rfl⟩
      exact (goodTimes_spec (htime g hg)).1
    exact (measure_mono hsubset).trans (goodTimes_spec (htime g₀ hg₀)).2
  · rw [not_nonempty_iff_eq_empty.mp hG, image_empty, measure_empty]
    exact zero_le

theorem estimate_commonLines_goodTimes (hβ : 0 ≤ β) (hβ2 : β ≤ 2)
    {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)} (hE : MeasurableSet E)
    {F : Set (Line m)} (hF : MeasurableSet F) (hFb : IsBounded F)
    {N r : ℝ} (hN : 0 ≤ N) (hr : 0 < r)
    (hmeasure : ∀ g ∈ F, ENNReal.ofReal r ≤ volume (goodTimes E (ENNReal.ofReal N) g))
    (σ : Fin D → ℝ) :
    (volume (S.commonLines F (goodTimes E (ENNReal.ofReal N)) σ)).toReal ≤
      (S.upperConstant * r⁻¹ ^ S.boundExponent) *
        (parallelMultiplicity F).toReal ^ (2 - β) * N ^ β := by
  let G := S.commonLines F (goodTimes E (ENNReal.ofReal N)) σ
  have hG : MeasurableSet G :=
    S.measurableSet_commonLines hF (measurableSet_goodTimes_family hE _) σ
  have hGF : G ⊆ F := inter_subset_left
  have hGb := hFb.subset hGF
  change (volume G).toReal ≤ _
  by_cases hGempty : G = ∅
  · simp only [hGempty, measure_empty, ENNReal.toReal_zero]
    have hC := zero_le_one.trans S.one_le_upperConstant
    positivity
  obtain ⟨g, hg⟩ := nonempty_iff_ne_empty.mpr hGempty
  have hupper := S.estimate_of_measure_lower (measurableSet_goodTimes hE _ g)
    (goodTimes_subset_unit E _ g) hr (hmeasure g hg.1) hg.2 hG hGb
  have hsize : (sliceSize (Finset.univ.image (S.time σ)) G).toReal ≤ N := by
    apply sliceSize_toReal_le hGb hN
    rintro t ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    simpa only [ENNReal.toReal_ofReal hN] using ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (volume_projection_commonLines_goodTimes_le S hE hr hmeasure σ i)
  have hM := ENNReal.toReal_mono (parallelMultiplicity_ne_top hFb) (parallelMultiplicity_mono hGF)
  have hC := zero_le_one.trans S.one_le_upperConstant
  exact hupper.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ENNReal.toReal_nonneg hM (by linarith))
      (by positivity))
    (Real.rpow_le_rpow ENNReal.toReal_nonneg hsize hβ) (by positivity) (by positivity))

end NKBesicovitch.XRay
