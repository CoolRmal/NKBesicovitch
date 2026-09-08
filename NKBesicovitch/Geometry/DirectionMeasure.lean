/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.DirectionChart
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Comparing spherical direction measure with slope volume

The cone formula for sphere measure gives an upper bound for the measure
of a chart image by the ambient dimension times the slope volume. A cone
inside the unit ball has height between zero and one; its horizontal
slices contract the slope set. This one-sided bound avoids an unnecessary
exact Jacobian computation.
-/

public section

open MeasureTheory Set Submodule Metric
open scoped ENNReal InnerProductSpace Pointwise

namespace NKBesicovitch

section SlopeCone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] {A : Set H}

theorem measurableSet_slopeCone (hA : MeasurableSet A) :
    MeasurableSet {z : H × ℝ | z.2 ∈ Ioo (0 : ℝ) 1 ∧ z.2⁻¹ • z.1 ∈ A} :=
  (measurableSet_Ioo.preimage measurable_snd).inter
    (hA.preimage (measurable_snd.inv.smul measurable_fst))

theorem volume_slopeCone_le (hA : MeasurableSet A) :
    volume {z : H × ℝ | z.2 ∈ Ioo (0 : ℝ) 1 ∧ z.2⁻¹ • z.1 ∈ A} ≤ volume A := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_slopeCone hA)]
  calc
    _ ≤ ∫⁻ t : ℝ, (Ioo (0 : ℝ) 1).indicator (fun _ ↦ volume A) t := by
      apply lintegral_mono
      intro t
      by_cases ht : t ∈ Ioo (0 : ℝ) 1
      · rw [indicator_of_mem ht]
        have hsub : {x : H | t ∈ Ioo (0 : ℝ) 1 ∧ t⁻¹ • x ∈ A} ⊆ t • A := by
          intro x hx
          exact mem_smul_set.mpr ⟨t⁻¹ • x, hx.2, by
            rw [smul_smul, mul_inv_cancel₀ ht.1.ne', one_smul]⟩
        calc
          _ ≤ volume (t • A) := measure_mono hsub
          _ = ENNReal.ofReal (t ^ Module.finrank ℝ H) * volume A :=
            volume.addHaar_smul_of_nonneg ht.1.le A
          _ ≤ volume A := by
            have ht1 : ENNReal.ofReal (t ^ Module.finrank ℝ H) ≤ 1 := by
              rw [← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal (pow_le_one₀ ht.1.le ht.2.le)
            simpa only [one_mul] using mul_le_mul_left ht1 (volume A)
      · simp only [Set.preimage, mem_ofPred_eq, ht, false_and, ofPred_false,
          measure_empty, indicator_of_notMem ht]
        exact le_rfl
    _ = volume A := by
      rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, sub_zero,
        ENNReal.ofReal_one, mul_one]

end SlopeCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : E}

theorem normalDirection_cone_subset (hv : ‖v‖ = 1) (A : Set (ℝ ∙ v)ᗮ) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (normalDirection hv '' A)) ⊆
      normalCoordinates hv ''
        {z : (ℝ ∙ v)ᗮ × ℝ | z.2 ∈ Ioo (0 : ℝ) 1 ∧ z.2⁻¹ • z.1 ∈ A} := by
  rintro y ⟨r, hr, _, ⟨_, ⟨ξ, hξ, rfl⟩, rfl⟩, rfl⟩
  let t := r * ‖(ξ : E) + v‖⁻¹
  have hn : 0 < ‖(ξ : E) + v‖ := zero_lt_one.trans_le (one_le_norm_add_normal hv ξ)
  have ht : 0 < t := mul_pos hr.1 (inv_pos.mpr hn)
  have ht1 : t < 1 := by
    change r / ‖(ξ : E) + v‖ < 1
    exact (div_lt_one hn).mpr (hr.2.trans_le (one_le_norm_add_normal hv ξ))
  refine ⟨(t • ξ, t), ⟨⟨ht, ht1⟩, ?_⟩, ?_⟩
  · simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using hξ
  · rw [normalCoordinates_apply, Submodule.coe_smul, coe_normalDirection]
    change t • (ξ : E) + t • v = r • (‖(ξ : E) + v‖⁻¹ • ((ξ : E) + v))
    rw [smul_smul]
    exact (smul_add t (ξ : E) v).symm

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem toSphere_normalDirection_image_le (hv : ‖v‖ = 1)
    {A : Set (ℝ ∙ v)ᗮ} (hA : MeasurableSet A) :
    (volume : Measure E).toSphere (normalDirection hv '' A) ≤
      (Module.finrank ℝ E : ℝ≥0∞) * volume A := by
  rw [Measure.toSphere_apply' _
    ((measurableEmbedding_normalDirection hv).measurableSet_image.mpr hA)]
  apply mul_le_mul_right
  calc
    _ ≤ volume (normalCoordinates hv ''
        {z : (ℝ ∙ v)ᗮ × ℝ | z.2 ∈ Ioo (0 : ℝ) 1 ∧ z.2⁻¹ • z.1 ∈ A}) :=
      measure_mono (normalDirection_cone_subset hv A)
    _ = volume {z : (ℝ ∙ v)ᗮ × ℝ | z.2 ∈ Ioo (0 : ℝ) 1 ∧ z.2⁻¹ • z.1 ∈ A} := by
      have hm : MeasurableSet (normalCoordinates hv ''
          {z : (ℝ ∙ v)ᗮ × ℝ | z.2 ∈ Ioo (0 : ℝ) 1 ∧ z.2⁻¹ • z.1 ∈ A}) :=
        (normalCoordinates hv).toHomeomorph.measurableEmbedding.measurableSet_image.mpr
          (measurableSet_slopeCone hA)
      have h := (measurePreserving_normalCoordinates hv).measure_preimage hm.nullMeasurableSet
      rw [(normalCoordinates hv).injective.preimage_image] at h
      exact h.symm
    _ ≤ volume A := volume_slopeCone_le hA

theorem toSphere_restrict_normalDirection_le (hv : ‖v‖ = 1)
    {A : Set (ℝ ∙ v)ᗮ} (hA : MeasurableSet A) :
    (volume : Measure E).toSphere.restrict (normalDirection hv '' A) ≤
      (Module.finrank ℝ E : ℝ≥0∞) • (volume.restrict A).map (normalDirection hv) := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.restrict_apply hs, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurableEmbedding_normalDirection hv).measurable hs,
    Measure.restrict_apply (hs.preimage (measurableEmbedding_normalDirection hv).measurable)]
  rw [← image_preimage_inter]
  exact toSphere_normalDirection_image_le hv
    ((hs.preimage (measurableEmbedding_normalDirection hv).measurable).inter hA)

/-- Outer direction norms are controlled by the corresponding slope norms on each chart. -/
theorem eLpNorm_toSphere_normalDirection_le (hv : ‖v‖ = 1)
    {A : Set (ℝ ∙ v)ᗮ} (hA : MeasurableSet A) (f : sphere (0 : E) 1 → ℝ≥0∞) (p : ℝ≥0∞) :
    eLpNorm f p ((volume : Measure E).toSphere.restrict (normalDirection hv '' A)) ≤
      (Module.finrank ℝ E : ℝ≥0∞) ^ (1 / p.toReal) *
        eLpNorm (f ∘ normalDirection hv) p (volume.restrict A) := by
  apply (eLpNorm_mono_measure f (toSphere_restrict_normalDirection_le hv hA)).trans
  simpa only [(measurableEmbedding_normalDirection hv).eLpNorm_map_measure,
    ENNReal.toReal_div, ENNReal.toReal_one, smul_eq_mul] using
    eLpNorm_smul_measure_le (Module.finrank ℝ E : ℝ≥0∞) f p
      ((volume.restrict A).map (normalDirection hv))

end NKBesicovitch
