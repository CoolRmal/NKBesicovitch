/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.Basic
public import NKBesicovitch.Operators.MixedNorm.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Moving a unit time interval to the model interval

Vertical translation of the input and a direction-dependent translation
of the horizontal intercept move `[a,a+1]` to `[0,1]`. Both input norms
and the mixed output norm are preserved by these translations.
-/

public section

open MeasureTheory Set NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞}

theorem lintegral_unitInterval_eq_localXRay (hf : Measurable f) (a : ℝ)
    (ξ x : EuclideanSpace ℝ (Fin m)) :
    (∫⁻ t in Icc a (a + 1), f (x + t • ξ, t)) =
      localXRay (fun z ↦ f (z.1, a + z.2)) ξ (x + a • ξ) := by
  have hm : Measurable (fun t : ℝ ↦ f (x + t • ξ, t)) := hf.comp (by fun_prop)
  have h := (measurePreserving_add_left volume a).setLIntegral_comp_preimage
    (measurableSet_Icc (a := a) (b := a + 1)) hm
  have hpre : (fun t : ℝ ↦ a + t) ⁻¹' Icc a (a + 1) = Icc 0 1 := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre] at h
  rw [← h]
  unfold localXRay
  congr 1
  funext t
  congr 2
  rw [add_smul, add_assoc]

theorem eLpNorm_vertical_translate (hf : Measurable f) (a : ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun z : EuclideanSpace ℝ (Fin m) × ℝ ↦ f (z.1, a + z.2)) p volume =
      eLpNorm f p volume := by
  have hp : MeasurePreserving (fun z : EuclideanSpace ℝ (Fin m) × ℝ ↦ (z.1, a + z.2))
      volume volume := by
    simpa only [Measure.volume_eq_prod, Prod.map_def, id_eq] using
      (MeasurePreserving.id (volume : Measure (EuclideanSpace ℝ (Fin m)))).prod
        (measurePreserving_add_left volume a)
  exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hp

theorem mixedNorm_unitInterval_eq_localXRay (hf : Measurable f) (a : ℝ)
    (Ξ : Set (EuclideanSpace ℝ (Fin m))) (q r : ℝ≥0∞) :
    mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ ∫⁻ t in Icc a (a + 1), f (g.1 + t • g.2, t))) q r volume volume =
        mixedNorm ((Prod.snd ⁻¹' Ξ).indicator (fun g : Line m ↦
          localXRay (fun z ↦ f (z.1, a + z.2)) g.2 g.1)) q r volume volume := by
  have htranslated : Measurable (fun z : EuclideanSpace ℝ (Fin m) × ℝ ↦
      f (z.1, a + z.2)) := hf.comp (by fun_prop)
  have hT := measurable_localXRay htranslated
  unfold mixedNorm
  congr 1
  funext ξ
  by_cases hξ : ξ ∈ Ξ
  · have hmem (x : EuclideanSpace ℝ (Fin m)) : (x, ξ) ∈ Prod.snd ⁻¹' Ξ := hξ
    simp only [indicator_of_mem (hmem _)]
    simp_rw [lintegral_unitInterval_eq_localXRay hf a]
    exact eLpNorm_comp_measurePreserving
      (hT.comp measurable_prodMk_right).aestronglyMeasurable
        (measurePreserving_add_right volume (a • ξ))
  · have hzero (x : EuclideanSpace ℝ (Fin m)) : (x, ξ) ∉ Prod.snd ⁻¹' Ξ := hξ
    simp only [indicator_of_notMem (hzero _)]

end NKBesicovitch.XRay
