/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.ParameterBox
public import Mathlib.MeasureTheory.Integral.Average

/-!
# One common parameter for a measurable family of time sets

Joint selection and Tonelli identify the total incidence mass in either
order of integration. Averaging inside the common finite parameter box
then produces one parameter shared by a quantitatively large line family.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

/-- Lines whose time-set selection contains the given common parameter. -/
def commonLines (F : Set (Line m)) (I : Line m → Set ℝ) (σ : Fin D → ℝ) : Set (Line m) :=
  F ∩ {g | σ ∈ S.select (I g)}

theorem measurableSet_commonLines {F : Set (Line m)} (hF : MeasurableSet F)
    {I : Line m → Set ℝ} (hI : MeasurableSet {p : Line m × ℝ | p.2 ∈ I p.1})
    (σ : Fin D → ℝ) : MeasurableSet (S.commonLines F I σ) :=
  hF.inter (S.measurableSet_mem_select hI measurable_const)

theorem lintegral_volume_commonLines {F : Set (Line m)} (hF : MeasurableSet F)
    {I : Line m → Set ℝ} (hI : MeasurableSet {p : Line m × ℝ | p.2 ∈ I p.1}) :
    (∫⁻ σ, volume (S.commonLines F I σ)) = ∫⁻ g in F, volume (S.select (I g)) := by
  let R : Set (Line m × (Fin D → ℝ)) := {p | p.1 ∈ F ∧ p.2 ∈ S.select (I p.1)}
  have hR : MeasurableSet R := by
    simpa only [R, preimage, ofPred_and] using
      (hF.preimage (measurable_fst : Measurable (Prod.fst : Line m × (Fin D → ℝ) → Line m))).inter
        (S.measurable_select I hI)
  have hσ (σ : Fin D → ℝ) : (fun g ↦ (g, σ)) ⁻¹' R = S.commonLines F I σ := by
    ext g
    simp [R, commonLines]
  calc
    _ = (volume : Measure (Line m)).prod volume R := by
      rw [Measure.prod_apply_symm hR]
      simp_rw [hσ]
    _ = _ := by
      rw [Measure.prod_apply hR, ← lintegral_indicator hF]
      apply lintegral_congr
      intro g
      by_cases hg : g ∈ F
      · have he : Prod.mk g ⁻¹' R = S.select (I g) := by
          ext σ
          simp [R, hg]
        simp only [he, indicator_of_mem hg]
      · have he : Prod.mk g ⁻¹' R = ∅ := by
          ext σ
          simp [R, hg]
        simp only [he, measure_empty, indicator_of_notMem hg]

theorem support_volume_commonLines_subset {F : Set (Line m)} {I : Line m → Set ℝ}
    (hI : MeasurableSet {p : Line m × ℝ | p.2 ∈ I p.1})
    (hunit : ∀ g ∈ F, I g ⊆ Icc 0 1) {r : ℝ} (hr : 0 < r)
    (hmeasure : ∀ g ∈ F, ENNReal.ofReal r ≤ volume (I g)) :
    Function.support (fun σ ↦ volume (S.commonLines F I σ)) ⊆ S.parameterBox r := by
  intro σ hσ
  obtain ⟨g, hgF, hgσ⟩ := nonempty_of_measure_ne_zero hσ
  have hIg : MeasurableSet (I g) :=
    hI.preimage (f := fun t ↦ (g, t)) (by fun_prop)
  exact S.select_subset_parameterBox hIg (hunit g hgF) hr (hmeasure g hgF) hgσ

theorem exists_common_parameter {F : Set (Line m)} (hF : MeasurableSet F)
    (hFfin : volume F ≠ ∞) {I : Line m → Set ℝ}
    (hI : MeasurableSet {p : Line m × ℝ | p.2 ∈ I p.1})
    (hunit : ∀ g ∈ F, I g ⊆ Icc 0 1) {r : ℝ} (hr : 0 < r)
    (hmeasure : ∀ g ∈ F, ENNReal.ofReal r ≤ volume (I g)) :
    ∃ σ ∈ S.parameterBox r,
      (ENNReal.ofReal (S.lowerConstant * r ^ S.volumeExponent) * volume F) /
        volume (S.parameterBox r) ≤ volume (S.commonLines F I σ) := by
  have hmass : (∫⁻ σ in S.parameterBox r, volume (S.commonLines F I σ)) =
      ∫⁻ g in F, volume (S.select (I g)) :=
    (setLIntegral_eq_of_support_subset
      (S.support_volume_commonLines_subset hI hunit hr hmeasure)).trans
      (S.lintegral_volume_commonLines hF hI)
  have hfin : (∫⁻ σ in S.parameterBox r, volume (S.commonLines F I σ)) ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hFfin (S.volume_parameterBox_ne_top hr.le))
    calc
      _ ≤ ∫⁻ _ in S.parameterBox r, volume F :=
        lintegral_mono (fun _ ↦ measure_mono inter_subset_left)
      _ = _ := setLIntegral_const _ _
  obtain ⟨σ, hσ, hσmass⟩ := exists_setLAverage_le (S.volume_parameterBox_pos hr).ne'
    (S.measurableSet_parameterBox r).nullMeasurableSet hfin
  refine ⟨σ, hσ, ?_⟩
  rw [setLAverage_eq, hmass] at hσmass
  apply le_trans _ hσmass
  apply ENNReal.div_le_div_right
  calc
    _ = ∫⁻ _ in F, ENNReal.ofReal (S.lowerConstant * r ^ S.volumeExponent) :=
      (setLIntegral_const _ _).symm
    _ ≤ _ := setLIntegral_mono' hF (fun g hg ↦ S.volume_lower_of_measure_lower
      (hI.preimage (f := fun t ↦ (g, t)) (by fun_prop)) (hunit g hg) hr (hmeasure g hg))

theorem selection_fraction_eq {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (S.lowerConstant * r ^ S.volumeExponent) / volume (S.parameterBox r) =
      ENNReal.ofReal ((S.lowerConstant / (2 * S.upperConstant) ^ D) *
        r ^ (S.volumeExponent + S.boundExponent * D)) := by
  have hC : 0 < S.upperConstant := zero_lt_one.trans_le S.one_le_upperConstant
  rw [S.volume_parameterBox hr.le, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  simp only [div_mul_eq_div_div, inv_pow, div_inv_eq_mul, pow_add]
  ring

/-- One common parameter retains a polynomial fraction of the original line mass. -/
theorem exists_common_parameter_polynomial {F : Set (Line m)} (hF : MeasurableSet F)
    (hFfin : volume F ≠ ∞) {I : Line m → Set ℝ}
    (hI : MeasurableSet {p : Line m × ℝ | p.2 ∈ I p.1})
    (hunit : ∀ g ∈ F, I g ⊆ Icc 0 1) {r : ℝ} (hr : 0 < r)
    (hmeasure : ∀ g ∈ F, ENNReal.ofReal r ≤ volume (I g)) :
    ∃ σ ∈ S.parameterBox r,
      ENNReal.ofReal ((S.lowerConstant / (2 * S.upperConstant) ^ D) *
        r ^ (S.volumeExponent + S.boundExponent * D)) * volume F ≤
          volume (S.commonLines F I σ) := by
  obtain ⟨σ, hσ, hmass⟩ := S.exists_common_parameter hF hFfin hI hunit hr hmeasure
  refine ⟨σ, hσ, ?_⟩
  rwa [ENNReal.mul_div_right_comm, S.selection_fraction_eq hr] at hmass

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
