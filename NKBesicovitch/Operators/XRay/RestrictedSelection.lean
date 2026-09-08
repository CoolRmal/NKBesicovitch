/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.SelectedFamily

/-!
# The restricted X-ray inequality before collecting selection losses

Each rich line has at least half the required time measure in small
spatial slices. One common parameter retains a polynomial fraction of
the rich line family, to which the selectable projection estimate applies.
All constants and powers below come from the given scheme.
-/

public section

open MeasureTheory Set Bornology NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {m D L : ℕ} {β : ℝ} (S : Selection.SelectableProjectionScheme m β D L)

theorem restricted_selection_bound (hβ : 0 ≤ β) (hβ2 : β ≤ 2)
    {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)} (hE : MeasurableSet E) (hEfin : volume E ≠ ∞)
    {F : Set (Line m)} (hF : MeasurableSet F) (hFb : IsBounded F) {r : ℝ} (hr : 0 < r)
    (hrich : ∀ g ∈ F, ENNReal.ofReal r ≤ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1) :
    (S.lowerConstant / (2 * S.upperConstant) ^ D) *
      (r / 2) ^ (S.volumeExponent + S.boundExponent * D) * (volume F).toReal ≤
        (S.upperConstant * (r / 2)⁻¹ ^ S.boundExponent) *
          (parallelMultiplicity F).toReal ^ (2 - β) * (2 * (volume E).toReal / r) ^ β := by
  let N := 2 * (volume E).toReal / r
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hrhalf : 0 < r / 2 := by positivity
  have hmeasure (g : Line m) (hg : g ∈ F) :
      ENNReal.ofReal (r / 2) ≤ volume (goodTimes E (ENNReal.ofReal N) g) :=
    half_le_volume_goodTimes hE hEfin hr (hrich g hg)
  obtain ⟨σ, _, hmass⟩ := S.exists_common_parameter_polynomial hF hFb.measure_lt_top.ne
    (measurableSet_goodTimes_family hE (ENNReal.ofReal N))
    (fun g _ ↦ goodTimes_subset_unit E _ g) hrhalf hmeasure
  have hGfin : volume (S.commonLines F (goodTimes E (ENNReal.ofReal N)) σ) ≠ ∞ :=
    (hFb.subset (show S.commonLines F _ σ ⊆ F from inter_subset_left)).measure_lt_top.ne
  have hreal := ENNReal.toReal_mono hGfin hmass
  have hc := S.lowerConstant_pos
  have hC := zero_lt_one.trans_le S.one_le_upperConstant
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
  exact hreal.trans (estimate_commonLines_goodTimes S hβ hβ2 hE hF hFb hN hrhalf hmeasure σ)

end NKBesicovitch.XRay
