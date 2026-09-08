/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.RestrictedSelection
public import NKBesicovitch.Operators.XRay.SelectionLosses
public import NKBesicovitch.Projection.Selection.Main

/-!
# Restricted X-ray estimates from selectable projections

At every projection exponent `β` strictly above the critical root and
at most two, there is a finite integer `K > 2` such that a bounded
family of lines with indicator transform at least `r` satisfies
`rᴷ |F| ≤ C M(F)^(2-β) |E|^β`. The constants are independent of the sets
and of `0 < r ≤ 1`. No positive-volume assumption is imposed on either set.
-/

public section

open MeasureTheory Set Bornology NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

theorem exists_restricted_bound_of_scheme {m D L : ℕ} {β : ℝ}
    (S : Selection.SelectableProjectionScheme m β D L) (hβ : 0 ≤ β) (hβ2 : β ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 2 < K ∧
      ∀ E : Set (EuclideanSpace ℝ (Fin m) × ℝ), MeasurableSet E → volume E ≠ ∞ →
        ∀ F : Set (Line m), MeasurableSet F → IsBounded F → ∀ r : ℝ, 0 < r → r ≤ 1 →
          (∀ g ∈ F, ENNReal.ofReal r ≤ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1) →
          r ^ K * (volume F).toReal ≤ C * (parallelMultiplicity F).toReal ^ (2 - β) *
            (volume E).toReal ^ β := by
  let a := S.volumeExponent + S.boundExponent * D
  let K := a + S.boundExponent + 2
  let c := S.lowerConstant / (2 * S.upperConstant) ^ D
  have hC : 0 < S.upperConstant := zero_lt_one.trans_le S.one_le_upperConstant
  have hc : 0 < c := div_pos S.lowerConstant_pos (by positivity)
  have hB := S.boundExponent_pos
  refine ⟨2 ^ K * S.upperConstant / c, by positivity, K, by dsimp [K]; omega, ?_⟩
  intro E hE hEfin F hF hFb r hr hr₁ hrich
  have h := restricted_selection_bound S hβ hβ2 hE hEfin hF hFb hr hrich
  have harg : 2 * (volume E).toReal / r = (volume E).toReal / (r / 2) := by ring
  rw [harg] at h
  have hmass := collect_selection_losses hc hC.le (by positivity : 0 < r / 2)
    (by linarith : r / 2 ≤ 1) (Real.rpow_nonneg ENNReal.toReal_nonneg _) ENNReal.toReal_nonneg hβ2 h
  calc
    r ^ K * (volume F).toReal = 2 ^ K * ((r / 2) ^ K * (volume F).toReal) := by
      rw [div_pow]
      field_simp
    _ ≤ 2 ^ K * ((S.upperConstant / c) * (parallelMultiplicity F).toReal ^ (2 - β) *
        (volume E).toReal ^ β) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

theorem exists_restricted_bound (m : ℕ) [Nonempty (Fin m)] {β : ℝ}
    (hβ : projectionExponent < β) (hβ2 : β ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 2 < K ∧
      ∀ E : Set (EuclideanSpace ℝ (Fin m) × ℝ), MeasurableSet E → volume E ≠ ∞ →
        ∀ F : Set (Line m), MeasurableSet F → IsBounded F → ∀ r : ℝ, 0 < r → r ≤ 1 →
          (∀ g ∈ F, ENNReal.ofReal r ≤ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1) →
          r ^ K * (volume F).toReal ≤ C * (parallelMultiplicity F).toReal ^ (2 - β) *
            (volume E).toReal ^ β := by
  obtain ⟨D, L, ⟨S⟩⟩ := Selection.exists_selectableProjectionScheme m hβ
  exact exists_restricted_bound_of_scheme S (by linarith [projectionExponent_mem.1]) hβ2

end NKBesicovitch.XRay
