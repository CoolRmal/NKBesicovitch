/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Controlling weighted integrals by translated averages

A nonnegative kernel that changes by only a bounded factor under translations
in a set is controlled by averaging over that set. Tonelli then bounds its
pairing with an input by the supremum of translated local averages times the
kernel mass. Positive finite averaging volume is required for cancellation.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NKBesicovitch

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant]

private lemma lintegral_mul_translate_average_eq_aux {f K : G → ℝ≥0∞}
    (hf : Measurable f) (hK : Measurable K) (S : Set G) :
    (∫⁻ t in S, ∫⁻ z, f z * K (z - t) ∂μ ∂μ) =
      ∫⁻ z, K z * (∫⁻ t in S, f (z + t) ∂μ) ∂μ := by
  have he (t : G) : (∫⁻ z, f z * K (z - t) ∂μ) = ∫⁻ z, f (z + t) * K z ∂μ := by
    rw [← lintegral_add_right_eq_self (μ := μ) (fun z ↦ f z * K (z - t)) t]
    simp only [add_sub_cancel_right]
  simp_rw [he]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro z
    rw [lintegral_mul_const (f := fun t ↦ f (z + t)) (K z)
      (hf.comp (measurable_const.add measurable_id)), mul_comm]
  · exact ((hf.comp (measurable_snd.add measurable_fst)).mul
      (hK.comp measurable_snd)).aemeasurable

/-- A kernel with bounded variation on an averaging set pairs boundedly with local averages. -/
theorem lintegral_mul_le_of_translated_averages {f K : G → ℝ≥0∞}
    (hf : Measurable f) (hK : Measurable K) {S : Set G} (hS : MeasurableSet S)
    (hS₀ : μ S ≠ 0) (hSfin : μ S ≠ ∞) {C : ℝ≥0} {M : ℝ≥0∞}
    (hshift : ∀ z t, t ∈ S → K z ≤ C * K (z - t))
    (havg : ∀ z, (∫⁻ t in S, f (z + t) ∂μ) ≤ M * μ S) :
    (∫⁻ z, f z * K z ∂μ) ≤ C * M * ∫⁻ z, K z ∂μ := by
  apply (ENNReal.mul_le_mul_iff_left hS₀ hSfin).mp
  calc
    _ = ∫⁻ t in S, ∫⁻ z, f z * K z ∂μ ∂μ := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ t in S, C * ∫⁻ z, f z * K (z - t) ∂μ ∂μ := by
      apply setLIntegral_mono' hS
      intro t ht
      apply (lintegral_mono fun z ↦ mul_le_mul_right (hshift z t ht) (f z)).trans_eq
      simp_rw [mul_left_comm (f _) (C : ℝ≥0∞)]
      exact lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ = C * ∫⁻ t in S, ∫⁻ z, f z * K (z - t) ∂μ ∂μ :=
      lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ = C * ∫⁻ z, K z * (∫⁻ t in S, f (z + t) ∂μ) ∂μ := by
      rw [lintegral_mul_translate_average_eq_aux μ hf hK]
    _ ≤ C * ∫⁻ z, K z * (M * μ S) ∂μ := by
      gcongr with z
      exact havg z
    _ = _ := by rw [lintegral_mul_const _ hK]; ac_rfl

end NKBesicovitch
