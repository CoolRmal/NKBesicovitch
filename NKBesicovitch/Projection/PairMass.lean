/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Incidence
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Tactic.NormNum

/-!
# The pair-incidence mass lower bound

Cauchy–Schwarz bounds squared line-family mass by the projection size times
the intrinsic pair mass. The projection size is an outer measure, so a Borel
projection-image assumption is unnecessary. The division-free form remains
valid in zero and infinite measure cases.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem lintegral_sq_le_measure_mul_lintegral_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ≥0∞} (hf : Measurable f) {s : Set X}
    (hs : Function.support f ⊆ s) :
    (∫⁻ x, f x ∂μ) ^ 2 ≤ μ s * ∫⁻ x, f x ^ 2 ∂μ := by
  have hh : (∫⁻ x in s, f x ∂μ) ≤
      (μ s) ^ (1 / 2 : ℝ) * (∫⁻ x in s, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    simpa only [Pi.mul_apply, Pi.one_apply, one_mul, one_pow, ENNReal.one_rpow, lintegral_const,
      Measure.restrict_apply_univ, ENNReal.rpow_two] using
      ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict s) Real.HolderConjugate.two_two
        (f := fun _ ↦ (1 : ℝ≥0∞)) measurable_const.aemeasurable hf.aemeasurable
  have hsq := pow_le_pow_left' hh 2
  rw [mul_pow, ← ENNReal.rpow_mul_natCast, ← ENNReal.rpow_mul_natCast] at hsq
  norm_num at hsq
  rw [setLIntegral_eq_of_support_subset hs] at hsq
  exact hsq.trans (mul_le_mul le_rfl (setLIntegral_le_lintegral _ _) bot_le bot_le)

theorem support_sliceMultiplicity_subset (a : ℝ) (G : Set (Line m)) :
    Function.support (sliceMultiplicity a G) ⊆ atHeight a '' G := by
  intro w hw
  obtain ⟨ξ, hξ⟩ := nonempty_of_measure_ne_zero hw
  refine ⟨lineAt a w ξ, hξ, ?_⟩
  simp [atHeight_lineAt]

/-- The Cauchy–Schwarz lower bound for intrinsic incidence pairs, without division. -/
theorem sq_volume_le_projection_mul_pairMass (a : ℝ) {G : Set (Line m)}
    (hG : MeasurableSet G) :
    volume G ^ 2 ≤ volume (atHeight a '' G) * volume (pairFamily a G) := by
  rw [volume_pairFamily a hG, ← lintegral_sliceMultiplicity a hG]
  exact lintegral_sq_le_measure_mul_lintegral_sq (measurable_sliceMultiplicity a hG)
    (support_sliceMultiplicity_subset a G)

theorem volume_pairFamily_pos (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G)
    (hpos : 0 < volume G) : 0 < volume (pairFamily a G) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have h := sq_volume_le_projection_mul_pairMass a hG
  rw [hz, mul_zero] at h
  exact (not_le_of_gt (ENNReal.pow_pos hpos 2)) h

end NKBesicovitch.Projection
