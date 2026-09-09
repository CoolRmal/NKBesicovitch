/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.TerminalDecay
public import NKBesicovitch.Operators.XRay.DyadicMajorant
public import NKBesicovitch.Operators.MixedNorm.Sums
public import NKBesicovitch.Operators.Fourier.DyadicDecomposition
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Summing the terminal plate majorants

When the lower-dimensional deficit is less than one, the frequency gains
form a convergent geometric series. The measurable sum of the weighted
plate majorants has a uniform joint `Lᵖ` bound for fixed input support.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.Induction

private lemma eLpNorm_add_tsum_le_of_geometric_aux {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p q T : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ∞) (hq : q < 1)
    (B D : ℝ≥0) {f : X → ℝ≥0∞} {g : ℕ → X → ℝ≥0∞}
    (hf : Measurable f) (hg : ∀ j, Measurable (g j)) (hfB : eLpNorm f p μ ≤ B * T)
    (hgD : ∀ j, eLpNorm (g j) p μ ≤ D * q ^ j * T) :
    eLpNorm (fun x ↦ f x + ∑' j, g j x) p μ ≤
      (B + D * (∑' j : ℕ, q ^ j).toNNReal : ℝ≥0) * T := by
  have hS : (∑' j : ℕ, q ^ j) ≠ ∞ := (tsum_geometric_lt_top.mpr hq).ne
  calc
    _ ≤ eLpNorm f p μ + eLpNorm (fun x ↦ ∑' j, g j x) p μ :=
      eLpNorm_add_le hf.aestronglyMeasurable (Measurable.tsum hg).aestronglyMeasurable hp
    _ ≤ B * T + ∑' j, eLpNorm (g j) p μ :=
      add_le_add hfB (eLpNorm_tsum_le hg hp hpfin)
    _ ≤ B * T + ∑' j, D * q ^ j * T := add_le_add le_rfl (ENNReal.tsum_le_tsum hgD)
    _ = _ := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.coe_add,
        ENNReal.coe_mul, ENNReal.coe_toNNReal hS, add_mul]

variable {m k : ℕ} [Nonempty (Fin m)]
  (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- The low-frequency and annular plate majorants have a uniformly bounded sum. -/
theorem HasPlateEstimate.exists_eLpNorm_plateMaximal_frame_series_le
    {hkm : k ≤ m} {α p : ℝ} (h : HasPlateEstimate hkm α p) (hα : α < 1) (hp : 2 ≤ p)
    (φ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ))
    (hφ : ∀ ξ, ‖ξ‖ ≤ 1 → 𝓕 φ ξ = 1) (A : ℕ) (R : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
        eLpNorm (XRay.dyadicFrameMajorant v b φ A f)
          (ENNReal.ofReal p) ((Rotations.probability (m + 1)).prod (Grassmannian.probability hkm)) ≤
            C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp₁ : 1 ≤ p := by linarith
  let q : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (-(1 - α) / p)
  let S := ∑' j : ℕ, q ^ j
  have hq : q < 1 := ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (div_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr hα)) (by linarith))
  obtain ⟨B, hB⟩ := h.exists_eLpNorm_plateMaximal_frame_convolution_le v b hp₁ φ A R
  obtain ⟨D, hD⟩ := h.exists_eLpNorm_plateMaximal_frame_decay v b hp
    (normalizedDilation 2 two_pos φ - φ)
    (fun _ hξ ↦ fourier_dilation_sub_eq_zero_of_norm_lt φ hφ hξ) A R
  refine ⟨B + D * S.toNNReal, fun f hs ↦ ?_⟩
  unfold XRay.dyadicFrameMajorant
  apply eLpNorm_add_tsum_le_of_geometric_aux (ENNReal.one_le_ofReal.mpr hp₁)
    ENNReal.ofReal_ne_top hq B D
  · exact XRay.measurable_plateMaximal_weighted_frameLineIntegral v b zero_lt_one A _
  · intro j
    exact XRay.measurable_plateMaximal_weighted_frameLineIntegral v b (by positivity) A _
  · exact hB f hs
  · intro j
    have he : (((2 : ℝ≥0) ^ j : ℝ≥0) : ℝ≥0∞) ^ (-(1 - α) / p) = q ^ j := by
      rw [ENNReal.coe_pow, ENNReal.coe_ofNat, ← ENNReal.rpow_natCast_mul,
        mul_comm (j : ℝ), ENNReal.rpow_mul, ENNReal.rpow_natCast]
    have hd := hD ((2 : ℝ≥0) ^ j) (by positivity) (one_le_pow₀ one_le_two) f hs
    rw [he] at hd
    simpa only [NNReal.coe_pow, NNReal.coe_ofNat] using hd

end NKBesicovitch.Induction
