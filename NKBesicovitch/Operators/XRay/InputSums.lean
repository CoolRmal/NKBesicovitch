/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.Basic
public import NKBesicovitch.Operators.MixedNorm.Sums

/-!
# Countable input decompositions for the local X-ray transform

A pointwise majorant by a countable weighted family of Borel inputs
gives the corresponding mixed-norm bound after restricting slopes.
All inputs may take the value infinity; the weights are finite.
-/

public section

open MeasureTheory Set NKBesicovitch.Projection
open scoped ENNReal NNReal

namespace NKBesicovitch.XRay

variable {m : ℕ} {ι : Type*} [Countable ι]

theorem localXRay_le_tsum {f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞}
    {F : ι → EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞} (hF : ∀ i, Measurable (F i))
    (w : ι → ℝ≥0) (h : ∀ z, f z ≤ ∑' i, (w i : ℝ≥0∞) * F i z)
    (ξ x : EuclideanSpace ℝ (Fin m)) :
    localXRay f ξ x ≤ ∑' i, (w i : ℝ≥0∞) * localXRay (F i) ξ x := by
  unfold localXRay
  apply (lintegral_mono (fun t ↦ h (x + t • ξ, t))).trans_eq
  have hm (i : ι) : Measurable (fun t : ℝ ↦ (w i : ℝ≥0∞) * F i (x + t • ξ, t)) :=
    measurable_const.mul ((hF i).comp (by fun_prop))
  rw [lintegral_tsum (fun i ↦ (hm i).aemeasurable)]
  congr 1
  funext i
  exact lintegral_const_mul' _ _ ENNReal.coe_ne_top

theorem mixedNorm_localXRay_le_tsum
    {f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞}
    {F : ι → EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞} (hF : ∀ i, Measurable (F i))
    (w : ι → ℝ≥0) (h : ∀ z, f z ≤ ∑' i, (w i : ℝ≥0∞) * F i z)
    {Ξ : Set (EuclideanSpace ℝ (Fin m))} (hΞ : MeasurableSet Ξ)
    {q r : ℝ≥0∞} (hq : 1 ≤ q) (hr : 1 ≤ r) (hqfin : q ≠ ∞) (hrfin : r ≠ ∞) :
    mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ localXRay f g.2 g.1)) q r volume volume ≤
        ∑' i, (w i : ℝ≥0∞) * mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
          (fun g : Line m ↦ localXRay (F i) g.2 g.1)) q r volume volume := by
  have hpoint (g : Line m) : (Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ localXRay f g.2 g.1) g ≤
        ∑' i, (w i : ℝ≥0∞) * (Prod.snd ⁻¹' Ξ).indicator
          (fun g : Line m ↦ localXRay (F i) g.2 g.1) g := by
    by_cases hg : g ∈ Prod.snd ⁻¹' Ξ
    · simp only [indicator_of_mem hg]
      exact localXRay_le_tsum hF w h g.2 g.1
    · simp only [indicator_of_notMem hg]
      exact zero_le
  apply (mixedNorm_mono hpoint).trans
  apply (mixedNorm_tsum_le (fun i ↦ measurable_const.mul
    ((measurable_localXRay (hF i)).indicator (hΞ.preimage measurable_snd)))
      hq hr hqfin hrfin).trans
  exact ENNReal.tsum_le_tsum (fun i ↦ mixedNorm_const_mul_le (w i) _)

end NKBesicovitch.XRay
