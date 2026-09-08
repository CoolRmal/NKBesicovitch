/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.InputSums

/-!
# Removing input normalization by homogeneity

Finite positive scalar multiplication preserves the local X-ray
transform and controls its mixed norm. A bound for the unit `L^p` ball
therefore gives the homogeneous bound for every Borel input. Taking an
infimum over strict upper bounds of the input norm also handles zero
and infinite norms without assuming pointwise finiteness.
-/

public section

open MeasureTheory Set NKBesicovitch.Projection
open scoped ENNReal NNReal

namespace NKBesicovitch.XRay

variable {m : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin m))} {p q r : ℝ≥0∞}
    {K : Set (EuclideanSpace ℝ (Fin m) × ℝ)} {C : ℝ≥0∞}

theorem mixedNorm_localXRay_const_mul_le (c : ℝ≥0)
    (f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞) :
    mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ localXRay (fun z ↦ (c : ℝ≥0∞) * f z) g.2 g.1)) q r volume volume ≤
        c * mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
          (fun g : Line m ↦ localXRay f g.2 g.1)) q r volume volume := by
  have heq : (Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ localXRay (fun z ↦ (c : ℝ≥0∞) * f z) g.2 g.1) =
        fun g ↦ (c : ℝ≥0∞) * (Prod.snd ⁻¹' Ξ).indicator
          (fun g : Line m ↦ localXRay f g.2 g.1) g := by
    funext g
    by_cases hg : g ∈ Prod.snd ⁻¹' Ξ
    · simp only [indicator_of_mem hg, localXRay, lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    · simp only [indicator_of_notMem hg, mul_zero]
  rw [heq]
  exact mixedNorm_const_mul_le c _

theorem mixedNorm_localXRay_le_of_eLpNorm_le
    (hbound : ∀ f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞, Measurable f →
      Function.support f ⊆ K → eLpNorm f p volume ≤ 1 →
        mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
          (fun g : Line m ↦ localXRay f g.2 g.1)) q r volume volume ≤ C)
    {f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞} (hf : Measurable f)
    (hsupport : Function.support f ⊆ K) {c : ℝ≥0} (hc : 0 < c)
    (hnorm : eLpNorm f p volume ≤ c) :
    mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ localXRay f g.2 g.1)) q r volume volume ≤ C * c := by
  let g := fun z ↦ ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * f z
  have hg : Measurable g := measurable_const.mul hf
  have hsupportg : Function.support g ⊆ K := by
    intro z hz
    apply hsupport
    intro hzero
    exact hz (by simp [g, hzero])
  have hgnorm : eLpNorm g p volume ≤ 1 := by
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (c := c⁻¹) (f := g) (g := f)
      (ae_of_all volume (fun z ↦ by simp only [g, enorm_eq_self]; exact le_rfl)) p
    apply h.trans
    calc
      _ ≤ (c⁻¹ : ℝ≥0) * (c : ℝ≥0∞) := mul_le_mul_right hnorm _
      _ = 1 := by rw [← ENNReal.coe_mul, inv_mul_cancel₀ hc.ne', ENNReal.coe_one]
  have hfg : f = fun z ↦ (c : ℝ≥0∞) * g z := by
    funext z
    simp only [g, ← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ hc.ne',
      ENNReal.coe_one, one_mul]
  calc
    _ = mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
        (fun l : Line m ↦ localXRay (fun z ↦ (c : ℝ≥0∞) * g z) l.2 l.1))
          q r volume volume := by rw [← hfg]
    _ ≤ c * mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
        (fun l : Line m ↦ localXRay g l.2 l.1)) q r volume volume :=
      mixedNorm_localXRay_const_mul_le c g
    _ ≤ c * C := mul_le_mul_right (hbound g hg hsupportg hgnorm) _
    _ = _ := mul_comm _ _

theorem mixedNorm_localXRay_bound_of_normalized (hC : C ≠ 0) (hCfin : C ≠ ∞)
    (hbound : ∀ f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞, Measurable f →
      Function.support f ⊆ K → eLpNorm f p volume ≤ 1 →
        mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
          (fun g : Line m ↦ localXRay f g.2 g.1)) q r volume volume ≤ C)
    {f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞} (hf : Measurable f)
    (hsupport : Function.support f ⊆ K) :
    mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ localXRay f g.2 g.1)) q r volume volume ≤ C * eLpNorm f p volume := by
  conv_rhs => arg 2; rw [← ENNReal.iInf_gt_eq_self (eLpNorm f p volume)]
  rw [ENNReal.mul_iInf_of_ne hC hCfin]
  apply le_iInf
  intro b
  rw [ENNReal.mul_iInf_of_ne hC hCfin]
  apply le_iInf
  intro hb
  by_cases hbfin : b = ∞
  · simp [hbfin, hC]
  lift b to ℝ≥0 using hbfin
  have hb0 : 0 < b := ENNReal.coe_pos.mp (zero_le.trans_lt hb)
  exact mixedNorm_localXRay_le_of_eLpNorm_le hbound hf hsupport hb0 hb.le

end NKBesicovitch.XRay
